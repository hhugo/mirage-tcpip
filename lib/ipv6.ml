(*
 * Copyright (c) 2010-2011 Anil Madhavapeddy <anil@recoil.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Lwt
open Printf
open Nettypes

cstruct ipv6 {
  uint32_t       version;
  uint16_t       payload_len;
  uint8_t        nxt;
  uint8_t        hop;
  uint64_t       src_hi;
  uint64_t       src_lo;
  uint64_t       dst_hi;
  uint64_t       dst_lo;
} as big_endian

type t = {
  ethif: Ethif.t;
  mutable ip: Ipaddr.V6.t;
  mutable netmask: Ipaddr.V6.t;
  mutable gateways: Ipaddr.V6.t list;
  mutable icmp: Ipaddr.V6.t -> Cstruct.t -> Cstruct.t -> unit Lwt.t;
  mutable udp: src:Ipaddr.V6.t -> dst:Ipaddr.V6.t -> Cstruct.t -> unit Lwt.t;
  mutable tcp: src:Ipaddr.V6.t -> dst:Ipaddr.V6.t -> Cstruct.t -> unit Lwt.t;
}

module Routing = struct

  type classify =
    |Broadcast
    |Gateway
    |Local

  exception No_route_to_destination_address of Ipaddr.V6.t

  let is_local t ip = false
    (* let ipand a b = Int32.logand (Ipaddr.V4.to_int32 a) (Ipaddr.V4.to_int32 b) in *)
    (* (ipand t.ip t.netmask) = (ipand ip t.netmask) *)

  let destination_mac t =
    function
    |ip  -> (* Broadcast *)
      return Macaddr.broadcast
    (* |ip when is_local t ip -> (\* Local *\) *)
    (*   Ethif.query_arp t.ethif ip *)
    (* |ip -> begin (\* Gateway *\) *)
    (*   match t.gateways with *)
    (*   |hd::_ -> Ethif.query_arp t.ethif hd *)
    (*   |[] -> *)
    (*     printf "IP.output: no route to %a\n%!" Ipaddr.V6.to_buffer ip; *)
    (*     fail (No_route_to_destination_address ip) *)
(* end *)
end

let get_header ~proto ~dest_ip t =
  lwt ethernet_frame = Ethif.get_frame t.ethif in
  (* Something of a layer violation here, but ARP is awkward *)
  lwt dmac = Routing.destination_mac t dest_ip >|= Macaddr.to_bytes in
  let smac = Macaddr.to_bytes (Ethif.mac t.ethif) in
  Ethif.set_ethernet_dst dmac 0 ethernet_frame;
  Ethif.set_ethernet_src smac 0 ethernet_frame;
  Ethif.set_ethernet_ethertype ethernet_frame 0x0800;
  let buf = Cstruct.shift ethernet_frame Ethif.sizeof_ethernet in
  (* Write the constant IPv4 header fields *)
  set_ipv6_version buf (Int32.shift_left 6l  28); (* TODO options *)
  let proto = match proto with |`ICMP -> 1 |`TCP -> 6 |`UDP -> 17 in
  set_ipv6_nxt buf proto;
  set_ipv6_hop buf 38; (* TODO *)
  let src_hi,src_lo = Ipaddr.V6.to_int64 t.ip in
  let dst_hi,dst_lo = Ipaddr.V6.to_int64 dest_ip in
  set_ipv6_src_hi buf src_hi;
  set_ipv6_src_lo buf src_lo;
  set_ipv6_dst_hi buf dst_hi;
  set_ipv6_dst_lo buf dst_lo;
  let len = Ethif.sizeof_ethernet + sizeof_ipv6 in
  return (ethernet_frame, len)

let adjust_output_header ~tlen frame =
  let buf = Cstruct.sub frame Ethif.sizeof_ethernet sizeof_ipv6 in
  (* Set the mutable values in the ipv4 header *)
  set_ipv6_payload_len buf tlen

(* We write a whole frame, truncated from the right where the
 * packet data stops.
 *)
let write t frame data =
  let ihl = 0 in (* TODO options *)
  let tlen = (ihl * 4) + (Cstruct.len data) in
  adjust_output_header ~tlen frame;
  Ethif.writev t.ethif [frame;data]

let writev t ethernet_frame bufs =
  let tlen = Cstruct.len ethernet_frame - Ethif.sizeof_ethernet + (Cstruct.lenv bufs) in
  adjust_output_header ~tlen ethernet_frame;
  Ethif.writev t.ethif (ethernet_frame::bufs)

let input t buf =
  (* buf pointers to to start of IPv4 header here *)
  let src_lo = get_ipv6_src_lo buf
  and src_hi = get_ipv6_src_hi buf
  and dst_lo = get_ipv6_dst_lo buf
  and dst_hi = get_ipv6_dst_hi buf in
  let src = Ipaddr.V6.of_int64 (src_hi,src_lo)
  and dst = Ipaddr.V6.of_int64 (dst_hi,dst_lo) in
  let payload_len = get_ipv6_payload_len buf in
  (* XXX this will raise exception for 0-length payload *)
  (* let hdr = Cstruct.sub buf 0 ihl in *)
  let data = Cstruct.sub buf sizeof_ipv6 (payload_len - sizeof_ipv6) in
  match get_ipv6_nxt buf with
  (* |1 -> (\* ICMP *\) *)
  (*   t.icmp src hdr data *)
  |6 -> (* TCP *)
    t.tcp ~src ~dst data
  |17 -> (* UDP *)
    t.udp ~src ~dst data
  |proto -> return ( (* printf "IPv4: dropping proto %d\n%!" proto *) )

let default_icmp = fun _ _ _ -> return ()
let default_udp = fun ~src ~dst _ -> return ()
let default_tcp = fun ~src ~dst _ -> return ()

let create ethif =
  let ip = Ipaddr.V6.unspecified in
  let netmask = Ipaddr.V6.unspecified in
  let gateways = [] in
  let icmp = default_icmp in
  let udp = default_udp in
  let tcp = default_tcp in
  let t = { ethif; ip; netmask; gateways; icmp; udp; tcp } in
  Ethif.attach ethif (`IPv6 (input t));
  let th,_ = Lwt.task () in
  Lwt.on_cancel th (fun () ->
    printf "IPv4: shutting down\n%!";
    Ethif.detach ethif `IPv6);
  t, th

let attach t = function
  |`ICMP x -> t.icmp <- x
  |`UDP x -> t.udp <- x
  |`TCP x -> t.tcp <- x

let detach t = function
  |`ICMP -> t.icmp <- default_icmp
  |`UDP -> t.udp <- default_udp
  |`TCP -> t.tcp <- default_tcp

let set_ip t ip =
  t.ip <- ip;
  (* Inform ARP layer of new IP *)
  (* Ethif.add_ip t.ethif ip *)
  Lwt.return_unit

let get_ip t = t.ip

let set_netmask t netmask =
  t.netmask <- netmask;
  return ()

let set_gateways t gateways =
  t.gateways <- gateways;
  return ()

let mac t = Ethif.mac t.ethif

let get_netmask t = t.netmask
