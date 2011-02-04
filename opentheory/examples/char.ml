(* ------------------------------------------------------------------------- *)
(* A type of Unicode characters.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "char-def";;

(* Planes *)

let is_plane_def = new_definition
  `!p. is_plane p = byte_lt p (num_to_byte 17)`;;

export_thm is_plane_def;;

let plane_exists = prove
  (`?p. is_plane p`,
   EXISTS_TAC `num_to_byte 0` THEN
   REWRITE_TAC [is_plane_def] THEN
   CONV_TAC byte_reduce_conv);;

let plane_tybij =
    new_type_definition "plane" ("mk_plane","dest_plane") plane_exists;;

export_thm plane_tybij;;

(* Positions *)

let is_position_def = new_definition
  `!p. is_position (p : word16) = T`;;

export_thm is_position_def;;

let position_exists = prove
  (`?p. is_position p`,
   EXISTS_TAC `p : word16` THEN
   REWRITE_TAC [is_position_def]);;

let position_tybij =
    new_type_definition
      "position" ("mk_position","dest_position") position_exists;;

export_thm position_tybij;;

(* Unicode characters *)

let is_unicode_def = new_definition
  `!pl pos.
     is_unicode (pl,pos) =
     let pli = dest_plane pl in
     let posi = dest_position pos in
     ~(pli = num_to_byte 0) \/
     word16_lt posi (num_to_word16 55296) \/
     (word16_lt (num_to_word16 57343) posi /\
      word16_lt posi (num_to_word16 65534))`;;

export_thm is_unicode_def;;

let unicode_exists = prove
  (`?pl_pos. is_unicode pl_pos`,
   EXISTS_TAC `(mk_plane (num_to_byte 1), (pos : position))` THEN
   REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC (SPEC `num_to_byte 1` (CONJUNCT2 plane_tybij)) THEN
   REWRITE_TAC [is_plane_def] THEN
   CONV_TAC byte_reduce_conv THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC byte_reduce_conv);;

let unicode_tybij =
    new_type_definition "unicode" ("mk_unicode","dest_unicode") unicode_exists;;

export_thm unicode_tybij;;

(* ------------------------------------------------------------------------- *)
(* UTF-8 encodings of unicode characters.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8";;

let is_cont_def = new_definition
  `!b. is_cont b <=> byte_bit b 7 /\ ~byte_bit b 6`;;

export_thm is_cont_def;;

let parse_cont_def = new_definition
  `parse_cont = parse_some is_cont`;;

export_thm parse_cont_def;;

let parse_cont2_def = new_definition
  `parse_cont2 = parse_pair parse_cont parse_cont`;;

export_thm parse_cont2_def;;

let parse_cont3_def = new_definition
  `parse_cont3 = parse_pair parse_cont parse_cont2`;;

export_thm parse_cont3_def;;

let decoder_parse_def = new_definition
  `!b0 s.
     decoder_parse b0 s =
     if byte_bit b0 7 then
       if byte_bit b0 6 then
         if byte_bit b0 5 then
           if byte_bit b0 4 then
             if byte_bit b0 3 then
               NONE
             else
               case_option
                 NONE
                 (\ ((b1,(b2,b3)),s').
                    let w = byte_shl (byte_and b0 (num_to_byte 7)) 2 in
                    let z = byte_shr (byte_and b1 (num_to_byte 48)) 4 in
                    let p = byte_or w z in
                    if p = num_to_byte 0 \/ byte_lt (num_to_byte 16) p then
                      NONE
                    else
                      let pl = mk_plane p in
                      let z0 = byte_shl (byte_and b1 (num_to_byte 15)) 4 in
                      let y0 = byte_shr (byte_and b2 (num_to_byte 60)) 2 in
                      let p0 = byte_or z0 y0 in
                      let y1 = byte_shl (byte_and b2 (num_to_byte 3)) 6 in
                      let x1 = byte_and b3 (num_to_byte 63) in
                      let p1 = byte_or y1 x1 in
                      let pos = mk_position (bytes_to_word16 p0 p1) in
                      let ch = mk_unicode (pl,pos) in
                      SOME (ch,s'))
                 (parse parse_cont3 s)
           else
             case_option
               NONE
               (\ ((b1,b2),s').
                  let z0 = byte_shl (byte_and b0 (num_to_byte 15)) 4 in
                  let y0 = byte_shr (byte_and b1 (num_to_byte 60)) 2 in
                  let p0 = byte_or z0 y0 in
                  if byte_lt p0 (num_to_byte 8) \/
                     (byte_le (num_to_byte 216) p0 /\
                      byte_le p0 (num_to_byte 223)) then
                    NONE
                  else
                    let y1 = byte_shl (byte_and b1 (num_to_byte 3)) 6 in
                    let x1 = byte_and b2 (num_to_byte 63) in
                    let p1 = byte_or y1 x1 in
                    if p0 = num_to_byte 255 /\ byte_le (num_to_byte 254) p1 then
                      NONE
                    else
                      let pl = mk_plane (num_to_byte 0) in
                      let pos = mk_position (bytes_to_word16 p0 p1) in
                      let ch = mk_unicode (pl,pos) in
                      SOME (ch,s'))
               (parse parse_cont2 s)
         else
           case_option
             NONE
             (\ (b1,s').
               let pl = mk_plane (num_to_byte 0) in
               let p0 = byte_shr (byte_and b0 (num_to_byte 28)) 2 in
               let y1 = byte_shl (byte_and b0 (num_to_byte 3)) 6 in
               let x1 = byte_and b1 (num_to_byte 63) in
               let p1 = byte_or y1 x1 in
               if p0 = num_to_byte 0 /\ byte_lt p1 (num_to_byte 128) then
                 NONE
               else
                 let pos = mk_position (bytes_to_word16 p0 p1) in
                 let ch = mk_unicode (pl,pos) in
                 SOME (ch,s'))
             (parse parse_cont s)
       else
         NONE
     else
       let pl = mk_plane (num_to_byte 0) in
       let pos = mk_position (bytes_to_word16 (num_to_byte 0) b0) in
       let ch = mk_unicode (pl,pos) in
       SOME (ch,s)`;;

export_thm decoder_parse_def;;

let decoder_def = new_definition
  `decoder = mk_parser decoder_parse`;;

export_thm decoder_def;;

let decode_stream_def = new_definition
  `decode_stream = parse_stream decoder`;;

export_thm decode_stream_def;;

let decode_def = new_definition
  `!bs. decode bs = stream_to_list (decode_stream (list_to_stream bs))`;;

export_thm decode_def;;

let encoder_def = new_definition
  `!ch.
     encoder ch =
     let (pl,pos) = dest_unicode ch in
     let p = dest_plane pl in
     let (p0,p1) = word16_to_bytes (dest_position pos) in
     if p = num_to_byte 0 then
       if p0 = num_to_byte 0 then
         if byte_bit p1 7 then
           let b00 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
           let b0 = byte_or (num_to_byte 192) b00 in
           let b10 = byte_and p1 (num_to_byte 63) in
           let b1 = byte_or (num_to_byte 128) b10 in
           CONS b0 (CONS b1 [])
         else
           let b0 = p1 in
           CONS b0 []
       else
         if byte_and (num_to_byte 248) p0 = num_to_byte 0 then
           let b00 = byte_shl p0 2 in
           let b01 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
           let b0 = byte_or (num_to_byte 192) (byte_or b00 b01) in
           let b10 = byte_and p1 (num_to_byte 63) in
           let b1 = byte_or (num_to_byte 128) b10 in
           CONS b0 (CONS b1 [])
         else
           let b00 = byte_shr (byte_and p0 (num_to_byte 240)) 4 in
           let b0 = byte_or (num_to_byte 224) b00 in
           let b10 = byte_shl (byte_and p0 (num_to_byte 15)) 2 in
           let b11 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
           let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
           let b20 = byte_and p1 (num_to_byte 63) in
           let b2 = byte_or (num_to_byte 128) b20 in
           CONS b0 (CONS b1 (CONS b2 []))
     else
       let b00 = byte_shr (byte_and p (num_to_byte 28)) 2 in
       let b0 = byte_or (num_to_byte 240) b00 in
       let b10 = byte_shl (byte_and p (num_to_byte 3)) 4 in
       let b11 = byte_shr (byte_and p0 (num_to_byte 240)) 4 in
       let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
       let b20 = byte_shl (byte_and p0 (num_to_byte 15)) 2 in
       let b21 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
       let b2 = byte_or (num_to_byte 128) (byte_or b20 b21) in
       let b30 = byte_and p1 (num_to_byte 63) in
       let b3 = byte_or (num_to_byte 128) b30 in
       CONS b0 (CONS b1 (CONS b2 (CONS b3 [])))`;;

export_thm encoder_def;;

let encode_def = new_definition
  `!chs. encode chs = concat (MAP encoder chs)`;;

export_thm encode_def;;

logfile_end ();;
