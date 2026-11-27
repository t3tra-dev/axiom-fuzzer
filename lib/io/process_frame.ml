(* Length-prefixed binary frames from a forked process of this executable to its supervisor.

   A frame is [magic (8 bytes) | payload length (8 bytes, big-endian) | MD5 of payload (16 bytes)
   | payload]. The payload is a [Marshal] image of one value whose type both sides agree on
   (they run the same binary). The stream must hold exactly one frame. The digest is checked
   before the payload is unmarshalled, so a truncated, corrupted or foreign stream is rejected
   as a whole and never reaches [Marshal]. Unlike the S-expression certificate format there is
   no size or nesting limit besides memory: deep proof terms and certificates larger than the
   32 MiB file limit cross intact. Anything received this way is untrusted data; a certificate
   must still pass [Kernel.check] before it is reported. (The portfolio may send one notice
   byte before the frame; see [Portfolio.proof_notice].) *)

let magic = "AXFRAME1"
let header_bytes = 32

let encode payload =
  let b = Buffer.create (header_bytes + String.length payload) in
  Buffer.add_string b magic;
  Buffer.add_int64_be b (Int64.of_int (String.length payload));
  Buffer.add_string b (Digest.string payload);
  Buffer.add_string b payload;
  Buffer.contents b

type decoded = Incomplete | Payload of string | Invalid of string

(* [decode data] classifies a complete stream: [Incomplete] only when [data] is a strict prefix
   of some valid frame (a writer stopped early). *)
let decode data =
  let n = String.length data in
  let prefix = min n (String.length magic) in
  if String.sub data 0 prefix <> String.sub magic 0 prefix then Invalid "bad frame magic"
  else if n < header_bytes then Incomplete
  else
    let length = String.get_int64_be data 8 in
    if Int64.compare length 0L < 0 || Int64.compare length (Int64.of_int max_int) > 0 then
      Invalid "bad frame length"
    else
      let length = Int64.to_int length in
      if n - header_bytes < length then Incomplete
      else if n - header_bytes > length then Invalid "trailing bytes after frame"
      else
        let payload = String.sub data header_bytes length in
        if Digest.string payload <> String.sub data 16 16 then Invalid "frame digest mismatch"
        else Payload payload

let pack (value : 'a) = encode (Marshal.to_string value [])

(* The caller fixes ['a]; it must be the type the writer packed. A wrong digest or a damaged
   Marshal header is reported as [Error]. *)
let unpack data : ('a, string) result =
  match decode data with
  | Incomplete -> Error "truncated frame"
  | Invalid reason -> Error reason
  | Payload payload -> (
      match Marshal.total_size (Bytes.unsafe_of_string payload) 0 with
      | size when size <> String.length payload -> Error "frame payload size mismatch"
      | _ -> (
          try Ok (Marshal.from_string payload 0 : 'a)
          with Failure e | Invalid_argument e -> Error ("frame payload: " ^ e))
      | exception (Failure e | Invalid_argument e) -> Error ("frame payload: " ^ e))

(* One write(2) per call: [Unix.write_substring] loops over 64 KiB chunks and raises EINTR
   even after earlier chunks were written, so retrying it from the old offset would duplicate
   data. [single_write_substring] raises only when nothing was written. [write] is that
   primitive; tests substitute scripted or counting versions with the same contract. *)
let rec write_all ?(write = Unix.single_write_substring) fd s offset =
  if offset < String.length s then
    match write fd s offset (String.length s - offset) with
    | 0 -> failwith "frame write made no progress"
    | n -> write_all ~write fd s (offset + n)
    | exception Unix.Unix_error (Unix.EINTR, _, _) -> write_all ~write fd s offset

let write fd value = write_all fd (pack value) 0
