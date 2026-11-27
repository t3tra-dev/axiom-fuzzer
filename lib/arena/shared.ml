(* Sharing-preserving list filters for index compaction.

   Index buckets are immutable lists, and inference cursors (Index.cursor,
   Equality_index.cursor, Goal and transfer cursors) capture the bucket list
   they started on. [List.filter] allocates a fresh copy of every list it
   filters, even when it keeps every element. Compaction runs at every
   collection point, so each long-lived cursor then pins its own private copy
   of the bucket spine: memory grows with the number of live cursors times the
   bucket size. [filter] returns the same elements in the same order as
   [List.filter], evaluates the predicate exactly once per element in list
   order, and shares the longest suffix of the input in which every element is
   kept (the whole input when nothing is dropped). Only physical sharing
   differs, so no search decision can observe it. *)

(* The first cell whose element is dropped, or [] when every element is kept. *)
let rec first_drop keep = function
  | [] -> []
  | x :: rest as cell -> if keep x then first_drop keep rest else cell

let[@tail_mod_cons] rec filter keep xs =
  match first_drop keep xs with [] -> xs | stop -> copy_until keep xs stop

(* Copies the (already accepted) elements before the cell [stop], skips the
   dropped element at [stop] and filters the rest. *)
and[@tail_mod_cons] copy_until keep cell stop =
  if cell == stop then match stop with _ :: rest -> filter keep rest | [] -> []
  else match cell with x :: rest -> x :: copy_until keep rest stop | [] -> []

(* Keeps the elements of [q] that satisfy [keep], in order, evaluating [keep] exactly once per
   element in queue order: the queue [Queue.to_seq q |> Seq.filter keep |> List.of_seq] refills,
   without the sequence and the intermediate list. [keep] is evaluated in one pass over the queue
   and its answers are recorded; the queue is rebuilt only when one is false, so a queue that
   keeps every element is left as it is instead of being refilled cell by cell (the same
   elements in the same order either way). [keep] must not change [q]. *)
let filter_queue keep q =
  let n = Queue.length q in
  if n > 0 then (
    let kept = Bytes.make n '\001' and dropped = ref false and i = ref 0 in
    Queue.iter
      (fun x ->
        if not (keep x) then (
          Bytes.unsafe_set kept !i '\000';
          dropped := true);
        incr i)
      q;
    if !dropped then
      for k = 0 to n - 1 do
        let x = Queue.take q in
        if Bytes.unsafe_get kept k = '\001' then Queue.add x q
      done)

(* The previous filter (every element taken and the kept ones added back): the reference of the
   unit tests. *)
let filter_queue_rotate keep q =
  for _ = 1 to Queue.length q do
    let x = Queue.take q in
    if keep x then Queue.add x q
  done
