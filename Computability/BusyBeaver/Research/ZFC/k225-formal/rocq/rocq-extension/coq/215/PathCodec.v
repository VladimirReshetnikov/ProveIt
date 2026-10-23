(** k225-formal/rocqperm/PathCodec.v (SHA256 afd1a0ded181064fad4f33c4903820b6a4e45f52883db841d0e66636ca1463af) under namespace K215F. *)
(** Binary decoding of finite Boolean paths from positive numbers, as stored in the 215's
    source certificate. Positive's leading 1 is a terminator, so leading and trailing false
    bits survive. *)
From Coq Require Import List PArith NArith.
Import ListNotations.

Fixpoint decode_path (p : positive) : list bool :=
  match p with
  | xH => []
  | xO tail => false :: decode_path tail
  | xI tail => true :: decode_path tail
  end.

Definition packed_entry := (positive * positive * N * N)%type.
