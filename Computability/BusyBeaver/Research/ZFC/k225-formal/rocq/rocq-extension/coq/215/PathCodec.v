(** k225-formal/rocqperm/PathCodec.v (SHA256 6fa7196f1004004f9aa420d9918eee5749e9b26b702711b9c5fb0dbfc45ae7bf) under namespace K215F. *)
(** Canonical lossless binary encoding of finite Boolean paths.
    Positive's leading 1 is a terminator, so leading/trailing false bits survive. *)
From Coq Require Import List PArith NArith ZArith.
Import ListNotations.

Fixpoint encode_path (xs : list bool) : positive :=
  match xs with
  | [] => xH
  | false :: tail => xO (encode_path tail)
  | true :: tail => xI (encode_path tail)
  end.

Fixpoint decode_path (p : positive) : list bool :=
  match p with
  | xH => []
  | xO tail => false :: decode_path tail
  | xI tail => true :: decode_path tail
  end.

Theorem decode_encode_path xs : decode_path (encode_path xs) = xs.
Proof. induction xs as [|[] xs IH]; simpl; congruence. Qed.

Theorem encode_decode_path p : encode_path (decode_path p) = p.
Proof. induction p; simpl; congruence. Qed.

Definition packed_entry := (positive * positive * N * N)%type.
Definition expanded_entry := (list bool * list bool * Z * N * N)%type.
Definition expand_entry (x : packed_entry) : expanded_entry :=
  let '(a,b,j,k) := x in (decode_path a,decode_path b,0%Z,j,k).

Definition plain_entry := (list bool * list bool * N * N)%type.
Definition expand_plain (x : packed_entry) : plain_entry :=
  let '(a,b,j,k) := x in (decode_path a,decode_path b,j,k).

Print Assumptions decode_encode_path.
Print Assumptions encode_decode_path.
