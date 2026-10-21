(** Optional audit against the old literal certificate. NOT compiled here.
    Keep this out of the production dependency closure after review. *)
From Coq Require Import List ZArith.
From K215F Require Import Cert215Offsets.
Require Import PackedCert215.
Import ListNotations.

Definition erase_offsets : list (list bool * list bool * N * N) :=
  map (fun '(a,b,z,j,k) => (a,b,j,k)) Cert215.

Lemma every_offset_zero : forallb (fun '(_,_,z,_,_) => Z.eqb z 0) Cert215 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma packed_decodes_exactly : Cert215Plain = erase_offsets.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions packed_decodes_exactly.
