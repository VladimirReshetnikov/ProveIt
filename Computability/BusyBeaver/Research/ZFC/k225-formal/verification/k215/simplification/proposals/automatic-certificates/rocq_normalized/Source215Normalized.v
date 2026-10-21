(** Exact K215 source equivalence using one 1,426-entry normalized certificate.
    This is an all-register theorem for the unchanged literal p215 and dagPerm.
    It is not a rebuild of the complete binary/ZFC endpoint. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedBisim NormalizedCert215.
Import ListNotations.

Lemma normalized_certificate_forward :
  NCheck.check (ptree p215) (ptree dagPerm)
    normalized_certificate = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_normalized R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (NCheck.check_one_sided_iff p215 dagPerm
    normalized_certificate normalized_certificate_forward R).
Qed.

Print Assumptions normalized_certificate_forward.
Print Assumptions p215_dagPerm_normalized.
