(** Integration proposal: retain the public all-register theorem name.
    Place the four small checker/codec modules and normalized certificate
    on this project's Rocq load path; adjust their namespace if required. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedBisim NormalizedCert215.
Import ListNotations.

Lemma certificate_normalized :
  NCheck.check (ptree p215) (ptree dagPerm) normalized_certificate = true.
Proof. vm_compute. reflexivity. Qed.

Theorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (NCheck.check_one_sided_iff p215 dagPerm normalized_certificate
    certificate_normalized R).
Qed.

Print Assumptions p215_dagPerm.
