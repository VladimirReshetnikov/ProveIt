(** All-register equivalence using the automatically inferred shared certificate.
    Dependencies are reused from the accepted normalized Rocq source closure. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedBisim AutoCert215.
Import ListNotations.

Lemma auto_certificate_forward :
  NCheck.check (ptree p215) (ptree dagPerm) auto_certificate = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_auto R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof.
  exact (NCheck.check_one_sided_iff p215 dagPerm
    auto_certificate auto_certificate_forward R).
Qed.

Print Assumptions auto_certificate_forward.
Print Assumptions p215_dagPerm_auto.
