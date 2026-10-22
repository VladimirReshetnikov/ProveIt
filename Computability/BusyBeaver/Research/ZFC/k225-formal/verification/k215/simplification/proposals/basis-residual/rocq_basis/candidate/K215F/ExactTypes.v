(** The same typed client is compiled against both the original and replacement
    proof trees. Its statements use the production code definitions. *)
From K230L Require Import Codes230.
From K215F Require Import Thm222 DomRho8 ThmDom CD222.

Definition checked_rho8_all : forall (T : nat -> Prop), DomImp T ->
  forall a b c u, T (rho8 a b c u) := rho8_all.
Definition checked_truth : forall (T : nat -> Prop), DomImp T -> T 0 := @dtruth.
Definition checked_mp : forall (T : nat -> Prop), DomImp T ->
  forall a b, T (wim a b) -> T a -> T b := @dmp.
Definition checked_restricted_row : forall (T : nat -> Prop), DomImp T ->
  forall a b c u, u <= a -> T (rho8 a b c u) := @drho8.
Definition checked_K : forall p q, thm222 (wim p (wim q p)) := thm_K.
Definition checked_P : forall p q, thm222 (wim (wim (wim p q) p) p) := thm_P.
Definition checked_B : forall p q r,
  thm222 (wim (wim p q) (wim (wim q r) (wim p r))) := thm_B.
Definition checked_S : forall p q r,
  thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))) := thm_S.
Definition checked_calculus_equivalence : forall n, thmDom n <-> thm222 n := thmDom_iff.

Print Assumptions checked_rho8_all.
Print Assumptions checked_truth.
Print Assumptions checked_mp.
Print Assumptions checked_restricted_row.
Print Assumptions checked_K.
Print Assumptions checked_P.
Print Assumptions checked_B.
Print Assumptions checked_S.
Print Assumptions checked_calculus_equivalence.
