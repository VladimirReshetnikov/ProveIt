From K230L Require Import Codes230.
From K215F Require Import DomRho8 Thm222 ThmDom CD222.

(** Exact production facade types, elaborated independently of inferred types. *)
Definition rho8_production_interface :
    forall (T : nat -> Prop), DomImp T -> forall a b c u, T (Codes230.rho8 a b c u) :=
  rho8_all.
Definition thmDom_production_interface : forall n, thmDom n <-> thm222 n := thmDom_iff.
Definition k_production_interface : forall p q, thm222 (wim p (wim q p)) := thm_K.
Definition peirce_production_interface : forall p q, thm222 (wim (wim (wim p q) p) p) := thm_P.
Definition b_production_interface :
    forall p q r, thm222 (wim (wim p q) (wim (wim q r) (wim p r))) := thm_B.
Definition s_production_interface :
    forall p q r, thm222 (wim (wim p (wim q r)) (wim (wim p q) (wim p r))) := thm_S.

Print Assumptions rho8_production_interface.
Print Assumptions thmDom_production_interface.
Print Assumptions k_production_interface.
Print Assumptions peirce_production_interface.
Print Assumptions b_production_interface.
Print Assumptions s_production_interface.
