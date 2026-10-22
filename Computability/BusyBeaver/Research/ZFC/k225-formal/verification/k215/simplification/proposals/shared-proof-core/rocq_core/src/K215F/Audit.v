From K230L Require Import Codes230.
From K215F Require Import DomRho8 Thm222 ThmDom.

(** Literal production interface types; no conversion theorem is assumed. *)
Definition rho8_production_interface :
    forall (T : nat -> Prop), DomImp T -> forall a b c u, T (Codes230.rho8 a b c u) :=
  rho8_all.
Definition thmDom_production_interface : forall n, thmDom n <-> thm222 n := thmDom_iff.

Print Assumptions rho8_production_interface.
Print Assumptions thmDom_production_interface.
