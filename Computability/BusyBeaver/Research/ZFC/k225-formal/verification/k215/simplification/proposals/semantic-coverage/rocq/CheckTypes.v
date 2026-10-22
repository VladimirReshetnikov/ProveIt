(** No new mathematics: exact public theorem types and compatibility witness. *)
From K230L Require Import Codes230.
From K215F Require Import DominatedImplication58 DomRho8 ThmDom.

Check @DominatedImplication58.rho8_all.
Check @DominatedImplication58.composition.
Check @DominatedImplication58.lift_right.
Check @DomRho8.rho8_all.
Check @thmDom_iff.

Definition production_rho8_api :
  forall T : nat -> Prop, DomImp T -> forall a b c u : nat,
    T (Codes230.rho8 a b c u) := DomRho8.rho8_all.

Print Assumptions production_rho8_api.
