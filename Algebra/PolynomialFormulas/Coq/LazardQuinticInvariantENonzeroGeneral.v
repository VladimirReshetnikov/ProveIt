From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import LazardGeneralResolventCriterion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The arbitrary-base-field algebra behind Lazard's nonvanishing argument.

    The only property of the coefficient field used here is that [-1] is
    not a square.  Once [a / b] descends through a field embedding, an
    equality [a^2 + b^2 = 0] would pull a square root of [-1] back along
    that embedding.  The final theorem derives the required descent from
    MathComp's finite-Galois fixed-field theorem. *)
Module PolynomialFormulasLazardQuinticInvariantENonzeroGeneral.

Import GRing.Theory.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.

Local Open Scope group_scope.
Local Open Scope ring_scope.

(** The exact base-field obstruction used on p. 216: [-1] is not a square
    in [F]. *)
Definition minus_one_nonsquare (F : fieldType) : Prop :=
  ~ exists q : F, q ^+ 2 = - 1.

Section AlgebraicCore.

Variables (F L : fieldType).
Variable embed : {rmorphism F -> L}.

(** If [a / b] belongs to the image of the base-field embedding and
    [b] is nonzero, then a vanishing sum of squares would contradict
    [minus_one_nonsquare F]. *)
Theorem lazard_sq_add_sq_neq0_of_ratio_in_image
    (hns : minus_one_nonsquare F)
    (a b : L) (hb : b != 0)
    (hbase : exists q : F, a / b = embed q) :
  a ^+ 2 + b ^+ 2 != 0.
Proof.
apply/eqP=> hzero.
have hb2 : b ^+ 2 != 0 by exact: expf_neq0 2 hb.
have hratio : (a / b) ^+ 2 = - 1.
  rewrite expr_div_n.
  apply/eqP.
  rewrite -[(- 1 : L)]divr1 eqr_div ?oner_neq0 //
    mulr1 mulN1r -addr_eq0.
  apply/eqP.
  exact: hzero.
have [q hq] := hbase.
apply: hns.
exists q.
apply: (fmorph_inj embed).
rewrite rmorphXn rmorphN rmorph1 -hq.
exact: hratio.
Qed.

End AlgebraicCore.

Section MathCompGaloisWrapper.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).
Local Notation gal_action :=
  (@GC.lazard_galois_action F L E).

(** Finite-Galois fixed-ratio form.  The caller supplies only fixedness;
    [GC.lazard_galois_base_fixed_iff], proved from [galois_fixedField],
    derives that the ratio lies in the embedded base field. *)
Theorem lazard_sq_add_sq_neq0_of_galois_fixed_ratio_general
    (hns : minus_one_nonsquare (subvs_of K))
    (a b : subvs_of E) (hb : b != 0)
    (hfixed : forall g : gal_of E, g \in 'Gal(E / K)%G ->
      gal_action g (a / b) = a / b) :
  a ^+ 2 + b ^+ 2 != 0.
Proof.
apply: (@lazard_sq_add_sq_neq0_of_ratio_in_image
  (subvs_of K) (subvs_of E) base_embed hns a b hb).
exact: (proj1 (@GC.lazard_galois_base_fixed_iff
  F L K E galois_K_E (a / b))) hfixed.
Qed.

End MathCompGaloisWrapper.

End PolynomialFormulasLazardQuinticInvariantENonzeroGeneral.
