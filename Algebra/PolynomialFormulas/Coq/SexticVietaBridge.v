From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticFactorCompleteness SexticSparsePolynomials SexticPowerSumSymmetric
  SexticNewtonPowerSums SexticComputedResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Vieta's formula in the precise tuple coordinates consumed by the
    executable resolvent computation.  The generic part is stated over any
    characteristic-zero commutative ring; the numfield instantiation below
    maps the six canonical roots into [algC]. *)
Module PolynomialFormulasSexticVietaBridge.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticFactorCompleteness.
Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticPowerSumSymmetric.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticComputedResolvents.

Section GenericVieta.

Variable R : comNzRingType.

Definition sextic_vieta_polynomial (roots : 6.-tuple R) : {poly R} :=
  'X^6 - (root_esymm roots ord0)%:P * 'X^5 +
    (root_esymm roots (inord 1))%:P * 'X^4 -
    (root_esymm roots (inord 2))%:P * 'X^3 +
    (root_esymm roots (inord 3))%:P * 'X^2 -
    (root_esymm roots (inord 4))%:P * 'X +
    (root_esymm roots (inord 5))%:P.

Lemma prod_XsubC_sixE (roots : 6.-tuple R) :
  \prod_(r <- roots) ('X - r%:P) = sextic_vieta_polynomial roots.
Proof.
have characteristic_product_big (values : 6.-tuple {poly R}) indices x :
    characteristic_product values indices x =
      \prod_(i <- indices) (x - tnth values i).
  induction indices as [|i indices ih].
  - by rewrite /characteristic_product big_nil.
  - change ((x - tnth values i) *
        characteristic_product values indices x =
      \prod_(j <- i :: indices) (x - tnth values j)).
    by rewrite big_cons ih.
have root_esymm_list_polyC (indices : seq 'I_6) k :
    root_esymm_list [tuple of map (@polyC R) roots] indices k =
      (root_esymm_list roots indices k)%:P.
  elim: indices k=> [|i indices ih] [|k] /=.
  - by rewrite polyC1.
  - by rewrite polyC0.
  - by rewrite polyC1.
  - by rewrite tnth_map ih ih polyCD polyCM.
have root_esymm_polyC i :
    root_esymm [tuple of map (@polyC R) roots] i =
      (root_esymm roots i)%:P.
  exact: root_esymm_list_polyC.
have h := @characteristic_product_six {poly R}
  [tuple of map (@polyC R) roots] 'X.
rewrite characteristic_product_big /six_indices !root_esymm_polyC in h.
have hmap :
    \prod_(i <- enum 'I_6)
      ('X - tnth [tuple of map (@polyC R) roots] i) =
    \prod_(i <- enum 'I_6) ('X - (tnth roots i)%:P).
  apply: eq_bigr=> i _.
  by rewrite tnth_map.
rewrite hmap in h.
rewrite -(map_tnth_enum roots) big_map.
rewrite /sextic_vieta_polynomial.
exact h.
Qed.

Lemma monic_sextic_vieta (roots : 6.-tuple R) (f : monic_sextic) :
  map_poly (intr : int -> R) (monic_polynomial f) =
      \prod_(r <- roots) ('X - r%:P) ->
  @cast_int_values R (monic_elementary_values f) = elementary_values roots.
Proof.
move=> hfactor.
rewrite prod_XsubC_sixE in hfactor.
apply: eq_from_tnth=> i.
rewrite /cast_int_values tnth_mktuple tnth_elementary_values.
case: i=> [[|[|[|[|[|[|i]]]]]] hi] /=.
all: rewrite /monic_elementary_values /=.
- have hi0 : (Ordinal hi : 'I_6) = ord0 by apply: val_inj.
  rewrite hi0.
  rewrite (tnth_nth 0) /=.
  have h5 := congr1 (fun q : {poly R} => q`_5) hfactor.
  move: h5; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; try rewrite !mulr0; try rewrite !mulr1; try rewrite !addr0;
    try rewrite !add0r; try rewrite !subr0; try rewrite !oppr0;
    try rewrite !add0r.
  move=> h5.
  rewrite rmorphN.
  apply: oppr_inj.
  rewrite opprK.
  exact h5.
- have hi1 : (Ordinal hi : 'I_6) = inord 1.
  exact: esym (inord_val (Ordinal hi)).
  rewrite hi1.
  rewrite (tnth_nth 0) (@inordK 5 1 isT) /=.
  have h4 := congr1 (fun q : {poly R} => q`_4) hfactor.
  move: h4; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; rewrite !mulr0 !mulr1 !addr0 !add0r !subr0;
    try rewrite !oppr0; try rewrite !add0r.
  move=> h4.
  exact h4.
- have hi2 : (Ordinal hi : 'I_6) = inord 2.
  exact: esym (inord_val (Ordinal hi)).
  rewrite hi2.
  rewrite (tnth_nth 0) (@inordK 5 2 isT) /=.
  have h3 := congr1 (fun q : {poly R} => q`_3) hfactor.
  move: h3; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; rewrite !mulr0 !mulr1 !addr0 !add0r !subr0;
    try rewrite !oppr0; try rewrite !add0r.
  move=> h3.
  rewrite rmorphN.
  apply: oppr_inj.
  rewrite opprK.
  exact h3.
- have hi3 : (Ordinal hi : 'I_6) = inord 3.
  exact: esym (inord_val (Ordinal hi)).
  rewrite hi3.
  rewrite (tnth_nth 0) (@inordK 5 3 isT) /=.
  have h2 := congr1 (fun q : {poly R} => q`_2) hfactor.
  move: h2; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; rewrite !mulr0 !mulr1 !addr0 !add0r !subr0;
    try rewrite !oppr0; try rewrite !add0r.
  by move=> ->.
- have hi4 : (Ordinal hi : 'I_6) = inord 4.
  exact: esym (inord_val (Ordinal hi)).
  rewrite hi4.
  rewrite (tnth_nth 0) (@inordK 5 4 isT) /=.
  have h1 := congr1 (fun q : {poly R} => q`_1) hfactor.
  move: h1; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; rewrite !mulr0 !mulr1 !addr0 !add0r !subr0;
    try rewrite !oppr0; try rewrite !add0r.
  move=> h1.
  rewrite rmorphN.
  apply: oppr_inj.
  rewrite opprK.
  exact h1.
- have hi5 : (Ordinal hi : 'I_6) = inord 5.
  exact: esym (inord_val (Ordinal hi)).
  rewrite hi5.
  rewrite (tnth_nth 0) (@inordK 5 5 isT) /=.
  have h0 := congr1 (fun q : {poly R} => q`_0) hfactor.
  move: h0; rewrite coef_map /monic_polynomial /sextic_vieta_polynomial.
  repeat (first
    [ rewrite coefD | rewrite coefB | rewrite coefN | rewrite coefCM
    | rewrite coefXn | rewrite coefX | rewrite coefC ]).
  simpl; try rewrite !mulr0; try rewrite !mulr1; try rewrite !addr0;
    try rewrite !add0r; try rewrite !subr0; try rewrite !oppr0;
    try rewrite !add0r.
  by move=> ->.
- by move: hi.
Qed.

End GenericVieta.

End PolynomialFormulasSexticVietaBridge.
