From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticCanonicalDecision
  LazardQuinticFourier
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootInvariantE
  LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticInvariantDescentF20
  LazardQuinticRootInvariantF20
  LazardQuinticRootInvariantENonzeroF20.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Canonical centering of an ordered quintic root tuple.

    Subtracting one fifth of the root sum gives a depressed tuple.  All
    difference products used in Lazard's first two radical layers are
    translation-invariant, so their nonvanishing transports to this tuple.
    This is the bridge between the general canonical root ordering and the
    depressed formulas. *)
Module PolynomialFormulasLazardQuinticRootCentering.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module LF := PolynomialFormulasLazardQuinticFourier.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module IF20 := PolynomialFormulasLazardQuinticRootInvariantF20.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Section Centering.

Variable F : fieldType.

Add Ring lazard_root_centering_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_centering_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_five_natrE
    | rewrite NR.lazard_numerator_four_natrE
    | rewrite NR.lazard_numerator_two_natrE
    | rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Definition lazard_root_center (roots : 5.-tuple F) : F :=
  RP.lazard_root_esymm1 roots / 5%:R.

Definition lazard_centered_roots (roots : 5.-tuple F) : 5.-tuple F :=
  [tuple tnth roots i - lazard_root_center roots | i < 5].

Lemma tnth_lazard_centered_roots (roots : 5.-tuple F) i :
  tnth (lazard_centered_roots roots) i =
    tnth roots i - lazard_root_center roots.
Proof. by rewrite /lazard_centered_roots tnth_mktuple. Qed.

Lemma lazard_root_esymm1_big (roots : 5.-tuple F) :
  RP.lazard_root_esymm1 roots = \sum_(i : 'I_5) tnth roots i.
Proof.
by rewrite LF.lazard_sum_ord5 /RP.lazard_root_esymm1.
Qed.

Lemma lazard_root_esymm1_permute (g : S5) (roots : 5.-tuple F) :
  RP.lazard_root_esymm1 (TV.permute_quintic_roots g roots) =
    RP.lazard_root_esymm1 roots.
Proof.
rewrite !lazard_root_esymm1_big.
under [LHS] eq_bigr=> i _ do
  rewrite TV.tnth_permute_quintic_roots.
rewrite (reindex_inj (@perm_inj _ g^-1)) /=.
apply: eq_bigr=> i _.
by rewrite permKV.
Qed.

Lemma lazard_centered_roots_permute (g : S5) (roots : 5.-tuple F) :
  lazard_centered_roots (TV.permute_quintic_roots g roots) =
    TV.permute_quintic_roots g (lazard_centered_roots roots).
Proof.
apply: eq_from_tnth=> i.
rewrite tnth_lazard_centered_roots
  !TV.tnth_permute_quintic_roots tnth_lazard_centered_roots.
by rewrite /lazard_root_center lazard_root_esymm1_permute.
Qed.

Lemma lazard_centered_roots_injective (roots : 5.-tuple F) :
  injective (tnth roots) -> injective (tnth (lazard_centered_roots roots)).
Proof.
move=> hroots i j.
rewrite !tnth_lazard_centered_roots=> hij.
apply: hroots.
have hc := congr1 (fun x : F => x + lazard_root_center roots) hij.
by move: hc; rewrite !subrK.
Qed.

Lemma lazard_centered_roots_sum_zero (roots : 5.-tuple F)
    (five_neq0 : (5%:R : F) != 0) :
  RP.lazard_root_esymm1 (lazard_centered_roots roots) = 0.
Proof.
have hcenter : (lazard_root_center roots * 5%:R)%R =
    RP.lazard_root_esymm1 roots.
  rewrite /lazard_root_center.
  exact: (divfK five_neq0 (RP.lazard_root_esymm1 roots)).
rewrite /RP.lazard_root_esymm1 !tnth_lazard_centered_roots.
have hid :
    (tnth roots o0 - lazard_root_center roots) +
      (tnth roots o1 - lazard_root_center roots) +
      (tnth roots o2 - lazard_root_center roots) +
      (tnth roots o3 - lazard_root_center roots) +
      (tnth roots o4 - lazard_root_center roots) =
    RP.lazard_root_esymm1 roots -
      (lazard_root_center roots * 5%:R)%R.
  rewrite /RP.lazard_root_esymm1.
  finish_lazard_root_centering_ring.
by rewrite hid hcenter subrr.
Qed.

(** Translation leaves each raw difference product unchanged. *)
Lemma lazard_root_T_prime_centered (roots : 5.-tuple F) :
  RR.lazard_root_T_prime (lazard_centered_roots roots) =
    RR.lazard_root_T_prime roots.
Proof.
rewrite /RR.lazard_root_T_prime !tnth_lazard_centered_roots.
finish_lazard_root_centering_ring.
Qed.

Lemma lazard_root_U_prime_centered (roots : 5.-tuple F) :
  RR.lazard_root_U_prime (lazard_centered_roots roots) =
    RR.lazard_root_U_prime roots.
Proof.
rewrite /RR.lazard_root_U_prime !tnth_lazard_centered_roots.
finish_lazard_root_centering_ring.
Qed.

Lemma lazard_epsilon_product_centered (roots : 5.-tuple F) :
  RR.lazard_epsilon_product (lazard_centered_roots roots) =
    RR.lazard_epsilon_product roots.
Proof.
rewrite /RR.lazard_epsilon_product !tnth_lazard_centered_roots.
finish_lazard_root_centering_ring.
Qed.

Lemma lazard_root_projection_epsilon_product_centered
    (roots : 5.-tuple F) :
  RP.lazard_root_epsilon_product (lazard_centered_roots roots) =
    RP.lazard_root_epsilon_product roots.
Proof.
rewrite /RP.lazard_root_epsilon_product !tnth_lazard_centered_roots.
finish_lazard_root_centering_ring.
Qed.

Lemma lazard_root_epsilon_centered omega (roots : 5.-tuple F) :
  RP.lazard_root_epsilon omega (lazard_centered_roots roots) =
    RP.lazard_root_epsilon omega roots.
Proof.
by rewrite /RP.lazard_root_epsilon
  lazard_root_projection_epsilon_product_centered.
Qed.

Lemma lazard_root_E_centered (roots : 5.-tuple F) :
  Q.lazard_root_E (lazard_centered_roots roots) = Q.lazard_root_E roots.
Proof.
by rewrite /Q.lazard_root_E
  lazard_root_T_prime_centered lazard_root_U_prime_centered.
Qed.

End Centering.

Section CenteringMap.

Variables (F E : fieldType).

(** Centering commutes with a field embedding.  These lemmas live after the
    one-field centering section so their source and target field parameters
    are generalized independently. *)
Lemma lazard_root_esymm1_map
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (RP.lazard_root_esymm1 roots) =
    RP.lazard_root_esymm1 (map_tuple h roots).
Proof.
by rewrite /RP.lazard_root_esymm1 !rmorphD !tnth_map.
Qed.

Lemma lazard_root_center_map
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (lazard_root_center roots) =
    lazard_root_center (map_tuple h roots).
Proof.
by rewrite /lazard_root_center fmorph_div
  lazard_root_esymm1_map rmorph_nat.
Qed.

Lemma lazard_centered_roots_map
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  map_tuple h (lazard_centered_roots roots) =
    lazard_centered_roots (map_tuple h roots).
Proof.
apply: eq_from_tnth=> i.
by rewrite tnth_map !tnth_lazard_centered_roots
  tnth_map rmorphB lazard_root_center_map.
Qed.

End CenteringMap.

Section CanonicalCentering.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

(** The selected tuple remains injective after depression. *)
Theorem lazard_centered_selected_roots_injective
    (p_irr : irreducible_poly p) (i : 'I_6) :
  injective (tnth
    (lazard_centered_roots (ID.lazard_selected_roots f i))).
Proof.
exact: lazard_centered_roots_injective
  (ENZ.lazard_permute_quintic_roots_injective
    (@GA.quintic_root_tuple_injective p p_size p_irr)).
Qed.

(** Centering commutes with the selected Galois action, so the same
    conjugated [F20] controls the depressed tuple. *)
Lemma lazard_centered_selected_roots_gal
    (i : 'I_6) (sigma : gal_of {:L}) :
  map_tuple sigma
      (lazard_centered_roots (ID.lazard_selected_roots f i)) =
    TV.permute_quintic_roots
      ((@GA.quintic_gal_perm p p_size sigma) ^ representative i)
      (lazard_centered_roots (ID.lazard_selected_roots f i)).
Proof.
rewrite lazard_centered_roots_map
  (@ID.lazard_selected_roots_gal f i sigma).
exact: lazard_centered_roots_permute.
Qed.

(** Consequently all five *centered* Lazard invariants are Galois-fixed. *)
Theorem lazard_centered_selected_root_invariants_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (sigma : gal_of {:L}) :
  IF20.lazard_root_invariants_map sigma
      (RP.lazard_root_invariants
        (lazard_centered_roots (ID.lazard_selected_roots f i))) =
    RP.lazard_root_invariants
      (lazard_centered_roots (ID.lazard_selected_roots f i)).
Proof.
have hmap := IF20.lazard_root_invariants_mapE sigma
  (lazard_centered_roots (ID.lazard_selected_roots f i)).
rewrite lazard_centered_selected_roots_gal in hmap.
have hmem := @ID.lazard_selected_gal_perm_mem_standard_F20
  f p_irr i q hi sigma.
rewrite (@IF20.lazard_root_invariants_standard_F20 L
  (lazard_centered_roots (ID.lazard_selected_roots f i))
  (((@GA.quintic_gal_perm p p_size sigma) ^ representative i)%g)
  hmem) in hmap.
exact: hmap.
Qed.

(** All five centered invariants descend simultaneously to one rational
    tuple; this is the tuple actually used by the depressed formula. *)
Theorem exists_rational_centered_lazard_invariants_of_selected_root
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  exists j : RP.LazardRootInvariants rat,
    IF20.lazard_root_invariants_map ratrL j =
      RP.lazard_root_invariants
        (lazard_centered_roots (ID.lazard_selected_roots f i)).
Proof.
pose inv := RP.lazard_root_invariants
  (lazard_centered_roots (ID.lazard_selected_roots f i)).
have hfixed4 : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_i4 inv) = RP.lazard_root_i4 inv.
  move=> sigma _.
  have h := congr1 (@RP.lazard_root_i4 L)
    (@lazard_centered_selected_root_invariants_fixed
      p_irr i q hi sigma).
  exact: h.
have hfixed5 : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_i5 inv) = RP.lazard_root_i5 inv.
  move=> sigma _.
  have h := congr1 (@RP.lazard_root_i5 L)
    (@lazard_centered_selected_root_invariants_fixed
      p_irr i q hi sigma).
  exact: h.
have hfixed6 : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_i6 inv) = RP.lazard_root_i6 inv.
  move=> sigma _.
  have h := congr1 (@RP.lazard_root_i6 L)
    (@lazard_centered_selected_root_invariants_fixed
      p_irr i q hi sigma).
  exact: h.
have hfixed7 : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_i7 inv) = RP.lazard_root_i7 inv.
  move=> sigma _.
  have h := congr1 (@RP.lazard_root_i7 L)
    (@lazard_centered_selected_root_invariants_fixed
      p_irr i q hi sigma).
  exact: h.
have hfixed8 : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_i8 inv) = RP.lazard_root_i8 inv.
  move=> sigma _.
  have h := congr1 (@RP.lazard_root_i8 L)
    (@lazard_centered_selected_root_invariants_fixed
      p_irr i q hi sigma).
  exact: h.
have [q4 hq4] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i4 inv) hfixed4.
have [q5 hq5] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i5 inv) hfixed5.
have [q6 hq6] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i6 inv) hfixed6.
have [q7 hq7] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i7 inv) hfixed7.
have [q8 hq8] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i8 inv) hfixed8.
exists {| RP.lazard_root_i4 := q4;
          RP.lazard_root_i5 := q5;
          RP.lazard_root_i6 := q6;
          RP.lazard_root_i7 := q7;
          RP.lazard_root_i8 := q8 |}.
apply: BE.lazard_root_invariants_ext=> /=;
  first [exact: esym hq4 | exact: esym hq5 | exact: esym hq6 |
         exact: esym hq7 | exact: esym hq8].
Qed.

(** Nonvanishing of the displayed depressed invariant [E] on the centered
    selected ordering, with no [E != 0] certificate. *)
Theorem lazard_centered_selected_invariant_E_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (five_neq0 : (5%:R : L) != 0) :
  FN.lazard_invariant_E
      (RP.lazard_depressed_of_roots
        (lazard_centered_roots (ID.lazard_selected_roots f i)))
      (RP.lazard_root_invariants
        (lazard_centered_roots (ID.lazard_selected_roots f i))) != 0.
Proof.
have hsum := lazard_centered_roots_sum_zero
  (ID.lazard_selected_roots f i) five_neq0.
rewrite (RIE.lazard_root_invariant_E_eq hsum)
  lazard_root_E_centered.
exact: (@ENZ.lazard_selected_root_E_neq0 f p_irr i q hi).
Qed.

(** Aggregate centered root-origin package: depression, injectivity,
    rational invariants, and nonzero displayed [E] all refer to one and the
    same ordering. *)
Theorem exists_complete_centered_lazard_root_origin
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (five_neq0 : (5%:R : L) != 0) :
  exists (ordered : 5.-tuple L) (j : RP.LazardRootInvariants rat),
    ordered = lazard_centered_roots (ID.lazard_selected_roots f i) /\
    injective (tnth ordered) /\
    RP.lazard_root_esymm1 ordered = 0 /\
    IF20.lazard_root_invariants_map ratrL j =
      RP.lazard_root_invariants ordered /\
    FN.lazard_invariant_E (RP.lazard_depressed_of_roots ordered)
      (RP.lazard_root_invariants ordered) != 0.
Proof.
have [j hj] :=
  @exists_rational_centered_lazard_invariants_of_selected_root
    p_irr i q hi.
exists (lazard_centered_roots (ID.lazard_selected_roots f i)), j.
split; first exact: erefl.
split; first exact: lazard_centered_selected_roots_injective p_irr i.
split; first exact: lazard_centered_roots_sum_zero five_neq0.
split; first exact: hj.
exact: (@lazard_centered_selected_invariant_E_neq0
  p_irr i q hi five_neq0).
Qed.

End CanonicalCentering.

End PolynomialFormulasLazardQuinticRootCentering.
