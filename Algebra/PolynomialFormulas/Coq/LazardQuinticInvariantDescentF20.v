From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticThetaGaloisBridge QuinticRecursiveFactor
  QuinticPaddedSymmetrization SexticRationalRootSearch
  SexticGaloisAction QuinticCanonicalDecision
  LazardQuinticRootProjections LazardQuinticRootBranchEquivariance
  LazardQuinticRootInvariantF20 LazardQuinticRootOrdering.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Rational descent of all five Lazard invariants by [F20]-invariance.

    A rational theta value fixes its six-point theta index under every
    Galois automorphism.  Reordering by that index's inverse representative
    conjugates the root permutation into the standard [F20].  Since the five
    orbit sums [i4], ..., [i8] are invariant under this subgroup, they are
    all Galois-fixed and hence belong to the rational prime field.

    This gives an independent, group-theoretic replacement for treating the
    four tail invariants as supplied rational certificates. *)
Module PolynomialFormulasLazardQuinticInvariantDescentF20.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module TGB := PolynomialFormulasQuinticThetaGaloisBridge.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module SGA := PolynomialFormulasSexticGaloisAction.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module IF20 := PolynomialFormulasLazardQuinticRootInvariantF20.
Module RO := PolynomialFormulasLazardQuinticRootOrdering.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Section FixedRational.

Variable p : {poly rat}.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let iota : {rmorphism L -> algC} := numfield_inC p.

(** Fixed-field descent stated directly in the canonical rational embedding,
    rather than through the auxiliary complex embedding used by the generic
    MathComp--Abel theorem. *)
Lemma lazard_numfield_fixed_is_rational (z : L) :
  (forall g : gal_of {:L},
      g \in 'Gal({:L} / 1%AS)%G -> g z = z) ->
  exists q : rat, z = ratrL q.
Proof.
move=> hfixed.
have [q hq] := (proj1 (@SGA.fixed_iff_rational p z)) hfixed.
exists q.
apply: (fmorph_inj iota).
rewrite hq.
change ((ratr q : algC) = ((iota \o ratrL)%FUN) q).
exact: esym (fmorph_eq_rat ((iota \o ratrL)%FUN) q).
Qed.

End FixedRational.

Section CanonicalDescent.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

Definition lazard_selected_roots (i : 'I_6) : 5.-tuple L :=
  TV.permute_quintic_roots ((representative i)^-1) roots.

(** Relabelling the canonical roots by an inverse representative conjugates
    their Galois permutation by the corresponding representative. *)
Lemma lazard_selected_roots_gal (i : 'I_6) (g : gal_of {:L}) :
  map_tuple g (lazard_selected_roots i) =
    TV.permute_quintic_roots
      ((@GA.quintic_gal_perm p p_size g) ^ representative i)
      (lazard_selected_roots i).
Proof.
apply: eq_from_tnth=> k.
rewrite tnth_map /lazard_selected_roots
  !TV.tnth_permute_quintic_roots.
rewrite -(@GA.quintic_gal_permP p p_size g
  ((representative i)^-1 k)).
rewrite conjg_permE.
by rewrite permK.
Qed.

(** Rationality of the selected theta value puts the conjugated Galois
    permutation in the standard [F20]. *)
Lemma lazard_selected_gal_perm_mem_standard_F20
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (g : gal_of {:L}) :
  ((@GA.quintic_gal_perm p p_size g) ^ representative i) \in
    standard_F20.
Proof.
have hfixed :
    g (TV.quintic_theta_value roots i) =
      TV.quintic_theta_value roots i.
  by rewrite hi /ratrL char0_ratrE (fmorph_rat g q).
have hgal := @TGB.quintic_theta_value_gal p p_size g i.
have hindex :
    TV.quintic_theta_index_action
      (@GA.quintic_gal_perm p p_size g) i = i.
  apply: (CD.canonical_quintic_theta_value_injective p_irr).
  exact: eq_trans (esym hgal) hfixed.
have hconjugate :
    @GA.quintic_gal_perm p p_size g \in
      (standard_F20 :^ (representative i)^-1).
  apply/TGB.quintic_theta_index_action_fixedP.
  exact: hindex.
by move: hconjugate; rewrite mem_conjgV.
Qed.

(** The complete invariant tuple on the selected ordering is fixed by every
    splitting-field automorphism. *)
Theorem lazard_selected_root_invariants_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (g : gal_of {:L}) :
  IF20.lazard_root_invariants_map g
      (RP.lazard_root_invariants (lazard_selected_roots i)) =
    RP.lazard_root_invariants (lazard_selected_roots i).
Proof.
have hmap :=
  IF20.lazard_root_invariants_mapE g (lazard_selected_roots i).
rewrite lazard_selected_roots_gal in hmap.
have hmem := lazard_selected_gal_perm_mem_standard_F20 p_irr hi g.
have hinv := @IF20.lazard_root_invariants_standard_F20 L
  (lazard_selected_roots i)
  ((@GA.quintic_gal_perm p p_size g) ^ representative i) hmem.
rewrite hinv in hmap.
exact: hmap.
Qed.

(** All five selected invariant values descend simultaneously to a rational
    tuple; no tail-coordinate certificate is present in the statement. *)
Theorem exists_rational_lazard_invariants_of_selected_root
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  exists j : RP.LazardRootInvariants rat,
    IF20.lazard_root_invariants_map ratrL j =
      RP.lazard_root_invariants (lazard_selected_roots i).
Proof.
pose inv := RP.lazard_root_invariants (lazard_selected_roots i).
have hfixed4 : forall g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G ->
    g (RP.lazard_root_i4 inv) = RP.lazard_root_i4 inv.
  move=> g _.
  have h := congr1 (@RP.lazard_root_i4 L)
    (lazard_selected_root_invariants_fixed p_irr hi g).
  exact: h.
have hfixed5 : forall g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G ->
    g (RP.lazard_root_i5 inv) = RP.lazard_root_i5 inv.
  move=> g _.
  have h := congr1 (@RP.lazard_root_i5 L)
    (lazard_selected_root_invariants_fixed p_irr hi g).
  exact: h.
have hfixed6 : forall g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G ->
    g (RP.lazard_root_i6 inv) = RP.lazard_root_i6 inv.
  move=> g _.
  have h := congr1 (@RP.lazard_root_i6 L)
    (lazard_selected_root_invariants_fixed p_irr hi g).
  exact: h.
have hfixed7 : forall g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G ->
    g (RP.lazard_root_i7 inv) = RP.lazard_root_i7 inv.
  move=> g _.
  have h := congr1 (@RP.lazard_root_i7 L)
    (lazard_selected_root_invariants_fixed p_irr hi g).
  exact: h.
have hfixed8 : forall g : gal_of {:L},
    g \in 'Gal({:L} / 1%AS)%G ->
    g (RP.lazard_root_i8 inv) = RP.lazard_root_i8 inv.
  move=> g _.
  have h := congr1 (@RP.lazard_root_i8 L)
    (lazard_selected_root_invariants_fixed p_irr hi g).
  exact: h.
have [q4 hq4] := @lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i4 inv) hfixed4.
have [q5 hq5] := @lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i5 inv) hfixed5.
have [q6 hq6] := @lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i6 inv) hfixed6.
have [q7 hq7] := @lazard_numfield_fixed_is_rational p
  (RP.lazard_root_i7 inv) hfixed7.
have [q8 hq8] := @lazard_numfield_fixed_is_rational p
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

(** End-to-end coefficient/root-origin package for a scalar resolvent root:
    the ordering is injective and complete, and all five Lazard invariants
    are obtained by mapping one rational tuple. *)
Theorem exists_complete_canonical_lazard_root_origin
    (p_irr : irreducible_poly p) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent roots) (ratrL q)) :
  exists (ordered : 5.-tuple L) (j : RP.LazardRootInvariants rat),
    injective (tnth ordered) /\
    (forall k : 'I_5, root (map_poly ratrL p) (tnth ordered k)) /\
    (forall x : L, root (map_poly ratrL p) x ->
      exists k : 'I_5, x = tnth ordered k) /\
    IF20.lazard_root_invariants_map ratrL j =
      RP.lazard_root_invariants ordered.
Proof.
have [i [ordered hdata]] :=
  RO.exists_canonical_lazard_indexed_root_ordering p_irr hq.
case: hdata=> hordered hdata.
case: hdata=> hi hdata.
case: hdata=> hinj hdata.
case: hdata=> hall hdata.
case: hdata=> hcomplete _.
have [j hj] :=
  exists_rational_lazard_invariants_of_selected_root p_irr hi.
exists ordered, j; split; first exact: hinj.
split; first exact: hall.
split; first exact: hcomplete.
rewrite hordered.
exact: hj.
Qed.

(** Executable scaled-resolvent wrapper. *)
Theorem exists_complete_canonical_lazard_root_origin_of_scaled_resolvent
    (p_irr : irreducible_poly p)
    (hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f)) :
  exists (q : rat) (ordered : 5.-tuple L)
      (j : RP.LazardRootInvariants rat),
    injective (tnth ordered) /\
    (forall k : 'I_5, root (map_poly ratrL p) (tnth ordered k)) /\
    (forall x : L, root (map_poly ratrL p) x ->
      exists k : 'I_5, x = tnth ordered k) /\
    IF20.lazard_root_invariants_map ratrL j =
      RP.lazard_root_invariants ordered.
Proof.
have hsemantic :=
  (proj1 (@CD.quintic_scaled_resolvent_has_rational_root_correct
    L ratrL roots f (CD.canonical_quintic_padded_vieta f)
    (CD.canonical_quintic_resolvent_scale_nonzero p_irr))) hq.
case: hsemantic=> q hqscalar.
have [ordered [j [hinj [hall [hcomplete hj]]]]] :=
  exists_complete_canonical_lazard_root_origin p_irr hqscalar.
by exists q, ordered, j.
Qed.

End CanonicalDescent.

End PolynomialFormulasLazardQuinticInvariantDescentF20.
