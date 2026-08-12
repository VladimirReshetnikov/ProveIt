From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticChapman
  QuinticGaloisAction QuinticRecursiveFactor QuinticCanonicalDecision
  QuinticPaddedSymmetrization SexticRationalRootSearch
  LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root ordering selected by a rational Lazard--Dummit resolvent root.

    The scalar resolvent is the product over six theta values.  A root of
    that polynomial therefore selects an index [i].  By construction, the
    selected theta value is the ten-term Lazard invariant [i4] evaluated on
    the root tuple permuted by the inverse coset representative attached to
    [i].  This file records that elementary but essential selection step and
    proves that the permutation preserves the complete root vector.

    No rationality of [i5], ..., [i8] is assumed here; their descent is the
    subsequent nonsingular invariant-system argument. *)
Module PolynomialFormulasLazardQuinticRootOrdering.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module C := PolynomialFormulasQuinticChapman.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module RP := PolynomialFormulasLazardQuinticRootProjections.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section GenericOrdering.

Variable F : fieldType.

(** Chapman's theta formula is definitionally Lazard's first metacyclic
    invariant after the harmless simplification [x^1 = x]. *)
Lemma lazard_root_i4_theta_formulaE (roots : 5.-tuple F) :
  RP.lazard_root_i4 (RP.lazard_root_invariants roots) =
    C.quintic_theta_formula roots.
Proof.
rewrite /RP.lazard_root_invariants /=
  /RP.lazard_root_orbit_formula /C.quintic_theta_formula !expr1.
reflexivity.
Qed.

Lemma lazard_permute_root_tuple_injective
    (roots : 5.-tuple F) (s : S5)
    (hroots : injective (tnth roots)) :
  injective (tnth (TV.permute_quintic_roots s roots)).
Proof.
move=> i j.
rewrite !TV.tnth_permute_quintic_roots=> hij.
apply: perm_inj.
exact: hroots hij.
Qed.

Lemma lazard_permute_root_tuple_sound
    (p : {poly F}) (roots : 5.-tuple F) (s : S5)
    (hall : forall k : 'I_5, root p (tnth roots k)) :
  forall k : 'I_5,
    root p (tnth (TV.permute_quintic_roots s roots) k).
Proof.
move=> k.
rewrite TV.tnth_permute_quintic_roots.
exact: hall.
Qed.

Lemma lazard_permute_root_tuple_complete
    (p : {poly F}) (roots : 5.-tuple F) (s : S5)
    (hcomplete : forall x : F, root p x ->
      exists k : 'I_5, x = tnth roots k) :
  forall x : F, root p x ->
    exists k : 'I_5,
      x = tnth (TV.permute_quintic_roots s roots) k.
Proof.
move=> x hx.
have [k hk] := hcomplete x hx.
exists (s^-1 k).
by rewrite TV.tnth_permute_quintic_roots permKV.
Qed.

(** A resolvent root selects a concrete ordering with the requested [i4]
    value, without losing any root-vector correctness property. *)
Theorem lazard_exists_root_ordering_of_scalar_resolvent_root
    (p : {poly F}) (roots : 5.-tuple F) (q : F)
    (hroots : injective (tnth roots))
    (hall : forall k : 'I_5, root p (tnth roots k))
    (hcomplete : forall x : F, root p x ->
      exists k : 'I_5, x = tnth roots k)
    (hq : root (TV.quintic_scalar_resolvent roots) q) :
  exists ordered : 5.-tuple F,
    injective (tnth ordered) /\
    (forall k : 'I_5, root p (tnth ordered k)) /\
    (forall x : F, root p x ->
      exists k : 'I_5, x = tnth ordered k) /\
    RP.lazard_root_i4 (RP.lazard_root_invariants ordered) = q.
Proof.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff roots q)) hq.
pose s := ((representative i)^-1)%g.
pose ordered := TV.permute_quintic_roots s roots.
exists ordered; split.
- exact: lazard_permute_root_tuple_injective hroots.
- split.
  + exact: lazard_permute_root_tuple_sound hall.
  + split.
    * exact: lazard_permute_root_tuple_complete hcomplete.
    * rewrite lazard_root_i4_theta_formulaE /ordered /s.
      exact: eq_trans (esym (C.quintic_theta_value_formulaE roots i)) hi.
Qed.

End GenericOrdering.

Section CanonicalOrdering.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

(** Indexed form of the ordering theorem.  Exposing the selected theta index
    records the conjugate [F20] which controls the subsequent Galois-descent
    argument. *)
Theorem exists_canonical_lazard_indexed_root_ordering
    (p_irr : irreducible_poly p) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent roots) (ratrL q)) :
  exists (i : 'I_6) (ordered : 5.-tuple L),
    ordered = TV.permute_quintic_roots ((representative i)^-1) roots /\
    TV.quintic_theta_value roots i = ratrL q /\
    injective (tnth ordered) /\
    (forall k : 'I_5, root (map_poly ratrL p) (tnth ordered k)) /\
    (forall x : L, root (map_poly ratrL p) x ->
      exists k : 'I_5, x = tnth ordered k) /\
    RP.lazard_root_i4 (RP.lazard_root_invariants ordered) = ratrL q.
Proof.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff roots (ratrL q))) hq.
pose ordered :=
  TV.permute_quintic_roots ((representative i)^-1) roots.
exists i, ordered; split; first exact: erefl.
split; first exact: hi.
split.
- exact: lazard_permute_root_tuple_injective
    (@GA.quintic_root_tuple_injective p p_size p_irr).
- split.
  + move=> k.
    rewrite /ordered TV.tnth_permute_quintic_roots.
    exact: CD.canonical_quintic_all_roots.
  + split.
    * apply: lazard_permute_root_tuple_complete.
      move=> x hx.
      exact: (proj1 (CD.canonical_quintic_root_iff_exists_index x)) hx.
    * rewrite lazard_root_i4_theta_formulaE /ordered.
      exact: eq_trans
        (esym (C.quintic_theta_value_formulaE roots i)) hi.
Qed.

(** Coefficient-level specialization: for the canonical splitting-field
    tuple of a monic rational quintic, a rational scalar-resolvent root
    chooses a complete injective ordering whose Lazard [i4] is that rational
    value. *)
Theorem exists_canonical_lazard_root_ordering
    (p_irr : irreducible_poly p) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent roots) (ratrL q)) :
  exists ordered : 5.-tuple L,
    injective (tnth ordered) /\
    (forall k : 'I_5, root (map_poly ratrL p) (tnth ordered k)) /\
    (forall x : L, root (map_poly ratrL p) x ->
      exists k : 'I_5, x = tnth ordered k) /\
    RP.lazard_root_i4 (RP.lazard_root_invariants ordered) = ratrL q.
Proof.
apply: (@lazard_exists_root_ordering_of_scalar_resolvent_root
  L (map_poly ratrL p) roots (ratrL q)).
- exact: (@GA.quintic_root_tuple_injective p p_size p_irr).
- exact: CD.canonical_quintic_all_roots.
- move=> x hx.
  exact: (proj1 (CD.canonical_quintic_root_iff_exists_index x)) hx.
- exact: hq.
Qed.

(** The executable, coefficient-only scaled resolvent supplies exactly the
    scalar root required by the preceding ordering theorem.  Thus callers
    do not have to postulate either a root tuple or a rational [i4]
    certificate. *)
Theorem exists_canonical_lazard_root_ordering_of_scaled_resolvent_root
    (p_irr : irreducible_poly p)
    (hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f)) :
  exists (q : rat) (ordered : 5.-tuple L),
    injective (tnth ordered) /\
    (forall k : 'I_5, root (map_poly ratrL p) (tnth ordered k)) /\
    (forall x : L, root (map_poly ratrL p) x ->
      exists k : 'I_5, x = tnth ordered k) /\
    RP.lazard_root_i4 (RP.lazard_root_invariants ordered) = ratrL q.
Proof.
have hsemantic :=
  (proj1 (@CD.quintic_scaled_resolvent_has_rational_root_correct
    L ratrL roots f (CD.canonical_quintic_padded_vieta f)
    (CD.canonical_quintic_resolvent_scale_nonzero p_irr))) hq.
case: hsemantic=> q hqscalar.
exists q.
exact (@exists_canonical_lazard_root_ordering p_irr q hqscalar).
Qed.

End CanonicalOrdering.

End PolynomialFormulasLazardQuinticRootOrdering.
