From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The five root-defined Lazard invariants are invariant under the standard
    Frobenius subgroup [F20].

    Rather than enumerate twenty permutations, we use the certified
    decomposition

      [standard_F20 = <five_cycle> <*> <multiplier_two>].

    The ten-term orbit formula is visibly fixed by each generator; closure
    under powers and the product decomposition then gives the full subgroup
    theorem uniformly for all exponent pairs. *)
Module PolynomialFormulasLazardQuinticRootInvariantF20.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section MapInvariants.

Variables (F E : fieldType) (h : {rmorphism F -> E}).

(** Coordinatewise extension of scalars for the five root invariants. *)
Definition lazard_root_invariants_map
    (i : RP.LazardRootInvariants F) : RP.LazardRootInvariants E :=
  {| RP.lazard_root_i4 := h (RP.lazard_root_i4 i);
     RP.lazard_root_i5 := h (RP.lazard_root_i5 i);
     RP.lazard_root_i6 := h (RP.lazard_root_i6 i);
     RP.lazard_root_i7 := h (RP.lazard_root_i7 i);
     RP.lazard_root_i8 := h (RP.lazard_root_i8 i) |}.

(** The explicit orbit sum commutes with every field embedding. *)
Lemma lazard_root_orbit_formula_map a b (roots : 5.-tuple F) :
  h (RP.lazard_root_orbit_formula a b roots) =
    RP.lazard_root_orbit_formula a b (map_tuple h roots).
Proof.
rewrite /RP.lazard_root_orbit_formula
  !rmorphD !rmorphM !rmorphXn !tnth_map.
reflexivity.
Qed.

Lemma lazard_root_invariants_mapE (roots : 5.-tuple F) :
  lazard_root_invariants_map (RP.lazard_root_invariants roots) =
    RP.lazard_root_invariants (map_tuple h roots).
Proof.
apply: BE.lazard_root_invariants_ext;
  exact: lazard_root_orbit_formula_map.
Qed.

End MapInvariants.

Section Invariance.

Variable F : fieldType.

Add Ring lazard_root_invariant_f20_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_invariant_f20_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Cyclic relabelling merely rotates the ten summands. *)
Lemma lazard_root_orbit_formula_five_cycle a b (roots : 5.-tuple F) :
  RP.lazard_root_orbit_formula a b
      (TV.permute_quintic_roots five_cycle roots) =
    RP.lazard_root_orbit_formula a b roots.
Proof.
rewrite /RP.lazard_root_orbit_formula
  !TV.tnth_permute_quintic_roots
  five_cycle_o0 five_cycle_o1 five_cycle_o2
  five_cycle_o3 five_cycle_o4.
set x0a := ((tnth roots o0 : F) ^+ a)%R.
set x1a := ((tnth roots o1 : F) ^+ a)%R.
set x2a := ((tnth roots o2 : F) ^+ a)%R.
set x3a := ((tnth roots o3 : F) ^+ a)%R.
set x4a := ((tnth roots o4 : F) ^+ a)%R.
set x0b := ((tnth roots o0 : F) ^+ b)%R.
set x1b := ((tnth roots o1 : F) ^+ b)%R.
set x2b := ((tnth roots o2 : F) ^+ b)%R.
set x3b := ((tnth roots o3 : F) ^+ b)%R.
set x4b := ((tnth roots o4 : F) ^+ b)%R.
clearbody x0a x1a x2a x3a x4a x0b x1b x2b x3b x4b.
rewrite [(x0a * x4b * x1b)%R]mulrAC
  [(x1a * x4b * x3b)%R]mulrAC
  [(x2a * x4b * x0b)%R]mulrAC
  [(x3a * x4b * x2b)%R]mulrAC.
exact: (@GRing.add F).[ACl 3 * 4 * 6 * 5 * 7 * 8 * 10 * 9 * 1 * 2].
Qed.

(** Multiplication by two permutes the same ten summands. *)
Lemma lazard_root_orbit_formula_multiplier_two a b
    (roots : 5.-tuple F) :
  RP.lazard_root_orbit_formula a b
      (TV.permute_quintic_roots multiplier_two roots) =
    RP.lazard_root_orbit_formula a b roots.
Proof.
rewrite /RP.lazard_root_orbit_formula
  !TV.tnth_permute_quintic_roots
  multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
  multiplier_two_o3 multiplier_two_o4.
set x0a := ((tnth roots o0 : F) ^+ a)%R.
set x1a := ((tnth roots o1 : F) ^+ a)%R.
set x2a := ((tnth roots o2 : F) ^+ a)%R.
set x3a := ((tnth roots o3 : F) ^+ a)%R.
set x4a := ((tnth roots o4 : F) ^+ a)%R.
set x0b := ((tnth roots o0 : F) ^+ b)%R.
set x1b := ((tnth roots o1 : F) ^+ b)%R.
set x2b := ((tnth roots o2 : F) ^+ b)%R.
set x3b := ((tnth roots o3 : F) ^+ b)%R.
set x4b := ((tnth roots o4 : F) ^+ b)%R.
clearbody x0a x1a x2a x3a x4a x0b x1b x2b x3b x4b.
rewrite [(x0a * x4b * x1b)%R]mulrAC
  [(x4a * x2b * x1b)%R]mulrAC
  [(x1a * x4b * x3b)%R]mulrAC.
exact: (@GRing.add F).[ACl 2 * 1 * 7 * 8 * 3 * 4 * 9 * 10 * 5 * 6].
Qed.

(** An invariant of one relabelling is invariant under every power of it. *)
Lemma lazard_root_orbit_formula_expg a b (g : S5)
    (hg : forall roots : 5.-tuple F,
      RP.lazard_root_orbit_formula a b
          (TV.permute_quintic_roots g roots) =
        RP.lazard_root_orbit_formula a b roots) n
    (roots : 5.-tuple F) :
  RP.lazard_root_orbit_formula a b
      (TV.permute_quintic_roots (g ^+ n) roots) =
    RP.lazard_root_orbit_formula a b roots.
Proof.
elim: n roots=> [|n ih] roots.
- by rewrite expg0 TV.permute_quintic_roots_one.
- rewrite expgS TV.permute_quintic_roots_mul.
  exact: eq_trans
    (hg (TV.permute_quintic_roots (g ^+ n) roots)) (ih roots).
Qed.

(** Uniform invariance of the orbit formula under every element of the
    standard Frobenius subgroup. *)
Theorem lazard_root_orbit_formula_standard_F20 a b
    (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  RP.lazard_root_orbit_formula a b
      (TV.permute_quintic_roots g roots) =
    RP.lazard_root_orbit_formula a b roots.
Proof.
move=> hg.
have hnorm : standard_C4 \subset 'N(standard_C5).
  exact: standard_C4_sub_standard_F20.
have hjoin : (affine_F20 : {set S5}) =
    (standard_C5 * standard_C4)%g.
  exact: norm_joinEr hnorm.
have hgprod : g \in (standard_C5 * standard_C4)%g.
  by move: hg; rewrite -affine_F20E hjoin.
case/imset2P: hgprod=> u v hu hv ->.
move/cycleP: hu=> [m ->].
move/cycleP: hv=> [n ->].
rewrite TV.permute_quintic_roots_mul.
transitivity
  (RP.lazard_root_orbit_formula a b
    (TV.permute_quintic_roots (multiplier_two ^+ n) roots)).
- exact (@lazard_root_orbit_formula_expg a b five_cycle
    (@lazard_root_orbit_formula_five_cycle a b) m
    (TV.permute_quintic_roots (multiplier_two ^+ n) roots)).
- exact (@lazard_root_orbit_formula_expg a b multiplier_two
    (@lazard_root_orbit_formula_multiplier_two a b) n roots).
Qed.

(** All five invariant coordinates are therefore fixed at once. *)
Theorem lazard_root_invariants_standard_F20
    (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  RP.lazard_root_invariants (TV.permute_quintic_roots g roots) =
    RP.lazard_root_invariants roots.
Proof.
move=> hg.
apply: BE.lazard_root_invariants_ext;
  exact: lazard_root_orbit_formula_standard_F20 hg.
Qed.

End Invariance.

End PolynomialFormulasLazardQuinticRootInvariantF20.
