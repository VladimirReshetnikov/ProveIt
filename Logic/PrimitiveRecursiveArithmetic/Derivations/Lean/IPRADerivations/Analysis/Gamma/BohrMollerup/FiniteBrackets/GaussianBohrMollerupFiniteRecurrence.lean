import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupBracketEndpoints
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerCompatibility

/-!
# Finite log recurrence on the original Bohr–Mollerup presentation

At one fixed precision, each original recurrence instance has an
explicit rational residual. Quantifier-free induction sums the
residuals with the literal shifted logarithm terms. The original
finite-sum clock then yields the exact named finite recurrence.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupFiniteRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBohrMollerupBracketEndpoints (rowBody row_at sumData sum_regular)
open GaussianBohrMollerupChords (argument_congr)
open GaussianBohrMollerupPresentation (Presentation argument laws values recurrence observe_value observe_recurrence)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_at)
open GaussianNameRingLaws (add_sample_error three)
open GaussianNamedFiniteSumFamily (finite body term_at sample_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "Sum" => GaussianBohrMollerupBracketEndpoints.sumF
local notation "logData" => GaussianHarmonicLogarithmName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def logSum (p a b N : PTm n) : PTm n := finite H rowBody p N (pairT a b)

@[simp] theorem subst_logSum {m : ℕ} (σ : Fin n → PTm m) (p a b N : PTm n) :
    Syn.subst σ (logSum p a b N) = logSum (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [logSum,finite]

theorem shifted_source (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] source (a+b*N) b :=
  .andI (le_trans h.andE₁ (le_add_right a (b*N))) h.andE₂

private theorem step_error (P : Presentation) (p a b : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P.nameF p (argument P (a+b) b))
      (qadd (ap2 H p (logData a b)) (ap2 P.nameF p (argument P a b))) (num 5) (unit p) := by
  let f := P.nameF
  let x := argument P a b
  let y := logData a b
  let d := argument P (a+b) b
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have hy := GaussianHarmonicLogarithmName.name_regular a b hs
  have hx := (observe_value P a b hv hs).andE₁
  have hr := cross_at f (addF H f) d (addData y x) p p (observe_recurrence P a b hr hs)
  have first := distance_radius_mono _ _ (U+U) (U*U) two U (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by ipra_ring)) hr
  have last := add_sample_error H f y x p hy hx
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first last)

def finiteBound (P : Presentation) (p a b N : PTm n) : Fm PTm n :=
  distanceBounded (ap2 P.nameF p (argument P (a+b*N) b))
    (qadd (ap2 P.nameF p (argument P a b)) (logSum p a b N)) (num 5*N) (unit p)

@[simp] theorem subst_finiteBound {m : ℕ} (σ : Fin n → PTm m) (P : Presentation) (p a b N : PTm n) :
    (finiteBound P p a b N).subst σ =
      finiteBound P (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [finiteBound]

private theorem finite_zero (P : Presentation) (p a b : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] finiteBound P p a b zero := by
  let u := ap2 P.nameF p (argument P a b)
  have e := congrAp2 P.nameF (Prf.eqRefl p) (argument_congr (Γ := Γ) P _ _ _ _ (by ipra_ring : Γ ⊢[PRAAx] a+b*zero ≐ a) (.eqRefl b))
  have v := GaussianRationalFiniteSum.sum_zero (Γ := Γ) (body H rowBody) (pairT p (pairT a b))
  have real := GaussianSignedNameExponentialOrder.real_sample_at _ _ p (observe_value P a b hv hs).andE₂
  have read : Γ ⊢[PRAAx] qadd u (logSum p a b zero) ≐ u :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl u) v).eqTrans
      (GaussianRationalLinearProduct.qadd_zero_right u real.andE₁)
  exact distance_congr e.eqSymm read.eqSymm (mul_zero _).eqSymm (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero u (unit p) (unit_positive p))

private theorem finite_step (P : Presentation) (p a b N : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (hs : Γ ⊢[PRAAx] source a b)
    (ih : Γ ⊢[PRAAx] finiteBound P p a b N) :
    Γ ⊢[PRAAx] finiteBound P p a b (succ N) := by
  let X := a+b*N
  let V := ap2 H p (logData X b)
  let W := ap2 P.nameF p (argument P X b)
  let U := ap2 P.nameF p (argument P a b)
  let S := logSum p a b N
  let D := unit p
  have hd := unit_positive (Γ := Γ) p
  have ea : Γ ⊢[PRAAx] X+b ≐ a+b*succ N := by unfold X; ipra_ring
  have head := congrAp2 P.nameF (Prf.eqRefl p) (argument_congr P _ _ _ _ ea (.eqRefl b))
  have h0 := step_error P p X b hv hr (shifted_source a b N hs)
  have h1 := sum_distance V V W (qadd U S) zero (num 5*N) D hd
    (GaussianRationalPowerDifference.distance_refl_zero V D hd) ih
  have h2 := distance_congr (.eqRefl _) (.eqRefl _) (zero_add _) (.eqRefl _) h1
  have raw := distance_triangle_same _ _ _ _ _ _ hd h0 h2
  have cell := (term_at (Γ := Γ) H rowBody N p (pairT a b)).eqTrans
    (congrAp2 H (.eqRefl p) (row_at N a b))
  have fold : Γ ⊢[PRAAx] logSum p a b (succ N) ≐ qadd S V :=
    (GaussianRationalFiniteSum.sum_succ (body H rowBody) N (pairT p (pairT a b))).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl S) cell)
  have order : Γ ⊢[PRAAx] qadd V (qadd U S) ≐ qadd U (logSum p a b (succ N)) :=
    (GaussianReciprocalHorner.qadd_commutative V (qadd U S)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative U S V).eqTrans
        (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl U) fold.eqSymm))
  exact distance_congr head order (by ipra_ring) (.eqRefl _) raw

theorem finite_error (P : Presentation) (p a b N : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] finiteBound P p a b N := by
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have vh : Δ ⊢[PRAAx] values P := by simpa [Δ,Fm.shift,Syn.shift] using hv.shift
  have rh : Δ ⊢[PRAAx] recurrence P := by simpa [Δ,Fm.shift,Syn.shift] using hr.shift
  have sh : Δ ⊢[PRAAx] source (s a) (s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hs.shift
  have e : Γ ⊢[PRAAx] .all (finiteBound P (s p) (s a) (s b) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_finiteBound,s,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using finite_zero P p a b hv hs
    · simpa only [subst_finiteBound,s,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        finite_step P (s p) (s a) (s b) (var 0) vh.wk rh.wk sh.wk Prf.hyp0
  simpa only [subst_finiteBound,s,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using e.allE N

private theorem diagonal_error (P : Presentation) (p a b N : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P.nameF p (argument P (a+b*N) b))
      (ap2 (addF P.nameF Sum) p (addData (argument P a b) (sumData a b N))) (num 12) (unit p) := by
  let F := P.nameF
  let x := argument P a b
  let y := argument P (a+b*N) b
  let z := sumData a b N
  let k := exponent N p
  let D := unit p
  let U := unit k
  let L := logSum k a b N
  have hD := unit_positive (Γ := Γ) p
  have hX := (observe_value P a b hv hs).andE₁
  have hY := (observe_value P (a+b*N) b hv (shifted_source a b N hs)).andE₁
  have hZ := sum_regular a b N hs
  have late : Γ ⊢[PRAAx] le p k := le_add_right _ _
  have left := GaussianEulerUpperPowerCompatibility.later_cross F F y y p p k (le_refl p) late (cross_refl _ _ hY)
  have gap := query_budget (Γ := Γ) N p
  have approx : Γ ⊢[PRAAx] distanceBounded (ap2 F k y) (qadd (ap2 F k x) L) (num 5) D :=
    distance_radius_mono _ _ (num 5*N) U (num 5) D (unit_positive k) hD
      (by ipra_le 5*sl gap) (finite_error P k a b N hv hr hs)
  have rise := GaussianEulerUpperPowerCompatibility.later_cross F F x x p k p late (le_refl p) (cross_refl _ _ hX)
  have pad := sum_distance (ap2 F k x) (ap2 F p x) L L two zero D hD rise
    (GaussianRationalPowerDifference.distance_refl_zero L D hD)
  have note : Γ ⊢[PRAAx] ap2 Sum p z ≐ L := sample_at H rowBody p N (pairT a b)
  have pad' := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) note.eqSymm)
    (add_zero _) (.eqRefl _) pad
  have last := add_sample_error F Sum x z p hX hZ
  have m := distance_triangle_same _ _ _ _ _ _ hD left approx
  have f := distance_triangle_same _ _ _ _ _ _ hD m pad'
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD f (distance_symmetric _ _ _ _ hD last))

theorem iterated_cross (P : Presentation) (a b N : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] recurrence P) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF (addF P.nameF Sum) (argument P (a+b*N) b)
      (addData (argument P a b) (sumData a b N)) := by
  have hX := (observe_value P a b hv hs).andE₁
  have hY := (observe_value P (a+b*N) b hv (shifted_source a b N hs)).andE₁
  have hZ := sum_regular a b N hs
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 12) hY (add_fast _ _ _ _ hX hZ) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have vh : Δ ⊢[PRAAx] values P := by simpa [Δ,Fm.shift,Syn.shift] using hv.shift
  have rh : Δ ⊢[PRAAx] recurrence P := by simpa [Δ,Fm.shift,Syn.shift] using hr.shift
  have sh : Δ ⊢[PRAAx] source (s a) (s b) := by simpa [Δ,s,Fm.shift,Syn.shift] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Δ,s,Syn.shift,GaussianBohrMollerupPresentation.subst_argument,
    GaussianBohrMollerupBracketEndpoints.subst_sumData,GaussianNameArithmetic.subst_addData,PTm.subst_add,PTm.subst_mul,PTm.subst_num] using
    diagonal_error P (var 0) (s a) (s b) (s N) vh rh sh

theorem actual_original_finite_Bohr_Mollerup_recurrence_closed (P : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (laws P ⟶ source (var 0) (var 1) ⟶ crossEquivalent P.nameF (addF P.nameF Sum)
        (argument P (var 0+var 1*var 2) (var 1)) (addData (argument P (var 0) (var 1)) (sumData (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (iterated_cross P _ _ _ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupFiniteRecurrence
