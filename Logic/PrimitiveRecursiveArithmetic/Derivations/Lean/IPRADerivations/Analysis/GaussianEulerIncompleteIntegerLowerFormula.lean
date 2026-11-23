import IPRADerivations.Analysis.GaussianEulerIncompleteIntegerFormula
import IPRADerivations.Analysis.GaussianEulerIncompleteSum
import IPRADerivations.Analysis.GaussianNamedDifference

/-!
# The original lower incomplete Gamma formula at positive integers

The program is the genuine normalized difference of the constant
factorial name and the original finite factorial-sum upper formula.
The actual incomplete sum and original C21 factorial identity give a
finite observation calculation. Exact rational cancellation uses the
canonical original lower observation. Only its fifteen auxiliary
dyadics disappear in the final regular-name comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerLowerFormula

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteIntegerDomain (source data original_source original_regular_names)
open GaussianEulerIncompleteName (lowerF upperF)
open GaussianGammaFactorialValues (argument radius factorialValue)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalHorner (qadd canonical positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev formulaF : PR 2 := GaussianNamedDifference.nameF constantF GaussianEulerIncompleteIntegerFormula.formulaF
def formulaData (i a b : PTm n) : PTm n := GaussianNamedDifference.data
  (factorialValue i) (GaussianEulerIncompleteIntegerFormula.formulaData i a b)

@[simp] theorem subst_formulaData {m : ℕ} (σ : Fin n → PTm m) (i a b : PTm n) :
    Syn.subst σ (formulaData i a b) = formulaData (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [formulaData,GaussianNamedDifference.subst_data,GaussianGammaFactorialValues.subst_factorialValue,
    GaussianEulerIncompleteIntegerFormula.subst_formulaData]

theorem formula_regular (i a b : PTm n) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN formulaF (formulaData i a b) :=
  GaussianNamedDifference.name_regular constantF GaussianEulerIncompleteIntegerFormula.formulaF _ _
    (constant_regular _) (GaussianEulerIncompleteIntegerFormula.formula_regular i a b)

theorem original_lower_canonical (p i a b : PTm n) : Γ ⊢[PRAAx]
    canonical (ap2 lowerF p (data i a b)) := by
  apply GaussianRationalHorner.canonical_congr (GaussianEulerIncompleteName.lower_at p (argument i) (radius i) one one a b)
  exact GaussianCompactRiemannName.name_canonical _ _ _ _ _ _ _ _

private theorem pair_to_diagonal (t x y : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (unit t+unit t) (unit t*unit t)) : Γ ⊢[PRAAx]
    distanceBounded x y two (unit t) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
    (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by ipra_ring)) h

theorem original_diagonal (t i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 lowerF t (data i a b)) (ap2 formulaF t (formulaData i a b)) (num 15) (unit t) := by
  let L := ap2 lowerF t (data i a b)
  let U := ap2 upperF t (data i a b)
  let S := ap2 GaussianEulerIncompleteSum.sumF t
    (GaussianEulerIncompleteSum.sumData (argument i) (radius i) one one a b)
  let G := ap2 GaussianGammaReciprocalInverse.gammaF t (GaussianGammaFactorialValues.data i)
  let F := factorialValue i
  let W := ap2 GaussianEulerIncompleteIntegerFormula.formulaF t
    (GaussianEulerIncompleteIntegerFormula.formulaData i a b)
  have ht := unit_positive (Γ := Γ) t
  have regs := original_regular_names i a b h
  have gammaSum := pair_to_diagonal t G S (cross_at _ _ _ _ t t
    (GaussianEulerIncompleteSum.original_Gamma_is_incomplete_sum (argument i) (radius i) one one a b (original_source i a b h)))
  have gammaFact := pair_to_diagonal (Γ := Γ) t G F (distance_congr (.eqRefl _) (constant_at t F) (.eqRefl _) (.eqRefl _)
    (cross_at _ _ _ _ t t (GaussianGammaFactorialValues.original_C21_factorial i)))
  have sumRaw : Γ ⊢[PRAAx] distanceBounded S (qadd L U) (num 3) (unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (GaussianNameRingLaws.add_sample_error lowerF upperF (data i a b) (data i a b) t regs.andE₁ regs.andE₂)
  have sumFact : Γ ⊢[PRAAx] distanceBounded (qadd L U) F (num 7) (unit t) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ S _ _ _ _ ht (distance_symmetric _ _ _ _ ht sumRaw)
        (distance_triangle_same S G F _ _ _ ht (distance_symmetric _ _ _ _ ht gammaSum) gammaFact))
  have upper := pair_to_diagonal t U W (cross_at _ _ _ _ t t
    (GaussianEulerIncompleteIntegerFormula.original_upper_integer_formula i a b h))
  have raw := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ ht sumFact upper
  have cancel : Γ ⊢[PRAAx] qsub (qadd L U) U ≐ L :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianReciprocalHorner.qadd_commutative L U) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel U L (original_lower_canonical t i a b))
  have recovered : Γ ⊢[PRAAx] distanceBounded L (qsub F W) (num 9) (unit t) :=
    distance_congr cancel (.eqRefl _) (by ipra_ring) (.eqRefl _) raw
  have readback := GaussianNamedDifference.sample_error (Γ := Γ) constantF GaussianEulerIncompleteIntegerFormula.formulaF
    F (GaussianEulerIncompleteIntegerFormula.formulaData i a b) t (constant_regular _)
    (GaussianEulerIncompleteIntegerFormula.formula_regular i a b)
  have literal : Γ ⊢[PRAAx] distanceBounded (ap2 formulaF t (formulaData i a b)) (qsub F W) (num 6) (unit t) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qsub_congr (constant_at t F) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) readback
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (qsub F W) _ _ _ _ ht recovered (distance_symmetric _ _ _ _ ht literal))

theorem original_lower_integer_formula (i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent lowerF formulaF (data i a b) (formulaData i a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 15)
    (original_regular_names i a b h).andE₁ (formula_regular i a b)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianEulerIncompleteIntegerDomain.subst_source] using h.shift
  change Γ.map Fm.shift ⊢[PRAAx]
    distanceBounded (ap2 lowerF (var 0) (Syn.shift (data i a b)))
      (ap2 formulaF (var 0) (Syn.shift (formulaData i a b))) (Syn.shift (num 15)) (unit (var 0))
  rw [show Syn.shift (data i a b) = data (Syn.shift i) (Syn.shift a) (Syn.shift b) from GaussianEulerIncompleteIntegerDomain.subst_data _ i a b,
    show Syn.shift (formulaData i a b) = formulaData (Syn.shift i) (Syn.shift a) (Syn.shift b) from subst_formulaData _ i a b,
    show Syn.shift (num 15 : PTm n) = (num 15 : PTm (n+1)) by simp only [Syn.shift,LeanProofs.IPRA.PTm.subst_num]]
  exact original_diagonal (var 0) (Syn.shift i) (Syn.shift a) (Syn.shift b) hs

theorem actual_original_lower_incomplete_Gamma_integer_formula_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 1) (var 2) ⟶ crossEquivalent lowerF formulaF (data (var 0) (var 1) (var 2))
        (formulaData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_lower_integer_formula _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerLowerFormula
