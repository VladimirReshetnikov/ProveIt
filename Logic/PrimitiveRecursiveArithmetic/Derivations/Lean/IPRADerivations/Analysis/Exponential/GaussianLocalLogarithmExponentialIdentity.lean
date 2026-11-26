import IPRADerivations.Analysis.Logarithm.GaussianLocalLogarithmName

/-!
# Source C4 for the actual ORIGINAL local logarithm and exponential names

At the computed auxiliary precision clock(p+4), the actual exponential
sample is compared with the SAME finite composition after its original
logarithm rounding error. Both actual finite cutoffs exceed that clock.
The checked dyadic composition error and actual exponential pointCN
transport back to p with an explicit19/2^(p+4) budget. This proves name
equivalence to1+z/N and to the checked cofinal finite-composition name.
Only the original positive divisor and Euclidean half-disk source guards
are inputs. No exponential/logarithm identity or output law is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmExponentialIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (evaluate ofGaussian)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFiniteLogarithmPolynomial (composition)
open GaussianFiniteLogarithmCompositionTail (linearValue)
open GaussianLocalLogarithmName (source pointF data)
open GaussianUnitDiskExponentialName (shifted index)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentialPoint (p z R N : PTm n) : PTm n := GaussianUnitDiskExponentialName.sample pointF p (data z R N)
def finiteDegree (p : PTm n) : PTm n := DyadicComplexLogarithm.precision (shifted p)+two
def finiteValue (p z N : PTm n) : PTm n := evaluate (composition (finiteDegree p) (index p)) (ofGaussian z N)
def auxiliary (p : PTm n) : PTm n := GaussianFiniteLogarithmDyadicTail.clock (p+num 4)
def denominator (p : PTm n) : PTm n := unit (p+num 4)
@[simp] theorem subst_exponentialPoint {l : ℕ} (σ : Fin n → PTm l) (p z R N : PTm n) :
    Syn.subst σ (exponentialPoint p z R N) = exponentialPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [exponentialPoint]
@[simp] theorem subst_finiteDegree {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (finiteDegree p) = finiteDegree (Syn.subst σ p) := by simp [finiteDegree,DyadicComplexLogarithm.precision]
@[simp] theorem subst_finiteValue {l : ℕ} (σ : Fin n → PTm l) (p z N : PTm n) :
    Syn.subst σ (finiteValue p z N) = finiteValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ N) := by simp [finiteValue]
@[simp] theorem subst_auxiliary {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (auxiliary p) = auxiliary (Syn.subst σ p) := by simp [auxiliary]
@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (denominator p) = denominator (Syn.subst σ p) := by simp [denominator]

theorem index_exact (p : PTm n) : Γ ⊢[PRAAx] index p ≐ p+num 11 := by
  have e : Γ ⊢[PRAAx] succ (index p) ≐ succ (p+num 11) :=
    (GaussianRationalExponentialTail.last_successor one (shifted p)).eqTrans (by
      unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt shifted
      ipra_ring)
  exact (pred_succ _).eqSymm.eqTrans ((congrPred e).eqTrans (pred_succ _))
theorem auxiliary_lower (p : PTm n) : Γ ⊢[PRAAx] le (p+num 4) (auxiliary p) :=
  le_of_eq_add (d := num 9*p+num 116) (by unfold auxiliary GaussianFiniteLogarithmDyadicTail.clock; ipra_ring)
theorem denominator_positive (p : PTm n) : Γ ⊢[PRAAx] le one (denominator p) := unit_positive _
theorem denominator_factor (p : PTm n) : Γ ⊢[PRAAx] denominator p ≐ unit p*num 16 :=
  (pw_add two p (num 4)).eqTrans (congrMul (.eqRefl _) GaussianFiniteLogarithmDyadicTail.two_four)
theorem auxiliary_unit_lower (p : PTm n) : Γ ⊢[PRAAx] le (denominator p) (unit (auxiliary p)) :=
  GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (auxiliary_lower p)

theorem exponential_point_at (p z R N : PTm n) : Γ ⊢[PRAAx] exponentialPoint p z R N ≐
    GaussianRationalPolynomialExponential.scalarSum (GaussianLocalLogarithmName.point (shifted p) z R N) (index p) := by
  simpa only [exponentialPoint,GaussianUnitDiskExponentialName.value,GaussianUnitDiskExponentialName.query,
    GaussianLocalLogarithmName.point] using GaussianUnitDiskExponentialName.sample_at (Γ := Γ) pointF p (data z R N)
theorem finite_value_at (p z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] finiteValue p z N ≐
    GaussianRationalPolynomialExponential.scalarSum
      (GaussianFiniteLogarithmSampler.sample z N (DyadicComplexLogarithm.precision (shifted p))) (index p) :=
  GaussianFiniteLogarithmSampler.composition_eq_original_sample z N _ _ hN

/-- Actual old observation rounding, at the SAME finite exponential
cutoff. The real original finite H query is also in the unit disk. -/
theorem rounding_comparison (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R N) (finiteValue p z N) (num 12) (DyadicComplexLogarithm.unit (shifted p)) := by
  have oldDisk : Γ ⊢[PRAAx] bounded
      (GaussianFiniteLogarithmSampler.sample z N (DyadicComplexLogarithm.precision (shifted p))) one one :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ GaussianLocalLogarithmName.four_positive (le_refl _)
      (le_of_eq_add (d := one) (by ipra_ring)) (GaussianLocalLogarithmName.finite_sample_bound z R N _ h)
  have raw := GaussianRationalExponentialLipschitz.scalar_sum_lipschitz _ _ _ _ (index p)
    (GaussianLocalLogarithmName.unit_positive _) (GaussianLocalLogarithmName.point_unit_disk _ z R N h) oldDisk
      (GaussianLocalLogarithmName.point_rounding_distance _ z R N h.andE₁)
  exact distance_congr (exponential_point_at _ _ _ _).eqSymm (finite_value_at _ _ _ h.andE₁).eqSymm
    (by ipra_ring) (.eqRefl _) raw

theorem rounding_budget (p : PTm n) : Γ ⊢[PRAAx] le (num 12*denominator p)
    (DyadicComplexLogarithm.unit (shifted (auxiliary p))) := by
  have first : Γ ⊢[PRAAx] le (num 12*denominator p) (DyadicComplexLogarithm.unit (p+num 4)) := by
    refine le_of_eq_add (d := num 4*denominator p) ?_
    have e := natEq (GaussianLocalLogarithmName.unit_factor (Γ := Γ) (p+num 4))
    apply deriveNat; unfold denominator; ipra_simps; rw [e]; ring
  have growth : Γ ⊢[PRAAx] le (DyadicComplexLogarithm.precision (p+num 4))
      (DyadicComplexLogarithm.precision (shifted (auxiliary p))) :=
    le_congr (by unfold DyadicComplexLogarithm.precision; ipra_ring)
      (by unfold DyadicComplexLogarithm.precision shifted; ipra_ring)
      (add_le_add_right (num 8) (le_trans (le_add_right p (num 4)) (auxiliary_lower p)))
  exact le_trans first (GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) growth)

theorem auxiliary_rounding (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint (auxiliary p) z R N) (finiteValue (auxiliary p) z N) one (denominator p) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianLocalLogarithmName.unit_positive _) (denominator_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (rounding_budget p)) (rounding_comparison _ z R N h)

theorem auxiliary_composition (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (finiteValue (auxiliary p) z N) (linearValue (ofGaussian z N)) one (denominator p) := by
  have hd : Γ ⊢[PRAAx] le (GaussianFiniteLogarithmDyadicTail.clock (p+num 4)) (finiteDegree (auxiliary p)) :=
    le_of_eq_add (d := num 10) (by unfold auxiliary finiteDegree DyadicComplexLogarithm.precision shifted; ipra_ring)
  have hk : Γ ⊢[PRAAx] le (GaussianFiniteLogarithmDyadicTail.clock (p+num 4)) (index (auxiliary p)) :=
    le_congr (.eqRefl _) (index_exact (auxiliary p)).eqSymm (le_add_right _ (num 11))
  have raw := GaussianFiniteLogarithmDyadicTail.composition_error _ _ (p+num 4) (ofGaussian z N) hd hk
    (GaussianFiniteLogarithmCompositionName.original_half_disk z R N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
  exact distance_radius_mono _ _ _ _ _ _ (GaussianFiniteLogarithmDyadicTail.precision_positive _) (denominator_positive p)
    (le_congr (one_mul _).eqSymm (one_mul _).eqSymm
      (GaussianFactorBudget.power_monotone_length two _ _ (le_succ_self one) (le_add_right _ (num 4)))) raw

theorem auxiliary_cauchy (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R N) (exponentialPoint (auxiliary p) z R N) (num 17) (denominator p) := by
  have raw := GaussianNameEquivalence.point_at (GaussianUnitDiskExponentialName.nameF pointF) (data z R N) p (auxiliary p)
    (GaussianLocalLogarithmName.original_exponential_name_regular z R N h)
  have radius : Γ ⊢[PRAAx] le ((unit p+unit (auxiliary p))*denominator p)
      (num 17*(unit p*unit (auxiliary p))) := by
    have grow := add_le_add_right (num 16*unit p*unit (auxiliary p))
      (le_mul_mono (le_refl (unit p)) (auxiliary_unit_lower (Γ := Γ) p))
    refine le_congr ?_ (by ipra_ring) grow
    have e := natEq (denominator_factor (Γ := Γ) p)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive _))
    (denominator_positive p) radius raw

/-- Source C4 at each requested precision, with three separately
derived finite errors17/D,1/D,1/D and D=2^(p+4). -/
theorem source_comparison (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R N) (linearValue (ofGaussian z N)) two (unit p) := by
  have combined := distance_triangle_same _ _ _ _ _ _ (denominator_positive p)
    (distance_triangle_same _ _ _ _ _ _ (denominator_positive p) (auxiliary_cauchy p z R N h) (auxiliary_rounding p z R N h))
    (auxiliary_composition p z R N h)
  have radius : Γ ⊢[PRAAx] le (((num 17+one)+one)*unit p) (two*denominator p) := by
    refine le_of_eq_add (d := num 13*unit p) ?_
    have e := natEq (denominator_factor (Γ := Γ) p)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive p) (unit_positive p) radius combined

theorem source_constant_comparison (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R N) (GaussianFiniteLogarithmCompositionName.constant p (ofGaussian z N)) two (unit p) :=
  distance_congr (.eqRefl _) (GaussianFiniteLogarithmCompositionName.constant_at _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (source_comparison p z R N h)

/-- Name-level C4 for the original local power-series logarithm sampler
and the actual checked bounded-name exponential operation. -/
theorem source_diagonal (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    diagonalEquivalent (GaussianUnitDiskExponentialName.nameF pointF) GaussianFiniteLogarithmCompositionName.constantF
      (data z R N) (ofGaussian z N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEquivalent,exponentialPoint,GaussianUnitDiskExponentialName.sample,
    GaussianFiniteLogarithmCompositionName.constant,GaussianRationalHorner.subst_ofGaussian,
    Syn.shift,GaussianLocalLogarithmName.subst_data] using source_constant_comparison (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift N) hs

theorem source_cross (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianUnitDiskExponentialName.nameF pointF) GaussianFiniteLogarithmCompositionName.constantF
      (data z R N) (ofGaussian z N) :=
  GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (GaussianLocalLogarithmName.original_exponential_name_regular z R N h)
    (GaussianFiniteLogarithmCompositionName.constant_regular _) (source_diagonal z R N h)

/-- The original rounded-logarithm exponential and the actual cofinal
finite-composition name are equivalent, at their distinct original data. -/
theorem source_cofinal_cross (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianUnitDiskExponentialName.nameF pointF) GaussianFiniteLogarithmCompositionName.nameF
      (data z R N) (ofGaussian z N) :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (source_cross z R N h)
    (GaussianNameEquivalence.cross_symm _ _ _ _
      (GaussianFiniteLogarithmCompositionName.name_cross_equivalent _
        (GaussianFiniteLogarithmCompositionName.original_half_disk z R N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)))

/-! An actual PR4 certificate retains both compared values, the concrete
auxiliary precision and the real finite-composition intermediate. -/
def output (p z R N : PTm n) : PTm n := pairT (exponentialPoint p z R N)
  (pairT (linearValue (ofGaussian z N)) (pairT (auxiliary p) (finiteValue (auxiliary p) z N)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (p z R N : PTm n) : PTm n := PTm.app outputF ![p,z,R,N]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p z R N : PTm n) :
    Syn.subst σ (output p z R N) = output (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p z R N : PTm n) :
    Syn.subst σ (run p z R N) = run (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (p z R N : PTm n) : Γ ⊢[PRAAx] run p z R N ≐ output p z R N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,z,R,N]
theorem returned_exponential (p z R N : PTm n) : Γ ⊢[PRAAx] fstT (run p z R N) ≐ exponentialPoint p z R N :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_tail (p z R N : PTm n) : Γ ⊢[PRAAx] sndT (run p z R N) ≐
    pairT (linearValue (ofGaussian z N)) (pairT (auxiliary p) (finiteValue (auxiliary p) z N)) :=
  (congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_linear (p z R N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z R N)) ≐ linearValue (ofGaussian z N) :=
  (congrFst (returned_tail _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_pair (p z R N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z R N)) ≐ pairT (auxiliary p) (finiteValue (auxiliary p) z N) :=
  (congrSnd (returned_tail _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_auxiliary (p z R N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z R N))) ≐ auxiliary p :=
  (congrFst (returned_pair _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_finite_value (p z R N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z R N))) ≐ finiteValue (auxiliary p) z N :=
  (congrSnd (returned_pair _ _ _ _)).eqTrans (snd_pair _ _)
theorem returned_comparison (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p z R N)) (fstT (sndT (run p z R N))) two (unit p) :=
  distance_congr (returned_exponential _ _ _ _).eqSymm (returned_linear _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (source_comparison p z R N h)

theorem actual_named_exponential_old_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (exponentialPoint (var 0) (var 1) (var 2) (var 3) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GaussianLocalLogarithmName.point (shifted (var 0)) (var 1) (var 2) (var 3)) (index (var 0))) :=
  closeUniv 4 (exponential_point_at _ _ _ _)
theorem original_logarithm_exponential_finite_rounding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded (exponentialPoint (var 0) (var 1) (var 2) (var 3))
      (finiteValue (var 0) (var 1) (var 3)) (num 12) (DyadicComplexLogarithm.unit (shifted (var 0)))) :=
  closeUniv 4 (.impI (rounding_comparison _ _ _ _ Prf.hyp0))
theorem original_logarithm_exponential_source_C4_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded (exponentialPoint (var 0) (var 1) (var 2) (var 3))
      (linearValue (ofGaussian (var 1) (var 3))) two (unit (var 0))) := closeUniv 4 (.impI (source_comparison _ _ _ _ Prf.hyp0))
theorem original_logarithm_exponential_source_C4_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ diagonalEquivalent (GaussianUnitDiskExponentialName.nameF pointF)
      GaussianFiniteLogarithmCompositionName.constantF (data (var 0) (var 1) (var 2)) (ofGaussian (var 0) (var 2))) :=
  closeUniv 3 (.impI (source_diagonal _ _ _ Prf.hyp0))
theorem original_logarithm_exponential_source_C4_cross_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent (GaussianUnitDiskExponentialName.nameF pointF)
      GaussianFiniteLogarithmCompositionName.constantF (data (var 0) (var 1) (var 2)) (ofGaussian (var 0) (var 2))) :=
  closeUniv 3 (.impI (source_cross _ _ _ Prf.hyp0))
theorem original_named_exponential_cofinal_composition_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent (GaussianUnitDiskExponentialName.nameF pointF)
      GaussianFiniteLogarithmCompositionName.nameF (data (var 0) (var 1) (var 2)) (ofGaussian (var 0) (var 2))) :=
  closeUniv 3 (.impI (source_cofinal_cross _ _ _ Prf.hyp0))
theorem actual_source_C4_certificate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem original_returned_source_C4_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3)))
      (fstT (sndT (run (var 0) (var 1) (var 2) (var 3)))) two (unit (var 0))) :=
  closeUniv 4 (.impI (returned_comparison _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmExponentialIdentity
