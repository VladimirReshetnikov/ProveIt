import IPRADerivations.Analysis.GaussianExactDiskExponential

/-!
# The exact C6 disk of the original canonical Gamma tail

The SAME original tail observations supply an A/B+C/2^p envelope with
A=R², B=N, C=1. Actual rational shrinking and explicit retiming yield
a regular representative in the exact R²/N disk, cross-equivalent to
the original tail. This includes R=0 and every original valid cutoff.

If R²≤N, its actual unit-disk exponential observations are within
3R²/N of one. Original exponential properness across radii identifies
this exponential with the original tail exponentiated at its computed
integer radius. The latter observations are within 3R²/N+2/2^p of
one. No exact disk is incorrectly asserted for the old rounded samples,
and no C8 factor identity or nonzero condition is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaExactTailDisk

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalTailName (source pointF point)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianFastValueCut (rawEnvelope)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_point_envelope (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    bounded (point p z R B N) (R*R*unit p+one*N) (N*unit p) := by
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (GaussianGammaCanonicalTailName.denominator_positive p N h.andE₂.andE₁)
    (positive_product _ _ h.andE₂.andE₁ (unit_positive p)) _ (GaussianGammaCanonicalTailName.point_bound p z R B N h)
  have e := natEq (GaussianLocalLogarithmName.unit_factor (Γ := Γ) p)
  apply le_of_eq_add (d := num 14*N*N*unit p)
  apply deriveNat
  simp only [GaussianGammaCanonicalTailName.radius,GaussianGammaCanonicalTailName.denominator]
  ipra_simps
  rw [e]
  ring

theorem original_raw_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    rawEnvelope pointF (GaussianGammaCanonicalTailName.data z R B N) (R*R) N one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [rawEnvelope,point,Syn.shift,GaussianGammaCanonicalTailName.subst_data,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_point_envelope (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

def exactF : PR 2 := GaussianExactDiskShrinking.nameF pointF
def exactData (z R B N : PTm n) : PTm n :=
  GaussianExactDiskShrinking.data (GaussianGammaCanonicalTailName.data z R B N) (R*R) N one
def exactPoint (p z R B N : PTm n) : PTm n := ap2 exactF p (exactData z R B N)
def exponentialF : PR 2 := GaussianUnitDiskExponentialName.nameF exactF
def exponentialPoint (p z R B N : PTm n) : PTm n := ap2 exponentialF p (exactData z R B N)
def originalRadius (z R B N : PTm n) : PTm n :=
  GaussianNameBounds.U pointF (GaussianGammaCanonicalTailName.data z R B N)
def originalExponentialF : PR 2 := GaussianRadiusExponentialName.nameF pointF
def originalExponentialData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data
  (originalRadius z R B N) (GaussianGammaCanonicalTailName.data z R B N)
def originalExponentialPoint (p z R B N : PTm n) : PTm n := ap2 originalExponentialF p (originalExponentialData z R B N)

@[simp] theorem subst_exactData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (exactData z R B N) = exactData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exactData]
@[simp] theorem subst_exactPoint {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (exactPoint p z R B N) = exactPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exactPoint]
@[simp] theorem subst_exponentialPoint {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (exponentialPoint p z R B N) = exponentialPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialPoint]
@[simp] theorem subst_originalRadius {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (originalRadius z R B N) = originalRadius (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [originalRadius]
@[simp] theorem subst_originalExponentialData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (originalExponentialData z R B N) = originalExponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [originalExponentialData]
@[simp] theorem subst_originalExponentialPoint {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (originalExponentialPoint p z R B N) = originalExponentialPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [originalExponentialPoint]

theorem exact_point_at (p z R B N : PTm n) : Γ ⊢[PRAAx] exactPoint p z R B N ≐
    GaussianExactDiskShrinking.value pointF p (GaussianGammaCanonicalTailName.data z R B N) (R*R) N one :=
  GaussianExactDiskShrinking.sample_at pointF p _ _ _ _

theorem exponential_point_at (p z R B N : PTm n) : Γ ⊢[PRAAx] exponentialPoint p z R B N ≐
    GaussianRationalPolynomialExponential.scalarSum (exactPoint (GaussianUnitDiskExponentialName.shifted p) z R B N)
      (GaussianUnitDiskExponentialName.index p) :=
  GaussianUnitDiskExponentialName.sample_at exactF p (exactData z R B N)

theorem original_exponential_point_at (p z R B N : PTm n) : Γ ⊢[PRAAx] originalExponentialPoint p z R B N ≐
    GaussianRationalPolynomialExponential.scalarSum
      (point (GaussianRadiusExponentialName.inputPrecision (originalRadius z R B N) p) z R B N)
      (GaussianRadiusExponentialName.index (originalRadius z R B N) p) :=
  GaussianRadiusExponentialName.sample_at pointF (originalRadius z R B N) p (GaussianGammaCanonicalTailName.data z R B N)

theorem exact_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN exactF (exactData z R B N) :=
  GaussianExactDiskShrinking.name_regular pointF _ _ _ _ h.andE₂.andE₁
    (GaussianGammaCanonicalTailName.name_regular z R B N h) (original_raw_envelope z R B N h)

theorem exact_cross (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent exactF pointF (exactData z R B N) (GaussianGammaCanonicalTailName.data z R B N) :=
  GaussianExactDiskShrinking.cross_equivalent pointF _ _ _ _ h.andE₂.andE₁
    (GaussianGammaCanonicalTailName.name_regular z R B N h) (original_raw_envelope z R B N h)

theorem exact_disk (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianExponentialSmallPerturbation.smallSamples exactF (exactData z R B N) (R*R) N :=
  GaussianExactDiskShrinking.exact_disk_samples pointF _ _ _ _ h.andE₂.andE₁ (original_raw_envelope z R B N h)

theorem exact_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (exactPoint p z R B N) (R*R) N :=
  GaussianExponentialSmallPerturbation.small_samples_at exactF _ _ _ p (exact_disk z R B N h)

theorem exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hN : Γ ⊢[PRAAx] le (R*R) N) : Γ ⊢[PRAAx] GaussianUnitDiskExponentialName.input exactF (exactData z R B N) :=
  GaussianExactDiskExponential.shrunk_unit_input pointF _ _ _ _ h.andE₂.andE₁ hN
    (GaussianGammaCanonicalTailName.name_regular z R B N h) (original_raw_envelope z R B N h)

theorem exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hN : Γ ⊢[PRAAx] le (R*R) N) : Γ ⊢[PRAAx] pointCN exponentialF (exactData z R B N) :=
  GaussianUnitDiskExponentialName.name_regular _ _ (exponential_input z R B N h hN)

theorem exact_exponential_error (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hN : Γ ⊢[PRAAx] le (R*R) N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R B N) qone (num 3*R*R) N :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianExponentialSmallPerturbation.uniformly_small_perturbation exactF p _ _ _ h.andE₂.andE₁ hN (exact_disk z R B N h))

theorem original_exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input pointF (originalRadius z R B N) (GaussianGammaCanonicalTailName.data z R B N) := by
  have cn := GaussianGammaCanonicalTailName.name_regular z R B N h
  refine .andI cn ?_
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianRootApproximationWitness.pointBounds,originalRadius] using
    GaussianNameBounds.all_samples_bounded pointF _ cn

theorem original_exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    pointCN originalExponentialF (originalExponentialData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (original_exponential_input z R B N h)

/-- The corrected unit-disk program and original larger-disk program represent the SAME exponential. -/
theorem exponential_cross (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hN : Γ ⊢[PRAAx] le (R*R) N) : Γ ⊢[PRAAx]
    crossEquivalent exponentialF originalExponentialF (exactData z R B N) (originalExponentialData z R B N) :=
  GaussianNameEquivalence.cross_symm _ _ _ _
    (GaussianExactDiskExponential.original_exp_equiv_shrunk_unit pointF (originalRadius z R B N)
      (GaussianGammaCanonicalTailName.data z R B N) (R*R) N one (original_exponential_input z R B N h)
      h.andE₂.andE₁ hN (original_raw_envelope z R B N h))

/-- Original observations retain their dyadic observation error; the exact C6 term is unchanged. -/
theorem original_exponential_error (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hN : Γ ⊢[PRAAx] le (R*R) N) : Γ ⊢[PRAAx]
    distanceBounded (originalExponentialPoint p z R B N) qone (num 3*R*R*unit p+two*N) (N*unit p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianExactDiskExponential.original_exp_sample_near_one pointF p (originalRadius z R B N)
      (GaussianGammaCanonicalTailName.data z R B N) (R*R) N one (original_exponential_input z R B N h)
      h.andE₂.andE₁ hN (original_raw_envelope z R B N h))

theorem actual_corrected_C6_tail_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (exactPoint (var 0) (var 1) (var 2) (var 3) (var 4) ≐ GaussianExactDiskShrinking.value pointF (var 0)
      (GaussianGammaCanonicalTailName.data (var 1) (var 2) (var 3) (var 4)) (var 2*var 2) (var 4) one) :=
  closeUniv 5 (exact_point_at _ _ _ _ _)
theorem original_exact_C6_tail_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      pointCN exactF (exactData (var 0) (var 1) (var 2) (var 3)) ⋏
        (crossEquivalent exactF pointF (exactData (var 0) (var 1) (var 2) (var 3)) (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3)) ⋏
          GaussianExponentialSmallPerturbation.smallSamples exactF (exactData (var 0) (var 1) (var 2) (var 3)) (var 1*var 1) (var 3))) :=
  closeUniv 4 (.impI (.andI (exact_regular _ _ _ _ Prf.hyp0) (.andI (exact_cross _ _ _ _ Prf.hyp0) (exact_disk _ _ _ _ Prf.hyp0))))
theorem original_exact_C6_tail_exponential_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ le (var 2*var 2) (var 4) ⟶
      distanceBounded (exponentialPoint (var 0) (var 1) (var 2) (var 3) (var 4)) qone (num 3*var 2*var 2) (var 4)) :=
  closeUniv 5 (.impI (.impI (exact_exponential_error _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_independent_radii_tail_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ le (var 1*var 1) (var 3) ⟶
      crossEquivalent exponentialF originalExponentialF (exactData (var 0) (var 1) (var 2) (var 3)) (originalExponentialData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (exponential_cross _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_C6_tail_exponential_observation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ le (var 2*var 2) (var 4) ⟶
      distanceBounded (originalExponentialPoint (var 0) (var 1) (var 2) (var 3) (var 4)) qone
        (num 3*var 2*var 2*unit (var 0)+two*var 4) (var 4*unit (var 0))) :=
  closeUniv 5 (.impI (.impI (original_exponential_error _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaExactTailDisk
