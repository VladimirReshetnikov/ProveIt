import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalTailName
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerNonzero
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# The actual canonical Gamma tail exponential tends to one

Source C6--C8 requires exp(T_N) as an actual name, including at zeros of
later polynomial prefactors. These are the existing verified exponential
samples applied to the EXACT old canonical tail observations. Genuine
finite scalar Lipschitz and exp(0)=1 give the explicit error3R²/N+6/U.
The computed cofinal N cutoff yields a real PR2 regular name equivalent
to constant one. No quotient, product convergence or exp-addition law is
assumed; the full C7 exponent and C8 product identity remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial)
open GaussianGammaCanonicalTailName (source safeSource data point pointF radius denominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The actual finite scalar sum at zero is one for EVERY runtime cutoff. -/
theorem scalar_zero_point (K : PTm n) : Γ ⊢[PRAAx] scalarSum qzero K ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (scalarSum qzero (var 0) ≐ qone) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,GaussianRationalPolynomialExponential.subst_scalarSum,GaussianRationalHorner.subst_qzero,
        GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.inst_zero] using GaussianRationalPolynomialExponential.scalar_sum_zero (Γ := Γ) (qzero : PTm n)
    · simp only [Fm.subst_eq,GaussianRationalPolynomialExponential.subst_scalarSum,GaussianRationalHorner.subst_qzero,
        GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.repl_zero]
      exact (GaussianRationalPolynomialExponential.scalar_sum_succ qzero (var 0)).eqTrans
        ((GaussianRationalSyntheticDivision.qadd_congr Prf.hyp0
          ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianRationalPowerNonzero.zero_positive_power (var 0))).eqTrans
            (GaussianRationalSyntheticDivision.qmul_zero_right _))).eqTrans
              (GaussianReciprocalHorner.qadd_zero_right qone GaussianRationalSyntheticDivision.qone_canonical))
  simpa only [Fm.subst_eq,GaussianRationalPolynomialExponential.subst_scalarSum,GaussianRationalHorner.subst_qzero,
    GaussianRationalSyntheticDivision.subst_qone,Syn.subst_var,Syn.inst_zero] using all.allE K

def exponentialPoint (p z R B N : PTm n) : PTm n :=
  GaussianUnitDiskExponentialName.sample pointF p (data z R B N)
@[simp] theorem subst_exponentialPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B N : PTm n) :
    Syn.subst σ (exponentialPoint p z R B N) = exponentialPoint (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialPoint]

theorem exponential_point_at (p z R B N : PTm n) : Γ ⊢[PRAAx] exponentialPoint p z R B N ≐
    scalarSum (point (GaussianUnitDiskExponentialName.shifted p) z R B N) (GaussianUnitDiskExponentialName.index p) := by
  simpa only [exponentialPoint,GaussianUnitDiskExponentialName.value,GaussianUnitDiskExponentialName.query,point] using
    GaussianUnitDiskExponentialName.sample_at pointF p (data z R B N)
theorem exponential_canonical (p z R B N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (exponentialPoint p z R B N) :=
  GaussianUnitDiskExponentialName.sample_canonical pointF p (data z R B N)

/-- Literal original tail observations and the finite scalar exponential,
with no completed exp law supplied as a premise. -/
theorem exponential_error (p z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R B N) qone
      (num 3*radius (GaussianUnitDiskExponentialName.shifted p) R N)
      (denominator (GaussianUnitDiskExponentialName.shifted p) N) := by
  let s := GaussianUnitDiskExponentialName.shifted p
  have positive := GaussianGammaCanonicalTailName.denominator_positive s N h.andE₁.andE₂.andE₁
  have raw := GaussianRationalExponentialLipschitz.scalar_sum_lipschitz (point s z R B N) qzero
    (radius s R N) (denominator s N) (GaussianUnitDiskExponentialName.index p) positive
    (GaussianGammaCanonicalTailName.point_unit_disk s z R B N h)
    (GaussianMonicResidualRadius.zero_bounded one one (le_refl _))
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ positive).iffMpr
      (GaussianGammaCanonicalTailName.point_bound s z R B N h.andE₁))
  exact distance_congr (exponential_point_at p z R B N).eqSymm
    (scalar_zero_point (GaussianUnitDiskExponentialName.index p)) (.eqRefl _) (.eqRefl _) raw

theorem shifted_unit_lower (p k : PTm n) (h : Γ ⊢[PRAAx] le k p) : Γ ⊢[PRAAx]
    le (num 12*unit k) (DyadicComplexLogarithm.unit (GaussianUnitDiskExponentialName.shifted p)) := by
  have exponent : Γ ⊢[PRAAx] le k (GaussianUnitDiskExponentialName.shifted p) := le_trans h (le_add_right _ _)
  have powers := GaussianFactorBudget.power_monotone_length two k (GaussianUnitDiskExponentialName.shifted p)
    (le_succ_self one) exponent
  have small : Γ ⊢[PRAAx] le (num 12 : PTm n) (num 16) := le_of_eq_add (d := num 4) (by ipra_ring)
  exact le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx] num 16*unit (GaussianUnitDiskExponentialName.shifted p) ≐
    unit (GaussianUnitDiskExponentialName.shifted p)*num 16).eqTrans
      (GaussianLocalLogarithmName.unit_factor _).eqSymm) (le_mul_mono small powers)

/-- A numerical N bound and the original sample precision suffice. -/
theorem cofinal_error (p k z R B N : PTm n) (h : Γ ⊢[PRAAx] safeSource z R B N)
    (hN : Γ ⊢[PRAAx] le (num 6*R*R*unit k) N) (hkp : Γ ⊢[PRAAx] le k p) : Γ ⊢[PRAAx]
    distanceBounded (exponentialPoint p z R B N) qone one (unit k) := by
  let s := GaussianUnitDiskExponentialName.shifted p
  have combined := add_le_add₂ (le_mul_mono hN (le_refl (DyadicComplexLogarithm.unit s)))
    (le_mul_mono (shifted_unit_lower p k hkp) (le_refl N))
  have budget : Γ ⊢[PRAAx] le ((num 3*radius s R N)*unit k) (one*denominator s N) := by
    apply mul_le_cancel (d' := one)
    exact le_congr (by unfold radius; ipra_ring) (by unfold denominator; ipra_ring) combined
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianGammaCanonicalTailName.denominator_positive s N h.andE₁.andE₂.andE₁) (unit_positive k) budget
    (exponential_error p z R B N h)

/-- This actual integer schedule covers every source guard and the error
budget; no target tail cutoff is assumed externally. -/
def cutoff (R k : PTm n) : PTm n := one+two*R+num 4*R*R+num 6*R*R*unit k
def diskSource (z R B : PTm n) : Fm PTm n := le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)
def cofinalValue (p z R B : PTm n) : PTm n := exponentialPoint p z R B (cutoff R p)
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (R k : PTm n) :
    Syn.subst σ (cutoff R k) = cutoff (Syn.subst σ R) (Syn.subst σ k) := by simp [cutoff]
@[simp] theorem subst_diskSource {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    (diskSource z R B).subst σ = diskSource (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [diskSource]
@[simp] theorem subst_cofinalValue {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (cofinalValue p z R B) = cofinalValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [cofinalValue]

theorem cutoff_positive (R k : PTm n) : Γ ⊢[PRAAx] le one (cutoff R k) :=
  le_of_eq_add (d := two*R+num 4*R*R+num 6*R*R*unit k) (by unfold cutoff; ipra_ring)
theorem cutoff_half_disk (R k : PTm n) : Γ ⊢[PRAAx] le (two*R) (cutoff R k) :=
  le_of_eq_add (d := one+num 4*R*R+num 6*R*R*unit k) (by unfold cutoff; ipra_ring)
theorem cutoff_safe (R k : PTm n) : Γ ⊢[PRAAx] le (num 4*R*R) (cutoff R k) :=
  le_of_eq_add (d := one+two*R+num 6*R*R*unit k) (by unfold cutoff; ipra_ring)
theorem cutoff_error_budget (R k : PTm n) : Γ ⊢[PRAAx] le (num 6*R*R*unit k) (cutoff R k) :=
  le_of_eq_add (d := one+two*R+num 4*R*R) (by unfold cutoff; ipra_ring)
theorem cutoff_source (z R B k : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    safeSource z R B (cutoff R k) :=
  .andI (.andI h.andE₁ (.andI (cutoff_positive R k) (.andI h.andE₂ (cutoff_half_disk R k)))) (cutoff_safe R k)

theorem cofinal_value_distance (p z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    distanceBounded (cofinalValue p z R B) qone one (unit p) :=
  cofinal_error p p z R B (cutoff R p) (cutoff_source z R B p h) (cutoff_error_budget R p) (le_refl p)
theorem cofinal_value_regularity (s t z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    distanceBounded (cofinalValue s z R B) (cofinalValue t z R B) (unit s+unit t) (unit s*unit t) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianReconstructionRoots.distance_triangle _ qone _ one (unit s) one (unit t) (unit_positive s) (unit_positive t)
      (cofinal_value_distance s z R B h)
      (distance_symmetric _ _ _ _ (unit_positive t) (cofinal_value_distance t z R B h)))

/-! The actual cofinal PR2 program, with original z/R/B packed persistently. -/
def cofinalData (z R B : PTm n) : PTm n := pairT z (pairT R B)
def cofinalTerm (p x : PTm n) : PTm n := cofinalValue p (fstT x) (fstT (sndT x)) (sndT (sndT x))
def cofinalF : PR 2 := PTm.toPR (cofinalTerm (var 0) (var 1))
def cofinalPoint (p z R B : PTm n) : PTm n := ap2 cofinalF p (cofinalData z R B)
@[simp] theorem subst_cofinalData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (cofinalData z R B) = cofinalData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [cofinalData]
@[simp] theorem subst_cofinalTerm {l : ℕ} (σ : Fin n → PTm l) (p x : PTm n) :
    Syn.subst σ (cofinalTerm p x) = cofinalTerm (Syn.subst σ p) (Syn.subst σ x) := by simp [cofinalTerm]
@[simp] theorem subst_cofinalPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (cofinalPoint p z R B) = cofinalPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [cofinalPoint]

theorem cofinal_point_at (p z R B : PTm n) : Γ ⊢[PRAAx] cofinalPoint p z R B ≐ cofinalValue p z R B := by
  have prog : Γ ⊢[PRAAx] cofinalPoint p z R B ≐ cofinalTerm p (cofinalData z R B) := by
    simpa [cofinalPoint,cofinalF,ap2] using toPR_eq (Γ := Γ) (cofinalTerm (var 0) (var 1) : PTm 2) ![p,cofinalData z R B]
  refine prog.eqTrans ?_
  simpa only [cofinalTerm,subst_cofinalValue,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (cofinalValue (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,fstT (cofinalData z R B),fstT (sndT (cofinalData z R B)),sndT (sndT (cofinalData z R B))]) (σ' := ![p,z,R,B])
      (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact fst_pair _ _
        · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
        · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
theorem cofinal_point_canonical (p z R B : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (cofinalPoint p z R B) :=
  GaussianRationalHorner.canonical_congr (cofinal_point_at p z R B) (exponential_canonical p z R B (cutoff R p))
theorem cofinal_point_distance (p z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    distanceBounded (cofinalPoint p z R B) qone one (unit p) :=
  distance_congr (cofinal_point_at p z R B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (cofinal_value_distance p z R B h)
theorem cofinal_point_regularity (s t z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    distanceBounded (cofinalPoint s z R B) (cofinalPoint t z R B) (unit s+unit t) (unit s*unit t) :=
  distance_congr (cofinal_point_at s z R B).eqSymm (cofinal_point_at t z R B).eqSymm (.eqRefl _) (.eqRefl _) (cofinal_value_regularity s t z R B h)
theorem cofinal_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    pointCN cofinalF (cofinalData z R B) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] diskSource (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,cofinalPoint,Syn.shift,subst_cofinalData] using
    cofinal_point_regularity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) hs

theorem cofinal_cross_at (s t z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    distanceBounded (cofinalPoint s z R B) (ap2 GaussianNameRingLaws.oneF t zero) (unit s+unit t) (unit s*unit t) :=
  distance_congr (.eqRefl _) (GaussianNameRingLaws.one_at t zero).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive s) (positive_product _ _ (unit_positive s) (unit_positive t))
      (le_of_eq_add (d := unit s*unit s) (by ipra_ring)) (cofinal_point_distance s z R B h))
theorem cofinal_cross_one (z R B : PTm n) (h : Γ ⊢[PRAAx] diskSource z R B) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent cofinalF GaussianNameRingLaws.oneF (cofinalData z R B) zero := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] diskSource (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [GaussianNameEquivalence.crossEquivalent,cofinalPoint,unit,Syn.shift,subst_cofinalData,ConciseIPRA.PTm.subst_zero] using
    cofinal_cross_at (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) hs

theorem actual_finite_zero_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (scalarSum qzero (var 0) ≐ qone) := closeUniv 1 (scalar_zero_point _)
theorem actual_tail_exponential_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (exponentialPoint (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      scalarSum (point (GaussianUnitDiskExponentialName.shifted (var 0)) (var 1) (var 2) (var 3) (var 4))
        (GaussianUnitDiskExponentialName.index (var 0))) := closeUniv 5 (exponential_point_at _ _ _ _ _)
theorem original_tail_exponential_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (safeSource (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (exponentialPoint (var 0) (var 1) (var 2) (var 3) (var 4)) qone
        (num 3*radius (GaussianUnitDiskExponentialName.shifted (var 0)) (var 2) (var 4))
        (denominator (GaussianUnitDiskExponentialName.shifted (var 0)) (var 4))) :=
  closeUniv 5 (.impI (exponential_error _ _ _ _ _ Prf.hyp0))
theorem original_cutoff_tail_exponential_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (safeSource (var 2) (var 3) (var 4) (var 5) ⟶
      le (num 6*var 3*var 3*unit (var 1)) (var 5) ⟶ le (var 1) (var 0) ⟶
        distanceBounded (exponentialPoint (var 0) (var 2) (var 3) (var 4) (var 5)) qone one (unit (var 1))) :=
  closeUniv 6 (.impI (.impI (.impI (cofinal_error _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_tail_exponential_cutoff_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (diskSource (var 0) (var 1) (var 2) ⟶
      (safeSource (var 0) (var 1) (var 2) (cutoff (var 1) (var 3)) ⋏
        le (num 6*var 1*var 1*unit (var 3)) (cutoff (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.andI (cutoff_source _ _ _ _ Prf.hyp0) (cutoff_error_budget _ _)))
theorem actual_cofinal_tail_exponential_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (cofinalPoint (var 0) (var 1) (var 2) (var 3) ≐
      exponentialPoint (var 0) (var 1) (var 2) (var 3) (cutoff (var 2) (var 0))) := closeUniv 4 (cofinal_point_at _ _ _ _)
theorem actual_cofinal_tail_exponential_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalHorner.canonical (cofinalPoint (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (cofinal_point_canonical _ _ _ _)
theorem original_cofinal_tail_exponential_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (diskSource (var 1) (var 2) (var 3) ⟶ distanceBounded (cofinalPoint (var 0) (var 1) (var 2) (var 3)) qone one (unit (var 0))) :=
  closeUniv 4 (.impI (cofinal_point_distance _ _ _ _ Prf.hyp0))
theorem original_cofinal_tail_exponential_independent_precisions_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (diskSource (var 2) (var 3) (var 4) ⟶
      distanceBounded (cofinalPoint (var 0) (var 2) (var 3) (var 4)) (cofinalPoint (var 1) (var 2) (var 3) (var 4))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (cofinal_point_regularity _ _ _ _ _ Prf.hyp0))
theorem original_cofinal_tail_exponential_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (diskSource (var 0) (var 1) (var 2) ⟶ pointCN cofinalF (cofinalData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (cofinal_regular _ _ _ Prf.hyp0))
theorem original_cofinal_tail_exponential_equals_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (diskSource (var 0) (var 1) (var 2) ⟶
      GaussianNameEquivalence.crossEquivalent cofinalF GaussianNameRingLaws.oneF (cofinalData (var 0) (var 1) (var 2)) zero) :=
  closeUniv 3 (.impI (cofinal_cross_one _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalTailExponential
