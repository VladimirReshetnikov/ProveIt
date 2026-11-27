import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedC9Bound
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaExactTailDisk
import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaEulerConvergence

/-!
# The quantitative C11 rate of the original folded Weierstrass products

The actual original P_N is C7 times exp(-T_N), by multiplication even at
zeros of the head. Actual negative tail samples give a true R²/N raw
envelope. An equivalent exact-disk representative supplies the unchanged
3 M_R R²/N rate at independent precisions. No pole guard is used.
The factor-by-factor specialization of P_N is a separate supplier.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassConvergence

open_ipra
open GaussianGammaFiniteApproximantName (pF pData)
open GaussianGammaFoldedC9Bound (tail_input tailRadius tailData negativeExpF negativeExpData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_to_diagonal)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedSmallPerturbationTransport (correctionSamples budgetNumerator budgetDenominator)
open GaussianGammaC9Bound (majorant)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B N : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (le (two*R) N ⋏ le (R*R) N)
ipra_subst source

theorem folded_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N := .andI h.andE₁ h.andE₂.andE₁
theorem local_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N :=
  GaussianGammaFoldedMajorantExponent.tail_source z R B N (folded_source z R B N h)

def negativeTailF : PR 2 := negativeF GaussianGammaCanonicalTailName.pointF
def negativeTailData (z R B N : PTm n) : PTm n := negativeData (tailData z R B N)
ipra_subst negativeTailData

theorem negative_tail_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN negativeTailF (negativeTailData z R B N) :=
  GaussianNameRingLaws.negative_fast _ _ (GaussianGammaCanonicalTailName.name_regular z R B N (local_source z R B N h))

theorem negative_tail_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    bounded (ap2 negativeTailF p (negativeTailData z R B N)) (R*R*unit p+one*N) (N*unit p) := by
  let t := GaussianFastValueCut.exponent (one+one) p
  have hs := local_source z R B N h
  have nd := positive_product (Γ := Γ) _ _ hs.andE₂.andE₁ (unit_positive t)
  have first := GaussianRationalReciprocal.bounded_difference qzero (GaussianGammaCanonicalTailName.point t z R B N)
    zero one (R*R*unit t+one*N) (N*unit t) (le_refl one) nd
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl one))
    (GaussianGammaExactTailDisk.original_point_envelope t z R B N hs)
  have actual : Γ ⊢[PRAAx] bounded (ap2 negativeTailF p (negativeTailData z R B N))
      (R*R*unit t+one*N) (N*unit t) := bound_congr (GaussianNameRingLaws.negative_at GaussianGammaCanonicalTailName.pointF (tailData z R B N) p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ nd).iffMpr (bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) first))
  have grow : Γ ⊢[PRAAx] le (unit p) (unit t) :=
    GaussianFactorBudget.power_monotone_length two p t (le_succ_self one) (le_add_right _ _)
  apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ nd
    (positive_product _ _ hs.andE₂.andE₁ (unit_positive p)) _ actual
  have scaled := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono grow (le_refl (N*N))
  exact le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add₂ (le_refl (R*R*N*unit p*unit t)) scaled)

theorem negative_tail_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianFastValueCut.rawEnvelope negativeTailF (negativeTailData z R B N) (R*R) N one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianFastValueCut.rawEnvelope,Syn.shift,subst_negativeTailData,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    negative_tail_point_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

def exactF : PR 2 := GaussianExactDiskShrinking.nameF negativeTailF
def exactData (z R B N : PTm n) : PTm n := GaussianExactDiskShrinking.data (negativeTailData z R B N) (R*R) N one
def smallExpF : PR 2 := GaussianUnitDiskExponentialName.nameF exactF
def smallExpData (z R B N : PTm n) : PTm n := exactData z R B N

theorem small_exp (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    pointCN smallExpF (smallExpData z R B N) ⋏ correctionSamples smallExpF (smallExpData z R B N) (R*R) N := by
  simpa only [smallExpF,smallExpData,exactF,exactData,correctionSamples,
    GaussianExponentialSmallPerturbation.nearOneSamples,GaussianUnitDiskExponentialName.sample] using
    GaussianExactDiskShrinking.exponential_near_one negativeTailF (negativeTailData z R B N) (R*R) N one
      (local_source z R B N h).andE₂.andE₁ h.andE₂.andE₂ (negative_tail_regular z R B N h) (negative_tail_envelope z R B N h)

theorem original_P_actual_product (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    crossEquivalent pF (multiplyF GaussianGammaC7Name.nameF smallExpF) (pData z B N)
      (multiplyData GaussianGammaC7Name.nameF smallExpF (GaussianGammaC7Name.data z R B) (smallExpData z R B N)) := by
  have si := folded_source z R B N h
  have ni := GaussianExponentialInverse.negative_input _ _ _ (tail_input z R B N si)
  have move := GaussianExactDiskExponential.original_exp_equiv_shrunk_unit negativeTailF (tailRadius z R B N)
    (negativeTailData z R B N) (R*R) N one ni (local_source z R B N h).andE₂.andE₁ h.andE₂.andE₂ (negative_tail_envelope z R B N h)
  have oldCN := GaussianGammaFoldedC9Bound.negative_exponential_regular z R B N si
  have hc := GaussianGammaC7Name.name_regular z R B h.andE₁
  have product := GaussianGammaAdjacentCutoff.multiply_cross GaussianGammaC7Name.nameF GaussianGammaC7Name.nameF negativeExpF smallExpF
    (GaussianGammaC7Name.data z R B) (GaussianGammaC7Name.data z R B) (negativeExpData z R B N) (smallExpData z R B N)
    hc hc oldCN (small_exp z R B N h).andE₁ (cross_refl _ _ hc) move
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianGammaFoldedC9Bound.withdrawal_is_original_P z R B N si)) product

theorem observation_error (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 pF p (pData z B N)) (GaussianGammaC7Name.sample q z R B)
      (budgetNumerator p q (R*R) N (majorant R)) (budgetDenominator p q N) :=
  GaussianNamedSmallPerturbationTransport.independent_error GaussianGammaC7Name.nameF smallExpF pF
    (GaussianGammaC7Name.data z R B) (smallExpData z R B N) (pData z B N) (majorant R) (R*R) N p q
    (local_source z R B N h).andE₂.andE₁ (GaussianGammaC7Name.name_regular z R B h.andE₁)
    (GaussianGammaEulerConvergence.reciprocal_prefactor z R B h.andE₁) (small_exp z R B N h).andE₂ (original_P_actual_product z R B N h)

def rate (R : PTm n) : PTm n := num 3*majorant R*(R*R)
def cutoff (p R : PTm n) : PTm n := two*R+R*R+rate R*unit (succ p)
ipra_subst rate
ipra_subst cutoff

theorem cutoff_guards (p R : PTm n) : Γ ⊢[PRAAx]
    le (two*R) (cutoff p R) ⋏ (le (R*R) (cutoff p R) ⋏ le (rate R*unit (succ p)) (cutoff p R)) :=
  GaussianGammaEulerConvergence.cutoff_bounds (two*R) (R*R) (rate R*unit (succ p))

theorem finite_cutoff_error (p q z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) (hcut : Γ ⊢[PRAAx] le (cutoff p R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 pF (succ p) (pData z B N)) (GaussianGammaC7Name.sample q z R B)
      (unit p+unit q) (unit p*unit q) := by
  have hg := cutoff_guards (Γ := Γ) p R
  have hs : Γ ⊢[PRAAx] source z R B N :=
    .andI h (.andI (le_trans hg.andE₁ hcut) (le_trans hg.andE₂.andE₁ hcut))
  have hn := (local_source z R B N hs).andE₂.andE₁
  exact GaussianNamedSmallPerturbationTransport.absorb_successor_budget _ _ p q (R*R) N (majorant R) hn
    (le_trans hg.andE₂.andE₂ hcut) (observation_error (succ p) q z R B N hs)

theorem cofinal_observation_error (p q z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 pF (succ p) (pData z B (cutoff p R))) (GaussianGammaC7Name.sample q z R B)
      (unit p+unit q) (unit p*unit q) :=
  finite_cutoff_error p q z R B (cutoff p R) h (le_refl _)

def observation (p z R B : PTm n) : PTm n := ap2 pF (succ p) (pData z B (cutoff p R))
def data (z R B : PTm n) : PTm n := pairT z (pairT R B)
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)
ipra_subst observation
ipra_subst data

theorem observation_congr {p p' z z' R R' B B' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] observation p z R B ≐ observation p' z' R' B' := by
  ipra_congr (observation (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hp, hz, hR, hB]
theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ observation p z R B := by
  simpa [sample, nameF, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2) (observation (var 0) (var 1) (var 2) (var 3)) p ![z, R, B])

theorem named_equivalence (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] crossEquivalent nameF GaussianGammaC7Name.nameF (data z R B) (GaussianGammaC7Name.data z R B) := by
  refine .allI (.allI ?_)
  let z' := Syn.shift (Syn.shift z)
  let R' := Syn.shift (Syn.shift R)
  let B' := Syn.shift (Syn.shift B)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianGammaCanonicalExponent.source z' R' B' := by
    simpa only [Fm.shift,Syn.shift,GaussianGammaCanonicalExponent.subst_source,z',R',B'] using h.shift.shift
  have bound := GaussianRationalDistanceOrder.distance_congr (sample_at (var 1) z' R' B').eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cofinal_observation_error (var 1) (var 0) z' R' B' hs)
  simpa only [crossEquivalent,sample,GaussianGammaC7Name.sample,Syn.shift,subst_data,
    GaussianGammaC7Name.subst_data,unit,GaussianEuclideanPointDistance.unit,z',R',B'] using bound

theorem name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  have e := named_equivalence z R B h
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem original_folded_P_C11_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded (ap2 pF (var 0) (pData (var 2) (var 4) (var 5)))
      (GaussianGammaC7Name.sample (var 1) (var 2) (var 3) (var 4))
      (budgetNumerator (var 0) (var 1) (var 3*var 3) (var 5) (majorant (var 3))) (budgetDenominator (var 0) (var 1) (var 5))) :=
  closeUniv 6 (.impI (observation_error _ _ _ _ _ _ Prf.hyp0))
theorem original_folded_P_C11_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianGammaCanonicalExponent.source (var 2) (var 3) (var 4) ⟶
      distanceBounded (ap2 pF (succ (var 0)) (pData (var 2) (var 4) (cutoff (var 0) (var 3))))
        (GaussianGammaC7Name.sample (var 1) (var 2) (var 3) (var 4))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (cofinal_observation_error _ _ _ _ _ Prf.hyp0))

theorem actual_cofinal_folded_P_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (var 0) (var 1) (var 2) (var 3) ≐ observation (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (sample_at _ _ _ _)
theorem original_folded_P_C11_named_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF GaussianGammaC7Name.nameF
      (data (var 0) (var 1) (var 2)) (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (named_equivalence _ _ _ Prf.hyp0))
theorem original_folded_P_C11_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaWeierstrassConvergence
