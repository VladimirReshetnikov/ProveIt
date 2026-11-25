import IPRADerivations.Analysis.GaussianGammaFoldedC9Bound
import IPRADerivations.Analysis.GaussianGammaExactTailDisk
import IPRADerivations.Analysis.GaussianGammaEulerConvergence
import IPRADerivations.Core.CongruenceTactic

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (pF pData)
open GaussianGammaFoldedC9Bound (tail_input tailRadius tailData negativeExpF negativeExpData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_to_diagonal)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedSmallPerturbationTransport (correctionSamples budgetNumerator budgetDenominator denominator_positive)
open GaussianGammaC9Bound (majorant)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B N : PTm n) : Fm PTm n := GaussianGammaCanonicalExponent.source z R B ⋏
  (le (two*R) N ⋏ le (R*R) N)
@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    (source z R B N).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [source]

theorem folded_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaFoldedMajorantExponent.input z R B N := .andI h.andE₁ h.andE₂.andE₁
theorem local_source (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianGammaCanonicalTailName.source z R B N :=
  GaussianGammaFoldedMajorantExponent.tail_source z R B N (folded_source z R B N h)

def negativeTailF : PR 2 := negativeF GaussianGammaCanonicalTailName.pointF
def negativeTailData (z R B N : PTm n) : PTm n := negativeData (tailData z R B N)
@[simp] theorem subst_negativeTailData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (negativeTailData z R B N) = negativeTailData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [negativeTailData]

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
@[simp] theorem subst_rate {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (rate R) = rate (Syn.subst σ R) := by simp [rate]
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (p R : PTm n) :
    Syn.subst σ (cutoff p R) = cutoff (Syn.subst σ p) (Syn.subst σ R) := by simp [cutoff]

theorem cutoff_guards (p R : PTm n) : Γ ⊢[PRAAx]
    le (two*R) (cutoff p R) ⋏ (le (R*R) (cutoff p R) ⋏ le (rate R*unit (succ p)) (cutoff p R)) := by
  unfold cutoff
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_le 𝔞 (R*R)+𝔞 (rate R*unit (succ p))
  · ipra_le 2*𝔞 R+𝔞 (rate R*unit (succ p))
  · ipra_le 2*𝔞 R+𝔞 (R*R)

theorem cofinal_observation_error (p q z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 pF (succ p) (pData z B (cutoff p R))) (GaussianGammaC7Name.sample q z R B)
      (unit p+unit q) (unit p*unit q) := by
  let N := cutoff p R
  have hg := cutoff_guards (Γ := Γ) p R
  have hs : Γ ⊢[PRAAx] source z R B N := .andI h (.andI hg.andE₁ hg.andE₂.andE₁)
  have hn := (local_source z R B N hs).andE₂.andE₁
  have c : Γ ⊢[PRAAx] le (budgetNumerator (succ p) q (R*R) N (majorant R)*(unit p*unit q))
      ((unit p+unit q)*budgetDenominator (succ p) q N) := by
    have e := natEq (pw_succ (Γ := Γ) two p)
    have hm := hg.andE₂.andE₂
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hm using
      unfold budgetNumerator budgetDenominator rate unit
      ipra_simps
      rw [e]
      ring
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (denominator_positive (succ p) q N hn)
    (positive_product _ _ (unit_positive p) (unit_positive q)) c (observation_error (succ p) q z R B N hs)

def observation (p z R B : PTm n) : PTm n := ap2 pF (succ p) (pData z B (cutoff p R))
def data (z R B : PTm n) : PTm n := pairT z (pairT R B)
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (observation p z R B) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp only [observation,subst_ap2,ConciseIPRA.PTm.subst_succ,GaussianGammaFoldedC9Bound.subst_pData,subst_cutoff]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

theorem observation_congr {p p' z z' R R' B B' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] observation p z R B ≐ observation p' z' R' B' := by
  ipra_congr (observation (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hp, hz, hR, hB]
theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ observation p z R B := by
  have raw := toPR_eq (Γ := Γ)
    (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,data z R B]
  have e : Γ ⊢[PRAAx] sample p z R B ≐
      observation p (fstT (data z R B)) (fstT (sndT (data z R B))) (sndT (sndT (data z R B))) := by
    simpa only [sample,nameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using raw
  have tail := snd_pair (Γ := Γ) z (pairT R B)
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) ((congrFst tail).eqTrans (fst_pair _ _))
    ((congrSnd tail).eqTrans (snd_pair _ _)))

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
