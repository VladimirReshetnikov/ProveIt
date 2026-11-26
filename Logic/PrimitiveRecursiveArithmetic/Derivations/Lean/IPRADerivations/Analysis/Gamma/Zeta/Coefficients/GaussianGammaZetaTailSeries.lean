import IPRADerivations.Analysis.Gamma.Zeta.Coefficients.GaussianGammaZetaDegreeName
import IPRADerivations.Core.CongruenceTactic

/-!
# Original C16 as an actual cofinal zeta-coefficient series name

At requested precision p, use the actual zeta-tail polynomial name one
bit later and degree cutoff L_p=p+R². Its computed C18 remainder is at
most 2^(-p-1). Together with the polynomial observation error this gives
the exact independent-name comparison to the ORIGINAL canonical T_N.
The displayed coefficients are the original C17 zeta-minus-prefix names;
no power-series identity is a premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaTailSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalTailName (source point)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def cutoff (p R : PTm n) : PTm n := p+R*R
def observation (p z R B N : PTm n) : PTm n := GaussianGammaZetaDegreeName.sample (succ p) z R B N (cutoff p R)
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p R : PTm n) :
    Syn.subst σ (cutoff p R) = cutoff (Syn.subst σ p) (Syn.subst σ R) := by simp [cutoff]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B N : PTm n) :
    Syn.subst σ (observation p z R B N) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ N) := by simp [observation,GaussianGammaZetaDegreeName.sample]

theorem cutoff_cofinal (p R : PTm n) : Γ ⊢[PRAAx] le p (cutoff p R) := le_add_right p (R*R)
theorem degree_budget (p R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le ((R*R)*unit (succ p)) (GaussianGammaCofinalDegreeTail.rateDen N (cutoff p R)) := by
  let A := unit (succ p)*pw two (R*R)
  have first := AnalyticNumberTheory.PhiLower.le_mul_mono (Γ := Γ) (le_refl (unit (succ p)))
    (le_trans (le_succ_self (R*R)) (RationalClosure.succ_le_two_pow (R*R)))
  have last : Γ ⊢[PRAAx] le A (N*A) := le_congr (one_mul A) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono hN (le_refl A))
  have eq : Γ ⊢[PRAAx] GaussianGammaCofinalDegreeTail.rateDen N (cutoff p R) ≐ N*A := by
    unfold GaussianGammaCofinalDegreeTail.rateDen unit
    exact congrMul (.eqRefl _) ((congrAp2 powF (by unfold cutoff; ipra_ring) (.eqRefl two)).eqTrans (pw_add two (succ p) (R*R)))
  exact le_congr (mul_comm (unit (succ p)) (R*R)) eq.eqSymm (le_trans first last)

theorem observation_error (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B N) (point q z R B N) (unit p+unit q) (unit p*unit q) := by
  let L := cutoff p R
  let V := GaussianGammaCofinalDegreeTail.rateDen N L
  have vp := GaussianGammaCofinalDegreeTail.rate_den_positive N L h.andE₂.andE₁
  have old := GaussianNamedInverseRate.rate_at GaussianGammaCanonicalTailName.pointF GaussianGammaZetaDegreeName.nameF
    (GaussianGammaCanonicalTailName.data z R B N) (GaussianGammaZetaDegreeName.data z R B N L) (R*R) V q (succ p)
    (GaussianGammaZetaDegreeName.original_zeta_C18_rate z R B N L h)
  have symm := distance_symmetric _ _ _ _ (denominator_positive V q (succ p) vp) old
  have c : Γ ⊢[PRAAx] le (rateNumerator (R*R) V q (succ p)*(unit p*unit q))
      ((unit p+unit q)*rateDenominator V q (succ p)) := by
    have hm := degree_budget p R N h.andE₂.andE₁
    have ep := natEq (pw_succ (Γ := Γ) two p)
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hm using
      unfold rateNumerator rateDenominator unit
      ipra_simps
      rw [ep]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive V q (succ p) vp)
    (positive_product _ _ (unit_positive p) (unit_positive q)) c symm

def data (z R B N : PTm n) : PTm n := GaussianGammaCanonicalTailName.data z R B N
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2)
def sample (p z R B N : PTm n) : PTm n := ap2 nameF p (data z R B N)
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (data z R B N) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]
theorem observation_congr {p p' z z' R R' B B' N N' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R')
    (hB : Γ ⊢[PRAAx] B ≐ B') (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx]
    observation p z R B N ≐ observation p' z' R' B' N' := by
  ipra_congr (observation (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hp, hz, hR, hB, hN]
theorem sample_at (p z R B N : PTm n) : Γ ⊢[PRAAx] sample p z R B N ≐ observation p z R B N := by
  have raw := toPR_eq (Γ := Γ) (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2) ![p,data z R B N]
  have e : Γ ⊢[PRAAx] sample p z R B N ≐ observation p (fstT (data z R B N)) (fstT (sndT (data z R B N)))
      (fstT (sndT (sndT (data z R B N)))) (sndT (sndT (sndT (data z R B N)))) := by
    simpa only [sample,nameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using raw
  have t₁ := snd_pair (Γ := Γ) z (pairT R (pairT B N))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair R (pairT B N))
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrSnd t₂).eqTrans (snd_pair _ _)))
theorem sample_canonical (p z R B N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p z R B N) :=
  GaussianRationalHorner.canonical_congr (sample_at p z R B N) (GaussianGammaZetaDegreeName.sample_canonical _ _ _ _ _ _)
theorem sample_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (sample p z R B N) (R*R) N :=
  GaussianRationalReciprocal.bound_congr (sample_at p z R B N).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaZetaDegreeName.sample_bound _ _ _ _ _ _ h)

theorem original_C16_name_identity (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent nameF GaussianGammaCanonicalTailName.pointF (data z R B N)
      (GaussianGammaCanonicalTailName.data z R B N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr
    (sample_at (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N))).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (observation_error (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift N)) hs)
  simpa only [GaussianNameEquivalence.crossEquivalent,sample,point,Syn.shift,subst_data,GaussianGammaCanonicalTailName.subst_data,
    unit,GaussianEuclideanPointDistance.unit] using bound
theorem name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data z R B N) := by
  have he := original_C16_name_identity z R B N h
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ he (GaussianNameEquivalence.cross_symm _ _ _ _ he)

theorem actual_C16_degree_cutoff_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (var 1*var 1*unit (succ (var 0))) (GaussianGammaCofinalDegreeTail.rateDen (var 2) (cutoff (var 0) (var 1)))) :=
  closeUniv 3 (.impI (degree_budget _ _ _ Prf.hyp0))
theorem actual_C16_degree_cutoff_cofinal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (var 0) (cutoff (var 0) (var 1))) := closeUniv 2 (cutoff_cofinal _ _)
theorem actual_C16_zeta_series_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) ≐ observation (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (sample_at _ _ _ _ _)
theorem original_C16_zeta_series_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianNameEquivalence.crossEquivalent nameF GaussianGammaCanonicalTailName.pointF
      (data (var 0) (var 1) (var 2) (var 3)) (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_C16_name_identity _ _ _ _ Prf.hyp0))
theorem original_C16_zeta_series_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem original_K_two_R_C16_zeta_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      GaussianNameEquivalence.crossEquivalent nameF GaussianGammaCanonicalTailName.pointF
        (data (var 0) (var 1) (var 2) (two*var 1)) (GaussianGammaCanonicalTailName.data (var 0) (var 1) (var 2) (two*var 1))) :=
  closeUniv 3 (.impI (original_C16_name_identity _ _ _ _ (GaussianGammaCanonicalExponent.tail_source _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaTailSeries
