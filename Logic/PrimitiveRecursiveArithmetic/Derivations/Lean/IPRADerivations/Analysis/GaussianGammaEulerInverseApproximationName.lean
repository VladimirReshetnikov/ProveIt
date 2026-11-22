import IPRADerivations.Analysis.GaussianGammaEulerInverseConvergence
import IPRADerivations.Core.Gcd

/-!
# A cofinal sampler of the original Euler Gamma reciprocals

The exact C15 numerator C and denominator scale S determine
N_p=2R+(R²+R)+p+1+floor(C*2^(p+1)/S).
Thus the actual cutoff is cofinal, meets the original two cutoff guards,
and retains the exact fractional rate in its division. Sampling the
original named reciprocal of Q_(N_p) at p+1 gives an actual regular PR2
name cross-equivalent to the original Gamma name at independent precisions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerInverseApproximationName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaReciprocalInverse (source lambdaNumerator gammaF gammaData)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaPerturbationExponent (numerator)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rateScale (R a : PTm n) : PTm n := lambdaNumerator R a*lambdaNumerator R a
def cutoff (p R a d : PTm n) : PTm n := two*R+numerator R+p+
  succ (quo (coefficientNumerator R d*unit (succ p)) (rateScale R a))
def observation (p z R B a d : PTm n) : PTm n :=
  ap2 eulerF (succ p) (eulerData z R B d (cutoff p R a d))

@[simp] theorem subst_rateScale {m : ℕ} (σ : Fin n → PTm m) (R a : PTm n) :
    Syn.subst σ (rateScale R a) = rateScale (Syn.subst σ R) (Syn.subst σ a) := by simp [rateScale]
@[simp] theorem subst_cutoff {m : ℕ} (σ : Fin n → PTm m) (p R a d : PTm n) :
    Syn.subst σ (cutoff p R a d) = cutoff (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [cutoff,unit]
@[simp] theorem subst_eulerData {m : ℕ} (σ : Fin n → PTm m) (z R B d N : PTm n) :
    Syn.subst σ (eulerData z R B d N) = eulerData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) (Syn.subst σ N) := by
  simp [eulerData,GaussianGammaEulerReciprocalInverse.eulerHeight]
@[simp] theorem subst_gammaData {m : ℕ} (σ : Fin n → PTm m) (z R B d : PTm n) :
    Syn.subst σ (gammaData z R B d) = gammaData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [gammaData,GaussianGammaReciprocalInverse.gammaHeight]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (p z R B a d : PTm n) :
    Syn.subst σ (observation p z R B a d) = observation (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ d) := by simp [observation]

theorem quotient_successor_cap (X S : PTm n) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] le X (S*succ (quo X S)) := by
  have ps : Γ ⊢[PRAAx] S ≐ succ (pred S) := by
    refine .orE (zero_or_succ S) ?_ Prf.hyp0
    exact lt_zero_absurd _ (le_congr (.eqRefl _) Prf.hyp0 hS.wk)
  have dm := div_mod_at (x := X) ps
  have e := natEq dm.andE₁
  ipra_le 1+sl dm.andE₂ using
    rw [e]
    ring

theorem cutoff_guards (p R a d : PTm n) : Γ ⊢[PRAAx]
    le (two*R) (cutoff p R a d) ⋏ (le (numerator R) (cutoff p R a d) ⋏ le p (cutoff p R a d)) := by
  unfold cutoff
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_le 𝔞 (numerator R)+𝔞 p+𝔞 (succ (quo (coefficientNumerator R d*unit (succ p)) (rateScale R a)))
  · ipra_le 2*𝔞 R+𝔞 p+𝔞 (succ (quo (coefficientNumerator R d*unit (succ p)) (rateScale R a)))
  · ipra_le 2*𝔞 R+𝔞 (numerator R)+𝔞 (succ (quo (coefficientNumerator R d*unit (succ p)) (rateScale R a)))

theorem cutoff_threshold (p R a d : PTm n) (ha : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx]
    le (coefficientNumerator R d*unit (succ p)) (rateScale R a*cutoff p R a d) := by
  have lp : Γ ⊢[PRAAx] le one (lambdaNumerator R a) := GaussianFactorBudget.power_positive _ _ ha
  have cap := quotient_successor_cap (Γ := Γ) (coefficientNumerator R d*unit (succ p)) (rateScale R a)
    (positive_product _ _ lp lp)
  have step : Γ ⊢[PRAAx] le (succ (quo (coefficientNumerator R d*unit (succ p)) (rateScale R a))) (cutoff p R a d) := by
    unfold cutoff
    ipra_le 2*𝔞 R+𝔞 (numerator R)+𝔞 p
  exact le_trans cap (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) step)

theorem observation_error (p q z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B a d) (ap2 gammaF q (gammaData z R B d))
      (unit p+unit q) (unit p*unit q) := by
  let N := cutoff p R a d
  have hg := cutoff_guards (Γ := Γ) p R a d
  have hs : Γ ⊢[PRAAx] GaussianGammaEulerInverseConvergence.source z R B a d N := .andI h (.andI hg.andE₁ hg.andE₂.andE₁)
  have pos := GaussianGammaEulerInverseConvergence.coefficient_denominator_positive z R B a d N hs
  have c : Γ ⊢[PRAAx]
      le (rateNumerator (coefficientNumerator R d) (coefficientDenominator R a N) (succ p) q*(unit p*unit q))
        ((unit p+unit q)*rateDenominator (coefficientDenominator R a N) (succ p) q) := by
    have e := natEq (pw_succ (Γ := Γ) two p)
    have hm := cutoff_threshold (Γ := Γ) p R a d h.andE₂.andE₁
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hm using
      unfold rateNumerator rateDenominator coefficientDenominator rateScale unit
      ipra_simps
      rw [e]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive _ (succ p) q pos)
    (positive_product _ _ (unit_positive p) (unit_positive q)) c
    (GaussianGammaEulerInverseConvergence.actual_observation_error (succ p) q z R B a d N hs)

def data (z R B a d : PTm n) : PTm n := pairT z (pairT R (pairT B (pairT a d)))
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
def sample (p z R B a d : PTm n) : PTm n := ap2 nameF p (data z R B a d)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B a d : PTm n) :
    Syn.subst σ (data z R B a d) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ d) := by
  simp [data]

theorem observation_congr {p p' z z' R R' B B' a a' d d' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R')
    (hB : Γ ⊢[PRAAx] B ≐ B') (ha : Γ ⊢[PRAAx] a ≐ a') (hd : Γ ⊢[PRAAx] d ≐ d') : Γ ⊢[PRAAx]
    observation p z R B a d ≐ observation p' z' R' B' a' d' := by
  have e5 : (![p,z,R,B,a,d] : Fin 6 → PTm n) 5 = d := rfl
  have e5' : (![p',z',R',B',a',d'] : Fin 6 → PTm n) 5 = d' := rfl
  simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,e5,e5',Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,z,R,B,a,d]) (σ' := ![p',z',R',B',a',d'])
      (fun i => by fin_cases i; exact hp; exact hz; exact hR; exact hB; exact ha; exact hd)

theorem sample_at (p z R B a d : PTm n) : Γ ⊢[PRAAx] sample p z R B a d ≐ observation p z R B a d := by
  have raw := toPR_eq (Γ := Γ) (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
    (fstT (sndT (sndT (var 1)))) (fstT (sndT (sndT (sndT (var 1))))) (sndT (sndT (sndT (sndT (var 1))))) : PTm 2)
    ![p,data z R B a d]
  have e : Γ ⊢[PRAAx] sample p z R B a d ≐ observation p (fstT (data z R B a d)) (fstT (sndT (data z R B a d)))
      (fstT (sndT (sndT (data z R B a d)))) (fstT (sndT (sndT (sndT (data z R B a d)))))
      (sndT (sndT (sndT (sndT (data z R B a d))))) := by
    simpa only [sample,nameF,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using raw
  have t₁ := snd_pair (Γ := Γ) z (pairT R (pairT B (pairT a d)))
  have t₂ := (congrSnd t₁).eqTrans (snd_pair R (pairT B (pairT a d)))
  have t₃ := (congrSnd t₂).eqTrans (snd_pair B (pairT a d))
  exact e.eqTrans (observation_congr (.eqRefl _) (fst_pair _ _) ((congrFst t₁).eqTrans (fst_pair _ _))
    ((congrFst t₂).eqTrans (fst_pair _ _)) ((congrFst t₃).eqTrans (fst_pair _ _)) ((congrSnd t₃).eqTrans (snd_pair _ _)))

theorem sample_canonical (p z R B a d : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample p z R B a d) :=
  GaussianRationalHorner.canonical_congr (sample_at p z R B a d)
    (GaussianNameReciprocal.name_canonical _ _ _ _)

theorem named_equivalence (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    crossEquivalent nameF gammaF (data z R B a d) (gammaData z R B d) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift d)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have bound := distance_congr
    (sample_at (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift d))).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (observation_error (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B))
      (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift d)) hs)
  simpa only [crossEquivalent,sample,Syn.shift,subst_data,subst_gammaData,unit,GaussianEuclideanPointDistance.unit] using bound

theorem name_regular (z R B a d : PTm n) (h : Γ ⊢[PRAAx] source z R B a d) : Γ ⊢[PRAAx]
    pointCN nameF (data z R B a d) := by
  have e := named_equivalence z R B a d h
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem actual_Gamma_euler_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (coefficientNumerator (var 1) (var 3)*unit (succ (var 0)))
      (rateScale (var 1) (var 2)*cutoff (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (cutoff_threshold _ _ _ _ Prf.hyp0))
theorem actual_Gamma_euler_cofinality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 0) (cutoff (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (cutoff_guards _ _ _ _).andE₂.andE₂
theorem actual_Gamma_euler_cofinal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ observation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (sample_at _ _ _ _ _ _)
theorem original_Gamma_euler_cofinal_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent nameF gammaF (data (var 0) (var 1) (var 2) (var 3) (var 4))
        (gammaData (var 0) (var 1) (var 2) (var 4))) := closeUniv 5 (.impI (named_equivalence _ _ _ _ _ Prf.hyp0))
theorem original_Gamma_euler_cofinal_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (name_regular _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerInverseApproximationName
