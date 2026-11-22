import IPRADerivations.Analysis.GaussianGammaEulerConvergence

/-!
# A primitive-recursive C10 cutoff for the folded Euler approximants

The original folded Q program is sampled one bit later. The numerical
cutoff makes the original C10 error at most that same later dyadic unit.
The actual cofinal sampler therefore agrees with the original reciprocal
name at independent precisions and is itself regular.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerApproximationName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaPerturbationExponent (numerator)
open GaussianGammaC9Bound (majorant)
open GaussianNamedSmallPerturbationTransport (budgetNumerator budgetDenominator denominator_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rate (R : PTm n) : PTm n := num 3*majorant R*numerator R
def cutoff (p R : PTm n) : PTm n := two*R+numerator R+rate R*unit (succ p)
def observation (p z R B : PTm n) : PTm n := ap2 qF (succ p) (qData z B (cutoff p R))

@[simp] theorem subst_rate {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (rate R) = rate (Syn.subst σ R) := by simp [rate]
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (p R : PTm n) :
    Syn.subst σ (cutoff p R) = cutoff (Syn.subst σ p) (Syn.subst σ R) := by simp [cutoff, unit]
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (observation p z R B) = observation (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [observation, qData, GaussianGammaFiniteApproximantName.approximantData,
    GaussianGammaFiniteApproximantName.exponentialInputData]
  have head := GaussianGammaCutoffName.subst_head σ z B (cutoff p R)
  simp only [GaussianGammaCutoffName.head, subst_cutoff] at head
  rw [head]

theorem cutoff_guards (p R : PTm n) : Γ ⊢[PRAAx]
    le (two*R) (cutoff p R) ⋏ (le (numerator R) (cutoff p R) ⋏ le (rate R*unit (succ p)) (cutoff p R)) := by
  unfold cutoff
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_le 𝔞 (numerator R)+𝔞 (rate R*unit (succ p))
  · ipra_le 2*𝔞 R+𝔞 (rate R*unit (succ p))
  · ipra_le 2*𝔞 R+𝔞 (numerator R)

theorem observation_error (p q z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] distanceBounded (observation p z R B) (GaussianGammaC7Name.sample q z R B)
      (unit p+unit q) (unit p*unit q) := by
  let N := cutoff p R
  have hg := cutoff_guards (Γ := Γ) p R
  have hs : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N := .andI h (.andI hg.andE₁ hg.andE₂.andE₁)
  have hn := (GaussianGammaEulerConvergence.local_source z R B N hs).andE₂.andE₁
  have c : Γ ⊢[PRAAx] le (budgetNumerator (succ p) q (numerator R) N (majorant R)*(unit p*unit q))
      ((unit p+unit q)*budgetDenominator (succ p) q N) := by
    have e := natEq (pw_succ (Γ := Γ) two p)
    have hm := hg.andE₂.andE₂
    ipra_le 𝔞 (unit p)*𝔞 (unit q)*𝔞 (unit q)*sl hm using
      unfold budgetNumerator budgetDenominator rate unit
      ipra_simps
      rw [e]
      ring
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive (succ p) q N hn)
    (positive_product _ _ (unit_positive p) (unit_positive q)) c
    (GaussianGammaEulerConvergence.observation_error (succ p) q z R B N hs)

def data (z R B : PTm n) : PTm n := pairT z (pairT R B)
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2)
def sample (p z R B : PTm n) : PTm n := ap2 nameF p (data z R B)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (data z R B) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [data]

theorem observation_congr {p p' z z' R R' B B' : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ p') (hz : Γ ⊢[PRAAx] z ≐ z') (hR : Γ ⊢[PRAAx] R ≐ R') (hB : Γ ⊢[PRAAx] B ≐ B') :
    Γ ⊢[PRAAx] observation p z R B ≐ observation p' z' R' B' := by
  simpa only [subst_observation, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (observation (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,z,R,B]) (σ' := ![p',z',R',B'])
      (fun i => by fin_cases i; exact hp; exact hz; exact hR; exact hB)

theorem sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] sample p z R B ≐ observation p z R B := by
  have raw := toPR_eq (Γ := Γ)
    (observation (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) : PTm 2) ![p,data z R B]
  have e : Γ ⊢[PRAAx] sample p z R B ≐
      observation p (fstT (data z R B)) (fstT (sndT (data z R B))) (sndT (sndT (data z R B))) := by
    simpa only [sample, nameF, ap2, subst_observation, subst_fstT, subst_sndT, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using raw
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
  have bound := distance_congr (sample_at (var 1) z' R' B').eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (observation_error (var 1) (var 0) z' R' B' hs)
  simpa only [crossEquivalent, sample, GaussianGammaC7Name.sample, Syn.shift, subst_data,
    GaussianGammaC7Name.subst_data, unit, GaussianEuclideanPointDistance.unit, z',R',B'] using bound

theorem name_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B) := by
  have e := named_equivalence z R B h
  exact cross_trans _ _ _ _ _ _ e (cross_symm _ _ _ _ e)

theorem actual_euler_cutoff_schedule_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (two*(var 1)) (cutoff (var 0) (var 1)) ⋏
      (le (numerator (var 1)) (cutoff (var 0) (var 1)) ⋏
        le (rate (var 1)*unit (succ (var 0))) (cutoff (var 0) (var 1)))) :=
  closeUniv 2 (cutoff_guards _ _)

theorem actual_euler_cofinal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (var 0) (var 1) (var 2) (var 3) ≐ observation (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (sample_at _ _ _ _)

theorem original_euler_cofinal_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶
      crossEquivalent nameF GaussianGammaC7Name.nameF (data (var 0) (var 1) (var 2))
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (named_equivalence _ _ _ Prf.hyp0))

theorem original_euler_cofinal_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerApproximationName
