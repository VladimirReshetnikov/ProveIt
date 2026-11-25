import IPRADerivations.Analysis.GaussianBinetArctangentSineUniform
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Early truncation schedule for the second Binet formula

Choose the time horizon, geometric cutoff, and positive strip width
before the angular count or the shared π clock. Each truncation has
an explicit dyadic budget at the requested precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondEarlySchedule

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentSineUniform (cutoff count count_dominates)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def seed (D K : PTm n) : PTm n :=
  num 32+(num 64+num 8*K)+num 160*D*(num 5*K+one)+num 11*K+D

def height (p D K : PTm n) : PTm n := p+seed D K
def index (p D K : PTm n) : PTm n := height p D K+num 4
def timeHorizon (p D K : PTm n) : PTm n := unit (index p D K)
def kernelCutoff (p D K : PTm n) : PTm n := unit (num 4*index p D K)
def stripDenominator (p D K : PTm n) : PTm n := unit (num 8*index p D K)
def angularAccuracy (p D K : PTm n) : PTm n := succ (num 8*index p D K)
def frequencyCutoff (p D K : PTm n) : PTm n := cutoff (angularAccuracy p D K) (timeHorizon p D K) K
def frequencyHorizon (p D K : PTm n) : PTm n := D*frequencyCutoff p D K

@[simp] theorem subst_seed {m : ℕ} (σ : Fin n → PTm m) (D K : PTm n) :
    Syn.subst σ (seed D K) = seed (Syn.subst σ D) (Syn.subst σ K) := by simp [seed,one]

@[simp] theorem subst_height {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (height p D K) = height (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by simp [height]

@[simp] theorem subst_index {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (index p D K) = index (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by simp [index]

@[simp] theorem subst_timeHorizon {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (timeHorizon p D K) = timeHorizon (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [timeHorizon]

@[simp] theorem subst_kernelCutoff {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (kernelCutoff p D K) = kernelCutoff (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [kernelCutoff]

@[simp] theorem subst_stripDenominator {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (stripDenominator p D K) = stripDenominator (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [stripDenominator]

@[simp] theorem subst_angularAccuracy {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (angularAccuracy p D K) = angularAccuracy (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [angularAccuracy]

@[simp] theorem subst_frequencyCutoff {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (frequencyCutoff p D K) = frequencyCutoff (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [frequencyCutoff]

@[simp] theorem subst_frequencyHorizon {m : ℕ} (σ : Fin n → PTm m) (p D K : PTm n) :
    Syn.subst σ (frequencyHorizon p D K) = frequencyHorizon (Syn.subst σ p) (Syn.subst σ D) (Syn.subst σ K) := by
  simp [frequencyHorizon]

theorem seed_bounds (D K : PTm n) : Γ ⊢[PRAAx]
    le (num 64+num 8*K) (seed D K) ⋏
      (le (num 160*D*(num 5*K+one)) (seed D K) ⋏ (le (num 11*K) (seed D K) ⋏ le D (seed D K))) := by
  unfold seed
  refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
  · ipra_le 32+160*𝔞(D)*𝔞(num 5*K+one)+11*𝔞(K)+𝔞(D)
  · ipra_le 96+19*𝔞(K)+𝔞(D)
  · ipra_le 96+8*𝔞(K)+160*𝔞(D)*𝔞(num 5*K+one)+𝔞(D)
  · ipra_le 96+19*𝔞(K)+160*𝔞(D)*𝔞(num 5*K+one)

theorem seed_large (D K : PTm n) : Γ ⊢[PRAAx] le (num 32) (seed D K) :=
  le_trans (by ipra_le 32) (le_trans (le_add_right _ _) (seed_bounds D K).andE₁)

private theorem le_unit (x : PTm n) : Γ ⊢[PRAAx] le x (unit x) :=
  le_trans (le_succ_self x) (RationalClosure.succ_le_two_pow x)

private theorem seed_le_time (p D K : PTm n) : Γ ⊢[PRAAx] le (seed D K) (timeHorizon p D K) :=
  le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (le_unit _))

theorem observation_budget (p D K : PTm n) : Γ ⊢[PRAAx] le (unit p) (timeHorizon p D K) :=
  unit_monotone (le_trans (le_add_right p (seed D K)) (le_add_right (height p D K) (num 4)))

theorem double_strip (p D K : PTm n) :
    Γ ⊢[PRAAx] two*stripDenominator p D K ≐ unit (angularAccuracy p D K) :=
  ((pw_succ two (num 8*index p D K)).eqTrans (mul_comm _ _)).eqSymm

private theorem time_read (p D K : PTm n) :
    Γ ⊢[PRAAx] timeHorizon p D K ≐ num 16*unit (height p D K) := by
  have e : Γ ⊢[PRAAx] unit (num 4) ≐ num 16 := LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4
  exact (pw_add two (height p D K) (num 4)).eqTrans ((congrMul (.eqRefl _) e).eqTrans (mul_comm _ _))

private theorem time_dominates_index (p D K : PTm n) :
    Γ ⊢[PRAAx] le (num 15*index p D K) (timeHorizon p D K) := by
  let h := height p D K
  let v := index p D K
  have seedLarge : Γ ⊢[PRAAx] le (num 64 : PTm n) (seed D K) :=
    le_trans (le_add_right (num 64) (num 8*K)) (seed_bounds (Γ := Γ) D K).andE₁
  have lower : Γ ⊢[PRAAx] le (num 60 : PTm n) h :=
    le_trans (by ipra_le 4) (le_trans seedLarge (le_add_left _ _))
  have linear : Γ ⊢[PRAAx] le (num 15*v) (num 16*h) := by
    dsimp only [v,index]
    ipra_le sl lower
  exact le_trans linear (le_congr (mul_comm h _) ((mul_comm (unit h) _).eqTrans (time_read p D K).eqSymm)
    (mul_le_mul_right (num 16) (le_unit h)))

private theorem cutoff_after_angular (p D K : PTm n) :
    Γ ⊢[PRAAx] le (angularAccuracy p D K) (frequencyCutoff p D K) :=
  le_trans (le_add_right _ _) (le_succ_self _)

theorem frequency_cutoff_late (p D K : PTm n) :
    Γ ⊢[PRAAx] le p (frequencyCutoff p D K) := by
  let v := index p D K
  let q := angularAccuracy p D K
  have pq : Γ ⊢[PRAAx] le p v := le_trans (le_add_right p (seed D K)) (le_add_right _ _)
  have vq : Γ ⊢[PRAAx] le v q :=
    le_of_eq_add (d := num 7*v+one) (by dsimp only [q,angularAccuracy]; ipra_ring)
  exact le_trans (le_trans pq vq) (cutoff_after_angular p D K)

theorem frequency_horizon_bound (p D K : PTm n) : Γ ⊢[PRAAx]
    le (frequencyHorizon p D K) (D*(num 5*K+one)*timeHorizon p D K) := by
  let v := index p D K
  let T := timeHorizon p D K
  let q := angularAccuracy p D K
  let A := num 5*T*K
  let b := GaussianRootSchedule.binaryLength A
  have hv : Γ ⊢[PRAAx] le one v := le_trans (by ipra_le 3) (le_add_left (num 4) _)
  have hq : Γ ⊢[PRAAx] le (q+num 3) T := by
    apply le_trans ?_ (time_dominates_index p D K)
    dsimp only [q,angularAccuracy]
    ipra_le 7*sl hv+3
  have hb : Γ ⊢[PRAAx] le b A := (GaussianRootSchedule.binary_length_correct A).andE₂
  have left : Γ ⊢[PRAAx] frequencyCutoff p D K ≐ (q+num 3)+b := by
    dsimp only [frequencyCutoff,cutoff,GaussianFastValueCut.exponent,GaussianFastValueCut.normalizer]
    ipra_ring
  exact le_congr (congrMul (.eqRefl D) left.eqSymm) (by dsimp only [A]; ipra_ring)
    (le_mul_mono (le_refl D) (add_le_add₂ hq hb))

private theorem doubled_exponent (v : PTm n) : Γ ⊢[PRAAx] unit (two*v) ≐ unit v*unit v :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] two*v ≐ v+v) (.eqRefl two)).eqTrans (pw_add two v v)

theorem frequency_cutoff_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (D*unit p) (unit (frequencyCutoff p D K)) := by
  let v := index p D K
  have hD := le_trans (seed_bounds (Γ := Γ) D K).andE₂.andE₂.andE₂ (seed_le_time p D K)
  have low : Γ ⊢[PRAAx] le (two*v) (angularAccuracy p D K) :=
    le_of_eq_add (d := num 6*v+one) (by dsimp only [angularAccuracy,v]; ipra_ring)
  exact le_trans (le_congr (.eqRefl _) (doubled_exponent v).eqSymm
    (le_mul_mono hD (observation_budget p D K))) (unit_monotone (le_trans low (cutoff_after_angular p D K)))

private theorem kernel_read (p D K : PTm n) :
    Γ ⊢[PRAAx] kernelCutoff p D K ≐ (timeHorizon p D K*timeHorizon p D K)*(timeHorizon p D K*timeHorizon p D K) := by
  let v := index p D K
  have a : Γ ⊢[PRAAx] unit (num 4*v) ≐ unit (two*(two*v)) :=
    congrAp2 powF (by ipra_ring) (.eqRefl two)
  exact a.eqTrans ((doubled_exponent (two*v)).eqTrans (congrMul (doubled_exponent v) (doubled_exponent v)))

private theorem strip_read (p D K : PTm n) :
    Γ ⊢[PRAAx] stripDenominator p D K ≐ kernelCutoff p D K*kernelCutoff p D K := by
  let v := index p D K
  have a : Γ ⊢[PRAAx] unit (num 8*v) ≐ unit (two*(num 4*v)) :=
    congrAp2 powF (by ipra_ring) (.eqRefl two)
  exact a.eqTrans (doubled_exponent (num 4*v))

private theorem strip_product (p D K : PTm n) :
    let T := timeHorizon p D K
    let I := kernelCutoff p D K
    Γ ⊢[PRAAx] ((I*T)*(T*T))*T ≐ stripDenominator p D K := by
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  exact (by ipra_ring : Γ ⊢[PRAAx] ((I*T)*(T*T))*T ≐ I*((T*T)*(T*T))).eqTrans
    ((congrMul (.eqRefl I) (kernel_read p D K).eqSymm).eqTrans (strip_read p D K).eqSymm)

theorem atan_sum_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (two*kernelCutoff p D K*timeHorizon p D K*(num 24+num 4*K*timeHorizon p D K)*unit p)
      (unit (angularAccuracy p D K)) := by
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  let E := stripDenominator p D K
  have hT : Γ ⊢[PRAAx] le one T := unit_positive (index p D K)
  have coef : Γ ⊢[PRAAx] le (num 64+num 8*K) T :=
    le_trans (seed_bounds (Γ := Γ) D K).andE₁ (seed_le_time p D K)
  have a : Γ ⊢[PRAAx] le (two*(num 24+num 4*K*T)) (T*T) := by
    ipra_le 48*sl hT+16*𝔞(T)+𝔞(T)*sl coef
  have grow := le_mul_mono (le_mul_mono (le_refl (I*T)) a) (observation_budget (Γ := Γ) p D K)
  have useful : Γ ⊢[PRAAx] le (two*I*T*(num 24+num 4*K*T)*unit p) E :=
    le_congr (by ipra_ring) (strip_product p D K) grow
  exact le_trans useful (le_congr (.eqRefl E) (double_strip p D K)
    (le_of_eq_add (d := E) (by ipra_ring)))

theorem strip_sum_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (num 32*kernelCutoff p D K*timeHorizon p D K*(timeHorizon p D K+one)*unit p)
      (stripDenominator p D K) := by
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  have hT : Γ ⊢[PRAAx] le one T := unit_positive (index p D K)
  have coef : Γ ⊢[PRAAx] le (num 64 : PTm n) T :=
    le_trans (le_add_right _ _) (le_trans (seed_bounds (Γ := Γ) D K).andE₁ (seed_le_time p D K))
  have a : Γ ⊢[PRAAx] le (num 32*(T+one)) (T*T) := by
    ipra_le 32*sl hT+𝔞(T)*sl coef
  have grow := le_mul_mono (le_mul_mono (le_refl (I*T)) a) (observation_budget (Γ := Γ) p D K)
  exact le_congr (by ipra_ring) (strip_product p D K) grow

theorem sine_tail_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (num 160*stripDenominator p D K*kernelCutoff p D K*frequencyHorizon p D K*unit p)
      (unit (timeHorizon p D K)) := by
  let v := index p D K
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  let E := stripDenominator p D K
  have coef : Γ ⊢[PRAAx] le (num 160*D*(num 5*K+one)) T :=
    le_trans (seed_bounds (Γ := Γ) D K).andE₂.andE₁ (seed_le_time p D K)
  have a : Γ ⊢[PRAAx] le (num 160*frequencyHorizon p D K) (T*T) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_refl (num 160)) (frequency_horizon_bound (Γ := Γ) p D K)))
      (mul_le_mul_right T coef)
  have grow := le_mul_mono (le_mul_mono (le_refl (E*I)) a) (observation_budget (Γ := Γ) p D K)
  have three : Γ ⊢[PRAAx] (T*T)*T ≐ unit (num 3*v) :=
    ((congrMul (pw_add two v v).eqSymm (.eqRefl T)).eqTrans (pw_add two (v+v) v).eqSymm).eqTrans
      (congrAp2 powF (by ipra_ring) (.eqRefl two))
  have join : Γ ⊢[PRAAx] ((E*I)*(T*T))*T ≐ unit (num 15*v) :=
    (by ipra_ring : Γ ⊢[PRAAx] ((E*I)*(T*T))*T ≐ (E*I)*((T*T)*T)).eqTrans
      ((congrMul (pw_add two (num 8*v) (num 4*v)).eqSymm three).eqTrans
        ((pw_add two (num 8*v+num 4*v) (num 3*v)).eqSymm.eqTrans
          (congrAp2 powF (by ipra_ring) (.eqRefl two))))
  exact le_trans (le_congr (by ipra_ring) join grow) (unit_monotone (time_dominates_index p D K))

theorem kernel_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (two*frequencyHorizon p D K*unit p) (kernelCutoff p D K) := by
  let T := timeHorizon p D K
  have hT := unit_positive (Γ := Γ) (index p D K)
  have coef : Γ ⊢[PRAAx] le (num 160*D*(num 5*K+one)) T :=
    le_trans (seed_bounds (Γ := Γ) D K).andE₂.andE₁ (seed_le_time p D K)
  have c : Γ ⊢[PRAAx] le (two*D*(num 5*K+one)) T := by
    ipra_le 158*𝔞(D)*𝔞(num 5*K+one)+sl coef
  have a : Γ ⊢[PRAAx] le (two*frequencyHorizon p D K) (T*T) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_refl two) (frequency_horizon_bound (Γ := Γ) p D K)))
      (mul_le_mul_right T c)
  have grow := le_mul_mono a (observation_budget (Γ := Γ) p D K)
  have again : Γ ⊢[PRAAx] le T (T*T) :=
    le_congr (one_mul T) (.eqRefl _) (mul_le_mul_right T hT)
  exact le_trans grow (le_congr (.eqRefl _) (kernel_read p D K).eqSymm (le_mul_mono (le_refl (T*T)) again))

theorem bose_tail_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (num 11*K*unit p) (kernelCutoff p D K) := by
  let T := timeHorizon p D K
  have hT := unit_positive (Γ := Γ) (index p D K)
  have coef : Γ ⊢[PRAAx] le (num 11*K) T :=
    le_trans (seed_bounds (Γ := Γ) D K).andE₂.andE₂.andE₁ (seed_le_time p D K)
  have grow := le_mul_mono coef (observation_budget (Γ := Γ) p D K)
  have hTT := positive_product _ _ hT hT
  exact le_trans grow (le_congr (one_mul (T*T)) (kernel_read p D K).eqSymm (mul_le_mul_right (T*T) hTT))

theorem restored_origin_budget (p D K : PTm n) :
    Γ ⊢[PRAAx] le (two*K*kernelCutoff p D K*unit p) (stripDenominator p D K*stripDenominator p D K) := by
  let T := timeHorizon p D K
  let I := kernelCutoff p D K
  let E := stripDenominator p D K
  have hT : Γ ⊢[PRAAx] le one T := unit_positive (index p D K)
  have hE : Γ ⊢[PRAAx] le one E := unit_positive (num 8*index p D K)
  have hTT := positive_product _ _ hT hT
  have coef : Γ ⊢[PRAAx] le (num 64+num 8*K) T :=
    le_trans (seed_bounds (Γ := Γ) D K).andE₁ (seed_le_time p D K)
  have twice : Γ ⊢[PRAAx] le (two*K) T := by ipra_le 64+6*𝔞(K)+sl coef
  have major := le_mul_mono twice (observation_budget p D K)
  have pad := le_congr (one_mul (T*T)) (kernel_read p D K).eqSymm (mul_le_mul_right (T*T) hTT)
  have first : Γ ⊢[PRAAx] le (two*K*I*unit p) E :=
    le_congr (by ipra_ring) (strip_read p D K).eqSymm (mul_le_mul_right I (le_trans major pad))
  exact le_trans first (le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E hE))

/-- Increasing the radius admits the same parameter and forces the
computed angular count to dominate any prescribed lower bound. -/
theorem angular_count_at_least (q X Y D sign R T K C : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] source X Y D sign (R+C) ⋏ le C (count q D (R+C) T K) := by
  have width := positive_product _ _ h.andE₁.andE₂
    (GaussianBinetArctangentSineUniform.cutoff_positive q T K)
  have growth := sq_le_sq (mul_le_mul_right D (le_add_right (Γ := Γ) R C))
  have enlarged : Γ ⊢[PRAAx] source X Y D sign (R+C) :=
    .andI h.andE₁ (le_trans h.andE₂ growth)
  have lower : Γ ⊢[PRAAx] le C (R+C+T) := le_trans (le_add_left C R) (le_add_right _ _)
  have toward := le_congr (one_mul C) (.eqRefl _) (le_mul_mono width lower)
  exact .andI enlarged (le_trans (le_congr (.eqRefl _) (mul_comm _ _) toward) (count_dominates q D (R+C) T K).andE₁)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondEarlySchedule
