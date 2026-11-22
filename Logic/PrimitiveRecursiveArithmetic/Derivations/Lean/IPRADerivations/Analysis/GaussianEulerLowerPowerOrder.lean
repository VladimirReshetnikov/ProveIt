import IPRADerivations.Analysis.GaussianEulerLowerPowerCoefficients
import IPRADerivations.Analysis.GaussianEulerUpperPowerOrder
import IPRADerivations.Analysis.GaussianBoundedConstantProductName

/-!
# Same-clock signed-real exponential comparison below time one

Both actual exponent input names multiply the same ordered harmonic-log
observation at the same supplied numerical clock. The original native
input disk therefore yields exponential order without an assumed
logarithm sign or an output-order premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerCoefficients (realMultiplier)
open GaussianEulerLowerPowerCoefficients (lowerMultiplier amplification)
open GaussianRationalHorner (qmul)
open ComplexLogarithmRemainder (oneCode)
open GaussianRationalMetric (bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open GaussianSignedNameExponentialOrder (realSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev logarithmF : PR 2 := GaussianHarmonicLogarithmName.nameF
abbrev inputF : PR 2 := GaussianBoundedConstantProductName.nameF logarithmF
abbrev expF : PR 2 := GaussianRadiusExponentialName.nameF inputF

def source (z R B A a b : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏
    (GaussianPositiveRationalLogarithm.source a b ⋏ le a b)
def leftData (z R B a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b)
def rightData (R A a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) (lowerMultiplier A) (GaussianHarmonicLogarithmName.data a b)
def radius (R b : PTm n) : PTm n := amplification R*GaussianHarmonicLogarithmName.radius b one
def leftExpData (z R B a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R b) (leftData z R B a b)
def rightExpData (R A a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R b) (rightData R A a b)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A a b : PTm n) :
    (source z R B A a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [source]
@[simp] theorem subst_leftData {m : ℕ} (σ : Fin n → PTm m) (z R B a b : PTm n) :
    Syn.subst σ (leftData z R B a b) = leftData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [leftData]
@[simp] theorem subst_rightData {m : ℕ} (σ : Fin n → PTm m) (R A a b : PTm n) :
    Syn.subst σ (rightData R A a b) = rightData (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [rightData]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (R b : PTm n) :
    Syn.subst σ (radius R b) = radius (Syn.subst σ R) (Syn.subst σ b) := by simp [radius]
@[simp] theorem subst_leftExpData {m : ℕ} (σ : Fin n → PTm m) (z R B a b : PTm n) :
    Syn.subst σ (leftExpData z R B a b) = leftExpData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [leftExpData]
@[simp] theorem subst_rightExpData {m : ℕ} (σ : Fin n → PTm m) (R A a b : PTm n) :
    Syn.subst σ (rightExpData R A a b) = rightExpData (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [rightExpData]

theorem actual_time_domain (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le a b) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain a b b one :=
  .andI h.andE₁ (.andI
    (le_congr (by ipra_ring) (.eqRefl _) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl b) h.andE₁.andE₁))
    (le_congr (.eqRefl _) (one_mul _).eqSymm h.andE₂))

theorem product_input (M c a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le a b)
    (hc : Γ ⊢[PRAAx] bounded c M one) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input inputF (M*GaussianHarmonicLogarithmName.radius b one)
      (GaussianBoundedConstantProductName.data M c (GaussianHarmonicLogarithmName.data a b)) := by
  refine .andI (GaussianBoundedConstantProductName.name_regular logarithmF M c _
    (.andI (GaussianHarmonicLogarithmName.name_regular a b h.andE₁) hc)) (.allI ?_)
  have ts : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (Syn.shift a) (Syn.shift b) ⋏ le (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift c) (Syn.shift M) one := by simpa [Fm.shift,Syn.shift] using hc.shift
  have hs := GaussianHarmonicLogarithmName.compact_sample_bound
    (GaussianBoundedConstantProductName.clock (var 0) (Syn.shift M)) (Syn.shift a) (Syn.shift b) (Syn.shift b) one
    ts.andE₁.andE₂ (actual_time_domain _ _ ts)
  have hb := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) cs hs
  have e := GaussianBoundedConstantProductName.sample_at (Γ := Γ.map Fm.shift) logarithmF (var 0) (Syn.shift M) (Syn.shift c) (GaussianHarmonicLogarithmName.data (Syn.shift a) (Syn.shift b))
  simpa [GaussianRadiusExponentialName.boundedSamples,Syn.shift,GaussianBoundedConstantProductName.sample] using
    GaussianRationalReciprocal.bound_congr e.eqSymm (.eqRefl _) (one_mul _) hb

theorem sample_order_at (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 inputF p (leftData z R B a b))) (fstT (ap2 inputF p (rightData R A a b))) := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let l := GaussianHarmonicLogarithmName.sample s a b
  have hr := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) s a b).andE₂
  have order := RationalArithmetic.multiply_antitone (fstT l) (fstT (lowerMultiplier A)) (fstT (realMultiplier z B))
    (GaussianEulerLowerPowerCoefficients.harmonic_sample_nonpositive s a b h.andE₂.andE₂)
    (GaussianEulerLowerPowerCoefficients.multiplier_lower z R B A h.andE₁)
  have left := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) logarithmF p (amplification R) (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have right := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) logarithmF p (amplification R) (lowerMultiplier A) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  exact RationalArgmin.rationalLE_congr left.eqSymm right.eqSymm order

theorem sample_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    sampleOrder inputF inputF (leftData z R B a b) (rightData R A a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleOrder,Syn.shift,subst_leftData,subst_rightData] using
    sample_order_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs

theorem ordered_exponentials (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    realOrder expF expF (leftExpData z R B a b) (rightExpData R A a b) :=
  GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF (radius R b) _ _
    (product_input _ _ _ _ h.andE₂ (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁))
    (product_input _ _ _ _ h.andE₂ (GaussianEulerLowerPowerCoefficients.lower_multiplier_bound R A h.andE₁.andE₁))
    (GaussianEulerUpperPowerOrder.product_real_samples _ _ _ _ (GaussianEulerUpperPowerCoefficients.real_multiplier_axis z B))
    (GaussianEulerUpperPowerOrder.product_real_samples _ _ _ _ (GaussianEulerUpperPowerCoefficients.real_multiplier_axis oneCode A))
    (sample_order z R B A a b h)

theorem actual_lower_time_ordered_exponentials_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      realOrder expF expF (leftExpData (var 0) (var 1) (var 2) (var 4) (var 5)) (rightExpData (var 1) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (ordered_exponentials _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerPowerOrder
