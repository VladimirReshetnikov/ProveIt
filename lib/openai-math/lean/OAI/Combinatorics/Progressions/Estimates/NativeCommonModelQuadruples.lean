/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import OAI.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates

namespace OAI

section

namespace Erdos3

open scoped TensorProduct Pointwise

structure NativeCyclicModel (degree N : ℕ) [NeZero N] (p : ℝ) (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  test : model.Niltest (fun _ : Unit => 1)
  norm : test.normBound ≤ 1
  complexity : test.ComplexityLE p
  eval : ∀ x, f x = test.evalCyclic N (fun _ => x)

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

noncomputable def NativeCyclicModel.smul {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (F : NativeCyclicModel degree N p f) (c : ℂ) (hc : ‖c‖ ≤ 1) :
    NativeCyclicModel degree N p (c • f) where
  L := F.L
  dim := F.dim
  model := F.model
  test := F.test.scaleComplex c
  norm := (F.test.scaleComplex_norm hc).trans F.norm
  complexity := F.test.scaleComplex_complexity hc F.complexity
  eval x := by
    change c * f x = c * F.test.evalCyclic N (fun _ => x)
    rw [F.eval x]

def nativeCyclicFunctions (degree N : ℕ) [NeZero N] (p : ℝ) : Set (ZMod N → ℂ) :=
  {f | Nonempty (NativeCyclicModel degree N p f)}

theorem nativeCyclicFunctions_balanced (degree N : ℕ) [NeZero N] (p : ℝ) :
    Balanced ℂ (nativeCyclicFunctions degree N p) := by
  rintro c hc _ ⟨f, ⟨F⟩, rfl⟩
  exact ⟨F.smul c hc⟩

theorem nativeCyclicFunctions_norm {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (hf : f ∈ nativeCyclicFunctions degree N p) (x : ZMod N) : ‖f x‖ ≤ 1 := by
  obtain ⟨F⟩ := hf
  rw [F.eval x]
  exact (F.test.norm_evalCyclic_le N (fun _ => x)).trans F.norm

theorem nativeCyclicFunctions_zero {degree N : ℕ} [NeZero N] (hdegree : 1 ≤ degree)
    {p : ℝ} (hp : 2 ≤ p) : (0 : ZMod N → ℂ) ∈ nativeCyclicFunctions degree N p := by
  let D := (RationalTorus.nilmanifold 0).raiseStep hdegree
  have hgeom : D.GeometryComplexityLE p :=
    (RationalTorus.nilmanifold 0).raiseStep_geometry hdegree
      (RationalTorus.nilmanifold_geometry 0 (by linarith) (by norm_num; linarith))
  refine ⟨{
    L := RationalTorus.Algebra 0
    dim := 0
    model := D
    test := RationalFilteredNilmanifold.Niltest.const D (fun _ : Unit => 1) 0
    norm := by simp [RationalFilteredNilmanifold.Niltest.const]
    complexity := ⟨hgeom, ?_⟩
    eval := fun _ => rfl }⟩
  change Real.log (2 + (‖(0 : ℂ)‖₊ : ℝ) + (0 : ℝ)) ≤ p
  simp only [nnnorm_zero, NNReal.coe_zero, add_zero]
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicNativeInverse (s C : ℕ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {p : ℝ}, 2 ≤ p → ∀ f : ZMod N → ℂ,
    (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 1) f →
    ∃ g ∈ nativeCyclicFunctions s N ((p + C) ^ C),
      Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x, f x * star (g x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeCommonDerivativeModels (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℂ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L degree dim
  geometry : model.GeometryComplexityLE p
  shifts : Finset (ZMod N)
  nonempty : shifts.Nonempty
  density : Real.exp (-p) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  test : ZMod N → model.Niltest (fun _ : Unit => 1)
  norm : ∀ h, (test h).normBound ≤ 1
  complexity : ∀ h, (test h).ComplexityLE p
  common_observable : ∀ h k, (test h).observable = (test k).observable
  correlation : ∀ h ∈ shifts, Real.exp (-p) ≤
    ‖𝔼 x, multiplicativeDerivative f h x * star ((test h).evalCyclic N (fun _ => x))‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_cyclic_model_of_detector {degree N : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) {p : ℝ} (hp : 2 ≤ p)
    (X : Seminorm ℂ (ZMod N → ℂ)) {K M beta tau : ℝ}
    (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : ZMod N → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ f ∈ nativeCyclicFunctions degree N p, beta ≤ ‖𝔼 x, psi x * star (f x)‖)
    (b : ZMod N → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (f : Fin n → ZMod N → ℂ)
      (F : ∀ i, NativeCyclicModel degree N p (f i))
      (c : Fin n → ℂ) (e : ZMod N → ℂ),
      (∀ x, b x = (∑ i, c i * (F i).test.evalCyclic N (fun _ => x)) + e x) ∧
      (∑ i, ‖c i‖) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  classical
  obtain ⟨n, hn, f, c, e, hf, heq, hcost, herr, hcount⟩ :=
    exists_uniform_model_of_detector X (nativeCyclicFunctions_balanced degree N p)
      ⟨0, nativeCyclicFunctions_zero hdegree hp⟩
      (fun _ hf x => nativeCyclicFunctions_norm hf x) hK hM hbeta htau hX hdetect b hb
  let F (i : Fin n) : NativeCyclicModel degree N p (f i) := Classical.choice (hf i)
  refine ⟨n, hn, f, F, (fun i => (c i : ℂ)), e, ?_, ?_, herr, hcount⟩
  · intro x
    have hx := congrFun heq x
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Complex.real_smul,
      fun i => (F i).eval x] using hx
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hcost

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

def NativeModelDetector (degree N : ℕ) [NeZero N] (p : ℝ)
    (X : Seminorm ℂ (ZMod N → ℂ)) (K M beta tau : ℝ) : Prop :=
  ∀ psi : ZMod N → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
    ∃ f ∈ nativeCyclicFunctions degree N p, beta ≤ ‖𝔼 x, psi x * star (f x)‖

def NativeTwoSiteModelingData (degree N : ℕ) [NeZero N]
    (p₁ p₂ K₁ K₂ beta₁ beta₂ eta : ℝ)
    (X₁ : Seminorm ℂ (ZMod N → ℂ))
    (X₂ : (ZMod N → ℂ) → Seminorm ℂ (ZMod N → ℂ)) (a b : ZMod N → ℂ) : Prop :=
  let tau₁ := eta / 4
  let tau₂ := eta * beta₁ / 8
  let length₁ := 1 + 4 * K₁ ^ 2 / (beta₁ ^ 2 * tau₁ ^ 2)
  let length₂ := 1 + 4 * K₂ ^ 2 / (beta₂ ^ 2 * tau₂ ^ 2)
  ∃ (n : ℕ) (_ : 0 < n) (f : Fin n → ZMod N → ℂ)
    (F : ∀ i, NativeCyclicModel degree N p₁ (f i))
    (c : Fin n → ℂ) (ea : ZMod N → ℂ)
    (m : Fin n → ℕ) (_ : ∀ i, 0 < m i)
    (g : ∀ i, Fin (m i) → ZMod N → ℂ)
    (G : ∀ i j, NativeCyclicModel degree N p₂ (g i j))
    (d : ∀ i, Fin (m i) → ℂ) (eb : Fin n → ZMod N → ℂ),
    (∀ x, a x = (∑ i, c i * (F i).test.evalCyclic N (fun _ => x)) + ea x) ∧
    (∀ i x, b x = (∑ j, d i j * (G i j).test.evalCyclic N (fun _ => x)) + eb i x) ∧
    (∑ i, ‖c i‖) ≤ 2 / beta₁ ∧ (∀ i, (∑ j, ‖d i j‖) ≤ 2 / beta₂) ∧
    X₁ ea + ∑ i, ‖c i‖ * X₂ (f i) (eb i) ≤ eta ∧
    (n : ℝ) ≤ length₁ ∧ (∀ i, (m i : ℝ) ≤ length₂) ∧
    (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ length₁ * length₂

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_two_site_models {degree N : ℕ} [NeZero N]
    (hdegree : 1 ≤ degree) {p₁ p₂ : ℝ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂)
    (X₁ : Seminorm ℂ (ZMod N → ℂ))
    (X₂ : (ZMod N → ℂ) → Seminorm ℂ (ZMod N → ℂ))
    {K₁ K₂ M₁ M₂ beta₁ beta₂ eta : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hbeta₁ : 0 < beta₁) (hbeta₂ : 0 < beta₂) (heta : 0 < eta)
    (hX₁ : ∀ v, X₁ v ≤ K₁ * (𝔼 x, ‖v x‖))
    (hX₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁, ∀ v, X₂ f v ≤ K₂ * (𝔼 x, ‖v x‖))
    (hdetect₁ : NativeModelDetector degree N p₁ X₁ K₁ M₁ beta₁ (eta / 4))
    (hdetect₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁,
      NativeModelDetector degree N p₂ (X₂ f) K₂ M₂ beta₂ (eta * beta₁ / 8))
    (a b : ZMod N → ℂ) (ha : ∀ x, ‖a x‖ ≤ M₁) (hb : ∀ x, ‖b x‖ ≤ M₂) :
    NativeTwoSiteModelingData degree N p₁ p₂ K₁ K₂ beta₁ beta₂ eta X₁ X₂ a b := by
  classical
  let tau₁ := eta / 4
  let tau₂ := eta * beta₁ / 8
  have htau₁ : 0 < tau₁ := by dsimp [tau₁]; positivity
  have htau₂ : 0 < tau₂ := by dsimp [tau₂]; positivity
  obtain ⟨n, hn, f, F, c, ea, hfirst, hc, hea, hnBound⟩ :=
    exists_native_cyclic_model_of_detector hdegree hp₁ X₁ hK₁ hM₁ hbeta₁ htau₁ hX₁ hdetect₁ a ha
  have hf (i) : f i ∈ nativeCyclicFunctions degree N p₁ := ⟨F i⟩
  have hsecond (i) := exists_native_cyclic_model_of_detector hdegree hp₂ (X₂ (f i))
    hK₂ hM₂ hbeta₂ htau₂ (hX₂ (f i) (hf i)) (hdetect₂ (f i) (hf i)) b hb
  choose m hm g G d eb hsecond hd heb hmBound using hsecond
  have herr₂ : (∑ i, ‖c i‖ * X₂ (f i) (eb i)) ≤ (2 / beta₁) * (2 * tau₂) := by
    calc
      _ ≤ ∑ i, ‖c i‖ * (2 * tau₂) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (heb i) (norm_nonneg _))
      _ = (∑ i, ‖c i‖) * (2 * tau₂) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  have hprecision : 2 * tau₁ + (2 / beta₁) * (2 * tau₂) = eta := by
    dsimp [tau₁, tau₂]
    field_simp
    ring
  have herr : X₁ ea + ∑ i, ‖c i‖ * X₂ (f i) (eb i) ≤ eta := by
    rw [← hprecision]
    exact add_le_add hea herr₂
  let length₁ := 1 + 4 * K₁ ^ 2 / (beta₁ ^ 2 * tau₁ ^ 2)
  let length₂ := 1 + 4 * K₂ ^ 2 / (beta₂ ^ 2 * tau₂ ^ 2)
  have hlength₂ : 0 ≤ length₂ := by dsimp [length₂]; positivity
  have htotal : (Fintype.card (Σ i, Fin (m i)) : ℝ) ≤ length₁ * length₂ := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _i : Fin n, length₂ := Finset.sum_le_sum (fun i _ => hmBound i)
      _ = (n : ℝ) * length₂ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hnBound hlength₂
  exact ⟨n, hn, f, F, c, ea, m, hm, g, G, d, eb, hfirst, hsecond, hc, hd, herr, hnBound, hmBound, htotal⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

noncomputable def NativeCommonDerivativeModels.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f) (hpq : p ≤ q) :
    NativeCommonDerivativeModels s N q f :=
  { B with
    geometry := B.geometry.mono B.model hpq
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    complexity := fun h => (B.complexity h).mono hpq
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (B.correlation h hh) }

theorem exists_normalized_native_common_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hnormalize⟩ := RationalFilteredNilmanifold.exists_normalized_common_correlators s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hf B
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, _, hH, hdense, hS, hsame, hcorr⟩ :=
    hnormalize B.model B.test B.shifts B.nonempty hp B.geometry B.complexity
      (fun h _ => B.norm h) (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).1
    complexity := fun h => (hS h).2.2.1.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  exact ⟨R, fun h => (hS h).2.2.2⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem cyclicNativeInverse_one : CyclicNativeInverse 1 2 := by
  intro N _ p hp f hf hG
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_gowers_two f hf
  obtain ⟨T, hTn, hTc, hTeval⟩ := exists_cyclic_character_niltest χ
  have h12 : (12 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
  have h2p : 2 * p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  have hcorr : Real.exp (-(2 * p)) ≤ ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      _ ≤ gowersNorm 2 f ^ 2 := pow_le_pow_left₀ (Real.exp_nonneg _) hG 2
      _ ≤ _ := hχ
  let F : NativeCyclicModel 1 N ((p + 2) ^ 2) (fun x => χ x) := {
    L := RationalTorus.Algebra 1
    dim := 1
    model := RationalTorus.nilmanifold 1
    test := T
    norm := hTn
    complexity := hTc.mono h12
    eval := fun x => (hTeval x).symm }
  exact ⟨fun x => χ x, ⟨F⟩, (Real.exp_le_exp.mpr (neg_le_neg h2p)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem mean_norm_le_fourier_sum {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) : (𝔼 x, ‖f x‖) ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
  have hpoint (x : G) : ‖f x‖ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = ‖∑ χ : AddChar G ℂ, finiteFourierCoeff f χ * χ x‖ := by rw [finiteFourier_inversion]
      _ ≤ ∑ χ : AddChar G ℂ, ‖finiteFourierCoeff f χ * χ x‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul, AddChar.norm_apply, mul_one]
  exact (Finset.expect_le_expect (fun x _ => hpoint x)).trans_eq (Fintype.expect_const _)

theorem exists_quadratic_small_modulus_correlation {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ g ∈ nativeCyclicFunctions 2 N 211,
      Real.exp (-(8 * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(8 * p)) ≤ ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ 8 := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ gowersNorm 3 f ^ 8 := pow_le_pow_left₀ (Real.exp_nonneg _) hGowers 8
      _ ≤ 𝔼 n, ‖f n‖ := by simpa using gowersNorm_pow_le_mean_norm 2 f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(8 * p + q)) ≤ ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(8 * p)) / Real.exp q = Real.exp (-(8 * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  let hdegree : 1 ≤ 2 := by omega
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hdegree
    test := T.raiseStep hdegree
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hdegree (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_shift_native_two_site_models {degree N : ℕ} [NeZero N] {ι : Type*}
    (hdegree : 1 ≤ degree) {p₁ p₂ : ℝ} (hp₁ : 2 ≤ p₁) (hp₂ : 2 ≤ p₂)
    (T : ι → ZMod N → ℂ) (hT : ∀ i x, ‖T i x‖ ≤ 1)
    (a b : ZMod N → ℂ) {K M beta₁ beta₂ eta : ℝ}
    (hK : 0 < K) (hM : 0 < M) (hbeta₁ : 0 < beta₁) (hbeta₂ : 0 < beta₂) (heta : 0 < eta)
    (ha : ∀ x, ‖a x‖ ≤ M) (hb : ∀ x, ‖b x‖ ≤ K)
    (hdetect₁ : NativeModelDetector degree N p₁ (shiftTestingSeminorm b T) K M beta₁ (eta / 4))
    (hdetect₂ : ∀ f ∈ nativeCyclicFunctions degree N p₁,
      NativeModelDetector degree N p₂ (shiftTestingSeminorm f (translatedTestFamily T))
        1 K beta₂ (eta * beta₁ / 8)) :
    NativeTwoSiteModelingData degree N p₁ p₂ K 1 beta₁ beta₂ eta
      (shiftTestingSeminorm b T) (fun f => shiftTestingSeminorm f (translatedTestFamily T)) a b := by
  apply exists_native_two_site_models hdegree hp₁ hp₂
    (shiftTestingSeminorm b T) (fun f => shiftTestingSeminorm f (translatedTestFamily T))
    hK.le (by norm_num) hM hK hbeta₁ hbeta₂ heta
  · exact shiftTestingSeminorm_le_of_nonneg b T hK.le hb hT
  · intro f hf v
    exact shiftTestingSeminorm_le_of_nonneg f (translatedTestFamily T) (by norm_num)
      (nativeCyclicFunctions_norm hf) (translatedTestFamily_norm_le_one T hT) v
  · exact hdetect₁
  · exact hdetect₂
  · exact ha
  · exact hb

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeVerticalDerivativeData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) where
  normalized : ∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
    (B.test h).orbit = 1
  frequency : B.L →ₗ[ℚ] ℚ
  height : ∀ i, rationalLogHeight (frequency (B.model.basis i)) ≤ p
  vertical : ∀ h z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    (B.test h).observable (z • x) =
      CircleFourier.character ((realifyFunctional frequency z.coord : ℝ) : CircleFourier.Circle) *
        (B.test h).observable x
  integral : ∀ z : B.model.RealGroup, z ∈ B.model.filtration.realification.subgroup s →
    z ∈ B.model.realLattice → ∃ n : ℤ, realifyFunctional frequency z.coord = n

noncomputable def NativeVerticalDerivativeData.mono {s N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {B : NativeCommonDerivativeModels s N p f}
    (V : NativeVerticalDerivativeData B) (hpq : p ≤ q) :
    NativeVerticalDerivativeData (B.mono hpq) where
  normalized := V.normalized
  frequency := V.frequency
  height i := (V.height i).trans hpq
  vertical := V.vertical
  integral := V.integral

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem NativeCommonDerivativeModels.exists_correlated_quadruples {s N : ℕ} [NeZero N]
    {p : ℝ} {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
      Real.exp (-(8 * p + 2)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.2.1 ∈ B.shifts ∧ t.2.1 - t.1 ∈ B.shifts ∧
        t.2.2 ∈ B.shifts ∧ t.2.2 - t.1 ∈ B.shifts ∧
        Real.exp (-(8 * p + 2)) ≤ additiveQuadrupleCorrelation
          (fun h x => (B.test h).evalCyclic N (fun _ => x)) t.1 t.2.1 t.2.2 := by
  classical
  let g : ZMod N → ZMod N → ℂ := fun h x =>
    if h ∈ B.shifts then (B.test h).evalCyclic N (fun _ => x) else 0
  have hunit (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    by_cases hh : h ∈ B.shifts
    · have hcap : ((B.test h).normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast B.norm h
      simp only [g, ite_eq_left hh]
      exact ((B.test h).norm_evalCyclic_le N (fun _ => x)).trans hcap
    · simp only [g, ite_eq_right hh, norm_zero, zero_le_one]
  have hzero (h : ZMod N) (hh : h ∉ B.shifts) (x : ZMod N) : g h x = 0 := by
    simp only [g, ite_eq_right hh]
  have hcorr (h : ZMod N) (hh : h ∈ B.shifts) :
      Real.exp (-p) ≤ ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    simpa only [g, ite_eq_left hh] using B.correlation h hh
  obtain ⟨Q, hQ, hdense, hgood⟩ := exists_many_correlated_additive_quadruples f g B.shifts
    hf hunit hzero (Real.exp_pos _) (Real.exp_pos _) B.density hcorr
  have heq : (Real.exp (-p) * Real.exp (-p)) ^ 4 = Real.exp (-(8 * p)) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hsmall : Real.exp (-(8 * p + 2)) ≤ (Real.exp (-p) * Real.exp (-p)) ^ 4 / 2 := by
    rw [heq]
    calc
      _ ≤ Real.exp (-(8 * p) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := exp_sub_one_le_half_exp _
  refine ⟨Q, hQ, (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans hdense, ?_⟩
  intro t ht
  obtain ⟨h₁, h₂, h₃, h₄, hc⟩ := hgood t ht
  refine ⟨h₁, h₂, h₃, h₄, hsmall.trans ?_⟩
  simpa only [additiveQuadrupleCorrelation, g, ite_eq_left h₁, ite_eq_left h₂,
    ite_eq_left h₃, ite_eq_left h₄] using hc

end Erdos3

end

end OAI
