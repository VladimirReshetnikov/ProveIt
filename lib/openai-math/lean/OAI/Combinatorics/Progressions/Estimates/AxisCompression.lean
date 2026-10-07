import OAI.Combinatorics.Progressions.Estimates.NativeDetectorContradiction
import OAI.Combinatorics.Progressions.Estimates.PositiveShiftTestingGowers
import OAI.Combinatorics.Progressions.Geometry.CoordinateExceptionUnion
import OAI.Combinatorics.Progressions.Nilpotent.MixedPrimitiveNiltest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedAxisProduct {G : Type*} [Add G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (c : ℝ) (y : G) : ℝ := axisProduct f t y / c ^ n

theorem orderedProduct_normalized_telescope (n : ℕ) (x : Fin n → ℝ) (c : ℝ) (hc : c ≠ 0) :
    (∏ i, x i) / c ^ n - 1 =
      ∑ i, (c ^ i.val / c ^ n) * (x i - c) * orderedProductTail x i := by
  calc
    _ = ((∏ i, x i) - c ^ n) / c ^ n := by rw [sub_div, div_self (pow_ne_zero n hc)]
    _ = (∑ i, c ^ i.val * (x i - c) * orderedProductTail x i) / c ^ n := by
      rw [orderedProduct_telescope]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem normalizedAxisProduct_tested_le {G : Type*} [Add G] [Fintype G] {n : ℕ}
    (f : Fin n → G → ℝ) (t : Fin n → G) (c : ℝ) (hc : 1 ≤ c)
    (T : G → ℝ) {error : ℝ} (herror : 0 ≤ error)
    (hinsert : ∀ i, (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * T y) ≤ error) :
    (𝔼 y, (normalizedAxisProduct f t c y - 1) * T y) ≤ (n : ℝ) * error := by
  have hc0 : 0 < c := by linarith
  have hpoint (y) : (normalizedAxisProduct f t c y - 1) * T y =
      ∑ i, (c ^ i.val / c ^ n) * ((f i (y + t i) - c) * axisSuffix f t i y * T y) := by
    rw [normalizedAxisProduct, axisProduct, orderedProduct_normalized_telescope n _ c hc0.ne', Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    change (c ^ i.val / c ^ n) * (f i (y + t i) - c) *
      orderedProductTail (fun j => f j (y + t j)) i * T y = _
    unfold axisSuffix
    ring
  calc
    _ = ∑ i, (c ^ i.val / c ^ n) *
        (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * T y) := by
      simp only [hpoint, Finset.expect_sum_comm, ← Finset.mul_expect]
    _ ≤ ∑ _i : Fin n, error := by
      apply Finset.sum_le_sum
      intro i _
      have hcoeff0 : 0 ≤ c ^ i.val / c ^ n := div_nonneg (pow_nonneg hc0.le _) (pow_nonneg hc0.le _)
      have hcoeff1 : c ^ i.val / c ^ n ≤ 1 :=
        (div_le_one (pow_pos hc0 n)).mpr (pow_le_pow_right₀ hc (Nat.le_of_lt i.isLt))
      exact (mul_le_mul_of_nonneg_left (hinsert i) hcoeff0).trans
        (mul_le_of_le_one_left herror hcoeff1)
    _ = _ := by simp

theorem normalizedAxisProduct_bounds {G : Type*} [Add G] {n : ℕ} {p c : ℝ}
    (f : Fin n → G → ℝ) (hf : ∀ i y, 0 ≤ f i y ∧ f i y ≤ Real.exp p)
    (t : Fin n → G) (hc : 1 ≤ c) (y : G) :
    0 ≤ normalizedAxisProduct f t c y ∧ normalizedAxisProduct f t c y ≤ Real.exp ((n : ℝ) * p) := by
  have hnonneg := axisProduct_nonneg f (fun i y => (hf i y).1) t y
  refine ⟨div_nonneg hnonneg (pow_nonneg (by linarith) _), ?_⟩
  exact (div_le_self hnonneg (one_le_pow₀ hc)).trans (axisProduct_le_exp f hf t y)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_cyclic_small_modulus_correlation (s : ℕ) (hs : 1 ≤ s)
    {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm (s + 1) f) :
    ∃ g ∈ nativeCyclicFunctions s N 211,
      Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) ≤
      ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ (2 ^ (s + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ gowersNorm (s + 1) f ^ (2 ^ (s + 1)) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hGowers _
      _ ≤ 𝔼 n, ‖f n‖ := gowersNorm_pow_le_mean_norm s f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤
      ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) / Real.exp q =
        Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hs
    test := T.raiseStep hs
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hs (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

section

universe u

namespace Erdos3

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_adapted_basis_of_shift_failure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p epsilon : ℝ}, 0 ≤ p →
      0 ≤ epsilon → epsilon ≤ 1 → ∀ f g J : ZMod N → ℝ,
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      (¬ ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicNiltestShiftBound.{u} s N p (Real.exp (-p))
          (fun n => f n - (1 + epsilon) * g n) J E) →
      ∃ B : PositiveShiftBasis.{u} s N ((p + C) ^ C) (fun n => f n - (1 + epsilon) * g n) J,
        ∃ weight : Fin B.dim → ℕ, ∀ i, B.model.filtration.layer i =
          Submodule.span ℚ (B.model.basis '' {j | i ≤ weight j}) := by
  obtain ⟨c, _, hbasis⟩ := exists_positive_basis_of_shift_failure s
  obtain ⟨k, _, hadapt⟩ := PositiveShiftBasis.exists_adapted
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C c) ^ c + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro N _ p epsilon hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  obtain ⟨B⟩ := hbasis hp hepsilon hepsilon1 f g J hf hg hJ hfailure
  obtain ⟨B', _, ⟨weight, hweight⟩, _, _, _⟩ := hadapt B
  have hbound : ((p + c) ^ c + k) ^ k ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨B'.mono hbound, weight, hweight⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_mixed_primitive_correlation_large_modulus (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ g ∈ nativeCyclicFunctions (d + 3) N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hprimitive⟩ := exists_mixed_primitive_gowers d hI
  let B := I
  have hinverse : CyclicNativeInverse (d + 2) B := hI
  obtain ⟨D, _, hmodel⟩ := NativeMultidegreeNilcharacter.exists_mixed_primitive_niltest_budget d
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + 2 + Polynomial.C B) ^ B
  let R := U + V + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + V + (R + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + 2 + B) ^ B
  let r := u + v + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : u + v + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, V, R, u, v, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + D) ^ D := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hmC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, i, hW⟩ :=
    hprimitive hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse (by linarith : 2 ≤ u + 2)
    (W.mixedPrimitiveFactor f i) (W.mixedPrimitiveFactor_norm f hf i)
    ((Real.exp_le_exp.mpr (by linarith : -(u + 2) ≤ -u)).trans hW)
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hgmodel : g ∈ nativeCyclicFunctions (d + 2) N r :=
    ⟨{ G with complexity := G.complexity.mono hvr }⟩
  have hm := hmodel hr (W.mono hqr) i g hgmodel
  have hm' : (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
      nativeCyclicFunctions (d + 3) N ((r + D) ^ D) := by
    simpa only [NativeMultidegreeNilcharacter.mono_eval] using hm
  obtain ⟨M⟩ := hm'
  refine ⟨fun n => star (W.eval i (fun _ => (n.val : ℤ))) * g n,
    ⟨{ M with complexity := M.complexity.mono hmC }⟩, ?_⟩
  have heq : (𝔼 n : ZMod N, f n * star (star (W.eval i (fun _ => (n.val : ℤ))) * g n)) =
      𝔼 n : ZMod N, W.mixedPrimitiveFactor f i n * star (g n) := by
    apply Finset.expect_congr rfl
    intro n _
    simp only [NativeMultidegreeNilcharacter.mixedPrimitiveFactor, star_mul, star_star]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hg

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_step (d : ℕ) {I : ℕ}
    (hI : CyclicNativeInverse (d + 2) I) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 3) C := by
  obtain ⟨A, _, hlarge⟩ := exists_mixed_primitive_correlation_large_modulus d hI
  let L := 2 ^ (d + 4)
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + Polynomial.C L * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hLp : 0 ≤ (L : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp0
  have hsum : u + (L : ℝ) * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨M⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨M⟩, hcorr⟩ :=
      exists_native_cyclic_small_modulus_correlation (d + 3) (by omega) (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : (L : ℝ) * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

theorem exists_cyclicNativeInverse_add_two (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse (d + 2) C := by
  induction d with
  | zero => exact exists_cyclicNativeInverse_two
  | succ d ih =>
      obtain ⟨I, _, hI⟩ := ih
      exact exists_cyclicNativeInverse_step d hI

theorem exists_cyclicNativeInverse_ge_two (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse s C := by
  have h : s - 2 + 2 = s := Nat.sub_add_cancel hs
  simpa only [h] using exists_cyclicNativeInverse_add_two (s - 2)

end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicNativeInverse_positive (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse s C := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => exact ⟨2, le_rfl, cyclicNativeInverse_one⟩
      | succ s => exact exists_cyclicNativeInverse_add_two s

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_native_inverse_on_cyclic_encoding (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ] {N : ℕ} [NeZero N]
      (Q : Finset (σ → ℤ)), Q.Nonempty → ∀ (φ : (σ → ℤ) →+ ℤ),
      ReflectsPairSums ((Int.castAddHom (ZMod N)).comp φ) (Q : Set (σ → ℤ)) →
      (∀ x ∈ Q, 0 ≤ φ x ∧ φ x < (N : ℤ)) →
      ∀ {p q : ℝ}, 2 ≤ p → 0 ≤ q → Real.exp (-q) ≤ (Q.card : ℝ) / (N : ℝ) →
      ∀ f : (σ → ℤ) → ℂ, (∀ x ∈ Q, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ finiteSupportGowersNorm (s + 1) Q f →
      ∃ V : NativeSampleCorrelation (fun _ : σ => 1) s ((p + q + C) ^ C) Q id f,
        V.test.normBound ≤ 1 := by
  obtain ⟨C, hC, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ N _ Q hQ φ hφ hrep p q hp hq hden f hf hGowers
  let ψ : (σ → ℤ) →+ ZMod N := (Int.castAddHom (ZMod N)).comp φ
  let F := imageExtension ψ Q f
  have hF : ∀ y, ‖F y‖ ≤ 1 := imageExtension_norm_le_one ψ Q f hφ.injOn hf
  have hG : Real.exp (-(p + q)) ≤ gowersNorm (s + 1) F :=
    exp_le_gowers_imageExtension s ψ Q hφ f (by simpa only [ZMod.card] using hden) hGowers
  obtain ⟨g, ⟨M⟩, hcorr⟩ := hinverse (by linarith : 2 ≤ p + q) F hF hG
  let T := M.test.linearPullbackHom (fun _ : Unit => φ)
  have heval (x : σ → ℤ) (hx : x ∈ Q) : T.eval x = g (ψ x) := by
    change (M.test.linearPullbackHom (fun _ : Unit => φ)).eval x = g (ψ x)
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom, M.eval]
    change M.test.eval (fun _ => φ x) = M.test.eval (fun _ => (((φ x : ZMod N).val) : ℤ))
    simp only [ZMod.val_intCast, Int.emod_eq_of_lt (hrep x hx).1 (hrep x hx).2]
  refine ⟨{
    L := M.L
    dim := M.dim
    model := M.model
    test := T
    complexity := M.complexity
    correlation := ?_ }, ?_⟩
  · have hmean : (𝔼 x ∈ Q, f x * star (T.eval x)) =
        (𝔼 x ∈ Q, f x * star (g (ψ x))) := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [heval x hx]
    change Real.exp (-((p + q + C) ^ C)) ≤ ‖𝔼 x ∈ Q, f x * star (T.eval x)‖
    rw [hmean]
    exact hcorr.trans (norm_expect_imageExtension_mul_le ψ Q hQ hφ.injOn f (fun y => star (g y)))
  · exact M.norm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_detector_of_gowers (s : ℕ) (hs : 1 ≤ s) (A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {u : ℝ}, 2 ≤ u →
      ∀ (X : Seminorm ℂ (ZMod N → ℂ)) (K M tau : ℝ),
      K / tau ≤ Real.exp u → Real.exp (-u) ≤ tau / M ^ 2 →
      (∀ v : ZMod N → ℂ, (∀ x, ‖v x‖ ≤ 1) →
        Real.exp (-(2 * u)) ≤ X v →
        Real.exp (-((2 * u + 2) ^ A)) ≤ gowersNorm (s + 1) v) →
      NativeModelDetector s N ((u + C) ^ C) X K M
        (Real.exp (-((u + C) ^ C))) tau := by
  obtain ⟨B, _, hinverse⟩ := exists_cyclicNativeInverse_positive s hs
  let Y : Polynomial ℕ := Polynomial.X
  let P := (2 * Y + 2) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ u hu X K M tau hcap hthreshold hdetect psi hpsi hlarge
  let v : ZMod N → ℂ := fun x => (Real.exp (-u) : ℂ) * psi x
  have hu0 : 0 ≤ u := by linarith
  have hv : ∀ x, ‖v x‖ ≤ 1 := by
    intro x
    calc
      _ = Real.exp (-u) * ‖psi x‖ := by
        simp only [v, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-u) * (K / tau) := mul_le_mul_of_nonneg_left (hpsi x) (Real.exp_nonneg _)
      _ ≤ Real.exp (-u) * Real.exp u := mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hXv : X v = Real.exp (-u) * X psi := by
    change X ((Real.exp (-u) : ℂ) • psi) = _
    rw [map_smul_eq_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hnorm : Real.exp (-(2 * u)) ≤ X v := by
    rw [hXv]
    calc
      _ = Real.exp (-u) * Real.exp (-u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-u) * (tau / M ^ 2) := mul_le_mul_of_nonneg_left hthreshold (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (Real.exp_nonneg _)
  let q := (2 * u + 2) ^ A + 2
  have hq : 2 ≤ q := by
    dsimp [q]
    have hp := pow_nonneg (by linarith : 0 ≤ 2 * u + 2) A
    linarith
  have hG : Real.exp (-q) ≤ gowersNorm (s + 1) v :=
    (Real.exp_le_exp.mpr (by dsimp [q]; linarith)).trans (hdetect v hv hnorm)
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse hq v hv hG
  have hcost : (q + B) ^ B ≤ (u + C) ^ C := by
    simpa [Y, P, q, Polynomial.eval₂_pow] using hbudget u hu0
  have hmean : ‖𝔼 x, v x * star (g x)‖ = Real.exp (-u) * ‖𝔼 x, psi x * star (g x)‖ := by
    have heq : (𝔼 x, v x * star (g x)) = (Real.exp (-u) : ℂ) * (𝔼 x, psi x * star (g x)) := by
      simp only [v, Finset.mul_expect, mul_assoc]
    rw [heq, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hc : Real.exp (-u) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  refine ⟨g, ⟨{ G with complexity := G.complexity.mono hcost }⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  apply hg.trans
  rw [hmean]
  exact mul_le_of_le_one_left (norm_nonneg _) hc

end Erdos3

end

section

namespace Erdos3.PositiveShiftBasis

universe u

theorem exists_testingFamily_native_detectors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {u : ℝ}, 2 ≤ u → q + 2 ≤ u →
      ∀ (W : ZMod N → ℂ), (∀ x, ‖W x‖ ≤ Real.exp u) →
      ∀ K M tau : ℝ, K / tau ≤ Real.exp u → Real.exp (-u) ≤ tau / M ^ 2 →
      NativeModelDetector (s + 1) N ((u + C) ^ C)
        (shiftTestingSeminorm W B.testingFamily) K M (Real.exp (-((u + C) ^ C))) tau ∧
      NativeModelDetector (s + 1) N ((u + C) ^ C)
        (shiftTestingSeminorm W (translatedTestFamily B.testingFamily))
        K M (Real.exp (-((u + C) ^ C))) tau := by
  obtain ⟨A, _, hGowers⟩ := exists_testingFamily_gowers_detection.{u} s
  obtain ⟨C, hC, hnative⟩ := exists_native_detector_of_gowers (s + 1) (by omega) A
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B u hu hqu W hW K M tau hcap hthreshold
  have hW₂ (x) : ‖W x‖ ≤ Real.exp (2 * u) :=
    (hW x).trans (Real.exp_le_exp.mpr (by linarith))
  constructor
  · apply hnative hu (shiftTestingSeminorm W B.testingFamily) K M tau hcap hthreshold
    intro v hv hlarge
    exact (hGowers B (by linarith) (by linarith) v W hv hW₂).1 hlarge
  · apply hnative hu (shiftTestingSeminorm W (translatedTestFamily B.testingFamily))
      K M tau hcap hthreshold
    intro v hv hlarge
    exact (hGowers B (by linarith) (by linarith) v W hv hW₂).2 hlarge

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open NativeModelingNumerics

universe u

theorem exists_bounded_testingFamily_native_detectors (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) {p : ℝ}, 2 ≤ p → q ≤ p →
      ∀ b : ZMod N → ℂ, (∀ x, ‖b x‖ ≤ Real.exp p) →
      ∃ p₁ p₂ beta₁ beta₂ : ℝ,
        p ≤ (p + C) ^ C ∧ 2 ≤ p₁ ∧ 2 ≤ p₂ ∧ p₁ ≤ (p + C) ^ C ∧ p₂ ≤ (p + C) ^ C ∧
        0 < beta₁ ∧ 0 < beta₂ ∧
        2 / beta₁ ≤ Real.exp ((p + C) ^ C) ∧ 2 / beta₂ ≤ Real.exp ((p + C) ^ C) ∧
        (1 + 4 * Real.exp p ^ 2 /
          (beta₁ ^ 2 * (Real.exp (-(2 * q + 2)) / 4) ^ 2)) *
        (1 + 4 / (beta₂ ^ 2 *
          (Real.exp (-(2 * q + 2)) * beta₁ / 8) ^ 2)) ≤ Real.exp ((p + C) ^ C) ∧
        NativeModelDetector (s + 1) N p₁ (shiftTestingSeminorm b B.testingFamily)
          (Real.exp p) (Real.exp (p + 2)) beta₁ (Real.exp (-(2 * q + 2)) / 4) ∧
        (∀ f ∈ nativeCyclicFunctions (s + 1) N p₁,
          NativeModelDetector (s + 1) N p₂
            (shiftTestingSeminorm f (translatedTestFamily B.testingFamily))
            1 (Real.exp p) beta₂ (Real.exp (-(2 * q + 2)) * beta₁ / 8)) := by
  obtain ⟨D, hD, hdetector⟩ := exists_testingFamily_native_detectors.{u} s
  let Y : Polynomial ℕ := Polynomial.X
  let R := (8 * Y + 8 + Polynomial.C D) ^ D
  let S := (8 * Y + 8 + R + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (1000 * (Y + S + 2))
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B p hp hqp b hb
  let u₁ := 8 * p + 8
  let p₁ := (u₁ + D) ^ D
  let p₂ := (u₁ + p₁ + D) ^ D
  have hp0 : 0 ≤ p := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hu₁ : 2 ≤ u₁ := by dsimp [u₁]; linarith
  have hbase : 1 ≤ u₁ + D := by linarith
  have hp₁base : u₁ + D ≤ p₁ := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ D)
  have hp₁ : 2 ≤ p₁ := by linarith
  have hp₁₂ : p₁ ≤ p₂ := by
    change (u₁ + (D : ℝ)) ^ D ≤ (u₁ + p₁ + D) ^ D
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have hp₂ : 2 ≤ p₂ := hp₁.trans hp₁₂
  have hq : 0 ≤ q := (Nat.cast_nonneg B.dim).trans B.geometry.1
  have hcost : 1000 * (p + p₂ + 2) ≤ (p + C) ^ C := by
    simpa [Y, R, S, p₁, p₂, u₁, Polynomial.eval₂_pow] using hbudget p hp0
  have hpcost : p ≤ (p + C) ^ C := by linarith
  have hp₁cost : p₁ + 2 ≤ (p + C) ^ C := by linarith
  have hp₂cost : p₂ + 2 ≤ (p + C) ^ C := by linarith
  obtain ⟨hcap₁, hthreshold₁, hcap₂, hthreshold₂⟩ :=
    sequential_thresholds (r := p₁) hp hqp
  refine ⟨p₁, p₂, Real.exp (-p₁), Real.exp (-p₂), hpcost, hp₁, hp₂,
    by linarith, by linarith, Real.exp_pos _, Real.exp_pos _, ?_, ?_, ?_, ?_, ?_⟩
  · exact (coefficient_bound p₁).trans (Real.exp_le_exp.mpr hp₁cost)
  · exact (coefficient_bound p₂).trans (Real.exp_le_exp.mpr hp₂cost)
  · exact (length_product_bound hp hq hqp (by linarith) hp₁₂).trans (Real.exp_le_exp.mpr hcost)
  · exact (hdetector B hu₁ (by dsimp [u₁]; linarith) b
      (fun x => (hb x).trans (Real.exp_le_exp.mpr (by dsimp [u₁]; linarith)))
      (Real.exp p) (Real.exp (p + 2)) (Real.exp (-(2 * q + 2)) / 4)
      hcap₁ hthreshold₁).1
  · intro f hf
    have hu₂ : 2 ≤ u₁ + p₁ := by linarith
    have hfunit (x) : ‖f x‖ ≤ Real.exp (u₁ + p₁) :=
      (nativeCyclicFunctions_norm hf x).trans (Real.one_le_exp_iff.mpr (by linarith))
    exact (hdetector B hu₂ (by dsimp [u₁]; linarith) f hfunit
      1 (Real.exp p) (Real.exp (-(2 * q + 2)) * Real.exp (-p₁) / 8)
      hcap₂ hthreshold₂).2

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u

theorem CyclicNiltestUpperComparison.mono_budget
    {degree N : ℕ} [NeZero N] {P Q epsilon delta : ℝ} {f g : ZMod N → ℝ}
    (h : CyclicNiltestUpperComparison.{u} degree N Q epsilon f g)
    (hPQ : P ≤ Q) (hdelta : epsilon ≤ delta) :
    CyclicNiltestUpperComparison.{u} degree N P delta f g := by
  intro L _ _ s dim _ _ _ _ D hs T hT hcomp
  exact (h D hs T hT (hcomp.mono hPQ)).trans hdelta

theorem cyclic_difference_norm_bound {N : ℕ} [NeZero N] {p epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) (f g : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) (x : ZMod N) :
    ‖((f x - (1 + epsilon) * g x : ℝ) : ℂ)‖ ≤ Real.exp (p + 2) := by
  have hm0 : 0 ≤ (1 + epsilon) * g x := mul_nonneg (by linarith) (hg x).1
  have hm : (1 + epsilon) * g x ≤ 2 * Real.exp p :=
    (mul_le_mul_of_nonneg_right (by linarith : 1 + epsilon ≤ 2) (hg x).1).trans
      (mul_le_mul_of_nonneg_left (hg x).2 (by norm_num))
  have hnorm : |f x - (1 + epsilon) * g x| ≤ 2 * Real.exp p := by
    rw [abs_le]
    constructor <;> linarith [(hf x).1, (hf x).2, Real.exp_pos p]
  rw [Complex.norm_real, Real.norm_eq_abs]
  apply hnorm.trans
  exact NativeModelingNumerics.mul_exp_le_exp
    (by linarith [Real.add_one_le_exp (2 : ℝ)]) le_rfl

namespace PositiveShiftBasis

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_bounded_native_contradiction (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {f g J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f n - (1 + epsilon) * g n) J)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f n ∧ f n ≤ Real.exp p) →
      (∀ n, 0 ≤ g n ∧ g n ≤ Real.exp p) →
      (∀ n, 0 ≤ J n ∧ J n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f g → False := by
  obtain ⟨D, _, hdetectors⟩ := exists_bounded_testingFamily_native_detectors (s + 1)
  obtain ⟨E, _, hcontra⟩ := exists_native_detector_contradiction s c hc hepsilon hepsilon1 hshift
  let Y : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Y + Polynomial.C D) ^ D + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro N _ q f g J B w hw p hp hqp hodd hN hf hg hJ hcompare
  have hJnorm (x) : ‖(J x : ℂ)‖ ≤ Real.exp p := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJ x).1] using (hJ x).2
  obtain ⟨p₁, p₂, beta₁, beta₂, hpwide, hp₁, hp₂, hp₁wide, hp₂wide,
    hbeta₁, hbeta₂, hcoeff₁, hcoeff₂, hlength, hdet₁, hdet₂⟩ :=
    hdetectors B hp hqp (fun x => (J x : ℂ)) hJnorm
  have hcost : ((p + D) ^ D + E) ^ E ≤ (p + C) ^ C := by
    simpa [Y, Polynomial.eval₂_pow] using hbudget p (by linarith)
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp ((p + D) ^ D) :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpwide)⟩
  exact hcontra B w hw (hp.trans hpwide) hp₁ hp₂ (hqp.trans hpwide) hp₁wide hp₂wide
    (Real.exp_pos _) (Real.exp_pos _) hbeta₁ hbeta₂
    (cyclic_difference_norm_bound hepsilon hepsilon1 f g hf hg) hJnorm
    hcoeff₁ hcoeff₂ hlength hdet₁ hdet₂ hodd
    ((Real.exp_le_exp.mpr hcost).trans hN) (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))

end PositiveShiftBasis
end Erdos3

end

section

namespace Erdos3

theorem exists_cyclicShiftComparison_step (s c : ℕ) (hc : 2 ≤ c)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hshift : CyclicShiftComparison.{0} (s + 1) (epsilon / 2) c) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} (s + 2) epsilon C := by
  obtain ⟨A, _, hextract⟩ := exists_adapted_basis_of_shift_failure.{0} (s + 1)
  obtain ⟨B, _, hcontra⟩ :=
    PositiveShiftBasis.exists_bounded_native_contradiction s c hc hepsilon hepsilon1 hshift
  let Y : Polynomial ℕ := Polynomial.X
  let R := Y + (Y + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hodd hN f g J hf hg hJ hcompare
  by_contra hfailure
  obtain ⟨basis, w, hw⟩ := hextract (by linarith) hepsilon.le hepsilon1.le f g J hf hg hJ hfailure
  let q := (p + A) ^ A
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 2 ≤ r := by dsimp [r]; linarith
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hcost : (r + B) ^ B ≤ (p + 2) ^ C := by
    simpa [Y, R, q, r, Polynomial.eval₂_pow] using hbudget p (by linarith)
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp r :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpr)⟩
  exact hcontra basis w hw hr hqr hodd ((Real.exp_le_exp.mpr hcost).trans hN)
    (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))

theorem exists_cyclicShiftComparison_succ (s : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} (s + 1) epsilon C := by
  induction s with
  | zero =>
    intro epsilon hepsilon hepsilon1
    exact exists_degree_one_cyclicShiftComparison hepsilon hepsilon1
  | succ s ih =>
    intro epsilon hepsilon hepsilon1
    obtain ⟨c, hc, hshift⟩ := ih (epsilon / 2) (by linarith) (by linarith)
    exact exists_cyclicShiftComparison_step s c hc hepsilon hepsilon1 hshift

theorem exists_cyclicShiftComparison_positive (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ CyclicShiftComparison.{0} s epsilon C := by
  cases s with
  | zero => omega
  | succ s => exact exists_cyclicShiftComparison_succ s epsilon hepsilon hepsilon1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def CyclicTranslatedNiltestShiftBound (degree N : ℕ) [NeZero N]
    (p error : ℝ) (a J : ZMod N → ℝ) (E : Finset (ZMod N)) : Prop :=
  ∀ h ∉ E, ∀ f : ZMod N → ℝ, PositiveCyclicNiltest.{0} degree N p f →
    ∀ b : ZMod N, (𝔼 x, a x * J (x + h) * f (b + x)) ≤ error

theorem exists_cyclicShiftComparison_translated (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N : ℕ) [NeZero N] {p : ℝ}, 2 ≤ p → Odd N →
      Real.exp ((p + 2) ^ C) ≤ N → ∀ f g J : ZMod N → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ Real.exp p) →
      (∀ x, 0 ≤ g x ∧ g x ≤ Real.exp p) →
      (∀ x, 0 ≤ J x ∧ J x ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} s N ((p + 2) ^ C) (Real.exp (-((p + 2) ^ C))) f g →
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-p) * N ∧
        CyclicTranslatedNiltestShiftBound (s - 1) N p (Real.exp (-p))
          (fun x => f x - (1 + epsilon) * g x) J E := by
  obtain ⟨c, hc, hshift⟩ := exists_cyclicShiftComparison_positive s hs hepsilon hepsilon1
  obtain ⟨D, _, htesting⟩ := exists_translated_shift_testing_bound 1
  let Y : Polynomial ℕ := Polynomial.X
  let Q := 8 * Y + 8
  let B := (Q + Polynomial.C D) ^ D
  let R := B + Q + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget ((R + 2) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hodd hN f g J hf hg hJ hcompare
  let q := 8 * p + 8
  let b₀ := (q + D) ^ D
  let r := b₀ + q + 10
  have hp0 : 0 ≤ p := by linarith
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hb : 0 ≤ b₀ := by dsimp [b₀]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := hpq.trans hqr
  have hr : 2 ≤ r := hp.trans hpr
  have hrr : r ≤ (r + 2) ^ c := le_power_budget (by linarith) (by omega)
  have hcost : (r + 2) ^ c ≤ (p + 2) ^ C := by
    simpa [Y, Q, B, R, q, b₀, r, Polynomial.eval₂_pow] using hbudget p hp0
  have hNr : Real.exp ((r + 2) ^ c) ≤ N := (Real.exp_le_exp.mpr hcost).trans hN
  have hcap (v : ZMod N → ℝ) (hv : ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp p) :
      ∀ x, 0 ≤ v x ∧ v x ≤ Real.exp r :=
    fun x => ⟨(hv x).1, (hv x).2.trans (Real.exp_le_exp.mpr hpr)⟩
  obtain ⟨E, hE, hbound⟩ := hshift N r hr hodd hNr f g J (hcap f hf) (hcap g hg) (hcap J hJ)
    (hcompare.mono_budget hcost (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  refine ⟨E, hE.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg hpr)) (Nat.cast_nonneg _)), ?_⟩
  intro h hh T hT b
  have hweight (x) : |(f x - (1 + epsilon) * g x) * J (x + h)| ≤ Real.exp (2 * p + 2) := by
    have hd := cyclic_difference_norm_bound hepsilon hepsilon1 f g hf hg x
    rw [Complex.norm_real, Real.norm_eq_abs] at hd
    rw [abs_mul, abs_of_nonneg (hJ (x + h)).1]
    calc
      _ ≤ Real.exp (p + 2) * Real.exp p := mul_le_mul hd (hJ (x + h)).2 (hJ (x + h)).1 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hinv : 1 / Real.exp (-q) ≤ Real.exp ((q + 2) ^ (1 : ℕ)) := by
    rw [Real.exp_neg, one_div, inv_inv, pow_one]
    exact Real.exp_le_exp.mpr (by linarith)
  have htest := htesting hq (Real.exp_pos (-q)) hinv
    (by dsimp [r, b₀]; linarith : (q + D) ^ D ≤ r) (Real.exp_nonneg (-r))
    (Real.exp_nonneg (2 * p + 2)) (fun x => f x - (1 + epsilon) * g x) J E
    hbound h hh hweight T (hT.mono le_rfl hpq) b
  apply htest.trans
  exact translated_shift_error_bound hp hb ((Real.exp_le_exp.mpr hrr).trans hNr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem exists_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N n : ℕ} [NeZero N] {p r g : ℝ},
      0 ≤ p → 2 ≤ r → p ≤ r → (n : ℝ) * p ≤ r → 1 ≤ g → g ≤ Real.exp r →
      Odd N → Real.exp ((r + 2) ^ C) ≤ N →
      ∀ f : Fin n → ZMod N → ℝ, (∀ i x, 0 ≤ f i x ∧ f i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((r + 2) ^ C)
        (Real.exp (-((r + 2) ^ C))) (f i) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ (n : ℝ) * Real.exp (-r) * (N : ℝ) ^ n ∧
        (∀ t y, 0 ≤ normalizedAxisProduct f t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct f t ((1 + epsilon) * g) y ≤ Real.exp ((n : ℝ) * p)) ∧
        ∀ t, t ∉ S → CyclicNiltestUpperComparison.{0} (s - 1) N r
          ((n : ℝ) * Real.exp (-r)) (normalizedAxisProduct f t ((1 + epsilon) * g)) (fun _ => 1) := by
  classical
  obtain ⟨C, hC, hshift⟩ := exists_cyclicShiftComparison_translated s hs hepsilon hepsilon1
  refine ⟨C, hC, ?_⟩
  intro N n _ p r g hp hr hpr hnpr hg hgb hodd hN f hf hcompare
  let c := (1 + epsilon) * g
  have hc : 1 ≤ c := by
    dsimp [c]
    calc
      1 ≤ g := hg
      _ = 1 * g := (one_mul g).symm
      _ ≤ (1 + epsilon) * g := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hex (i : Fin n) (t : Fin n → ZMod N) :
      ∃ E : Finset (ZMod N), (E.card : ℝ) ≤ Real.exp (-r) * N ∧
        CyclicTranslatedNiltestShiftBound (s - 1) N r (Real.exp (-r))
          (fun x => f i x - c) (axisSuffix f t i) E := by
    apply hshift N hr hodd hN (f i) (fun _ => g) (axisSuffix f t i)
    · intro x
      exact ⟨(hf i x).1, (hf i x).2.trans (Real.exp_le_exp.mpr hpr)⟩
    · intro x
      exact ⟨by linarith, hgb⟩
    · intro x
      exact ⟨axisSuffix_nonneg f (fun j y => (hf j y).1) t i x,
        (axisSuffix_le_exp hp f hf t i x).trans (Real.exp_le_exp.mpr hnpr)⟩
    · exact hcompare i
  choose E hE hbound using hex
  let A : Fin n → (Fin n → ZMod N) → Finset (ZMod N) :=
    fun i t => E i (Function.update t i 0)
  have hA (i) (t) : ((A i t).card : ℝ) ≤ Real.exp (-r) * Fintype.card (ZMod N) := by
    simpa only [A, ZMod.card] using hE i (Function.update t i 0)
  have hAi (i) (t) (a : ZMod N) : A i (Function.update t i a) = A i t := by
    simp only [A, Function.update_idem]
  obtain ⟨S, hS, hgood⟩ := exists_coordinate_exception_union A hA hAi
  refine ⟨S, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin, Fintype.card_fun, ZMod.card, Nat.cast_pow] using hS
  · intro t y
    exact normalizedAxisProduct_bounds f hf t hc y
  · intro t ht L _ _ degree dim _ _ _ _ D hdegree T hT hTc
    let U : ZMod N → ℝ := fun x => (T.evalCyclic N (fun _ => x)).re
    have hU : PositiveCyclicNiltest.{0} (s - 1) N r U :=
      .of_test D hdegree T hT hTc (fun _ => rfl)
    apply normalizedAxisProduct_tested_le f t c hc U (Real.exp_nonneg (-r))
    intro i
    have hi := hgood t ht i
    have hb := hbound i (Function.update t i 0)
    have hJ : axisSuffix f (Function.update t i 0) i = axisSuffix f t i := by
      funext y
      exact axisSuffix_update f t i 0 y
    rw [hJ] at hb
    have hcorr := hb (-(t i)) hi U hU (-(t i))
    have heq : (𝔼 y, (f i (y + t i) - c) * axisSuffix f t i y * U y) =
        𝔼 x, (f i x - c) * axisSuffix f t i (x + -(t i)) * U (-(t i) + x) := by
      apply Fintype.expect_equiv (Equiv.addRight (t i))
      intro y
      simp [add_assoc, add_comm]
    exact heq.trans_le hcorr

end Erdos3

end

end OAI
