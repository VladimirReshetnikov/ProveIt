/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
import OAI.Combinatorics.Progressions.Estimates.NativeRetainedInverseIntervals
import OAI.Combinatorics.Progressions.Nilpotent.QuadraticPrimitiveNiltest
import OAI.Combinatorics.Progressions.Polynomial.StepOneScalarPhase

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_unit_row_model_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ) (R : (Unit → ℤ) → ℂ), (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p R) →
      Real.exp (-p) ≤ ‖𝔼 n : ZMod N, f n * star (R (fun _ => (n.val : ℤ)))‖ →
      ∃ g : (Unit → ℤ) → ℂ,
        (∀ x, ‖g x‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) g) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n : ZMod N, f n * star (g (fun _ => (n.val : ℤ)))‖ ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ k : ZMod N, ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g (fun _ => (n.val : ℤ)) * star (g (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hdifference⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_univariate_cyclic_difference_models s hs
  let X : Polynomial ℕ := Polynomial.X
  let U := (2 * X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + 4 + (U + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f R hf hR hcorr
  let sample (_ : Unit) (n : ZMod N) : Unit → ℤ := fun _ => (n.val : ℤ)
  have hc : Real.exp (-p) ≤ 𝔼 _h : Unit, ‖𝔼 n : ZMod N, f n * star (R (sample () n))‖ := by
    simpa only [Fintype.expect_const] using hcorr
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion (Classical.choice hR) hp hc
  have hpp : p + p = 2 * p := by ring
  rw [hpp] at P
  obtain ⟨n, hn, hncard, V, hD, hV⟩ := hunit P.model P.test
    (by positivity : 0 ≤ 2 * p) P.complexity sample (fun _ n => f n) (fun _ n => hf n) P.correlation
  let u := (2 * p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 4 + (u + p + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u + 4 ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have huC' : u ≤ (p + C) ^ C := by linarith
  let g : (Unit → ℤ) → ℂ := (V.test P.test.orbit 0).eval
  have hcard : (Fintype.card (Fin (n + 1)) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hncard
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (V.test P.test.orbit 0).norm_eval_le x
  · exact ⟨(NativeIntegerExpansion.ofTest (V.test P.test.orbit 0)
      (V.test_complexity P.test.orbit hu hD 0) (fun _ => rfl)).mono huC⟩
  · apply (Real.exp_le_exp.mpr (neg_le_neg huC')).trans
    simpa only [sample, Fintype.expect_const] using hV
  · intro e he hN k
    obtain ⟨K, ⟨E⟩, herr⟩ := hdifference P.model V P.test.orbit hu hD hcard he hN 0 0 k
    have hcost : (u + e + B) ^ B ≤ (p + e + C) ^ C := by
      have hu' : u ≤ (2 * (p + e) + A) ^ A :=
        pow_le_pow_left₀ (by positivity) (by linarith) A
      have hb : (2 * (p + e) + A) ^ A + 4 +
          ((2 * (p + e) + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
        simpa [X, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
      apply le_trans _ ((le_add_of_nonneg_left (by positivity)).trans hb)
      exact pow_le_pow_left₀ (by positivity) (by linarith) B
    exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem dense_set_mean_lower_bound {I : Type*} [Fintype I] [Nonempty I]
    (H : Finset I) (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) {α δ : ℝ} (hδ : 0 ≤ δ)
    (hdensity : α * Fintype.card I ≤ (H.card : ℝ))
    (hlarge : ∀ i ∈ H, δ ≤ f i) : α * δ ≤ 𝔼 i, f i := by
  classical
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hindicator : (𝔼 i : I, if i ∈ H then δ else 0) =
      (H.card : ℝ) * δ / Fintype.card I := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  calc
    _ ≤ (H.card : ℝ) * δ / Fintype.card I := by
      apply (le_div_iff₀ hcard).mpr
      nlinarith [mul_le_mul_of_nonneg_right hdensity hδ]
    _ = _ := hindicator.symm
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro i _
      split_ifs with hi
      · exact hlarge i hi
      · exact hf i

theorem exists_quadratic_primitive_correlation_large_modulus :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hintegrate⟩ := exists_quadratic_original_integration
  obtain ⟨B, _, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  obtain ⟨D, _, hprimitive⟩ :=
    NativeMultidegreeNilcharacter.exists_quadratic_primitive_niltest_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := 3 * (U + 1)
  let E := 2 * U + 3 * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 2 * U + 2 + 3 * R + T
  let F := (V + Polynomial.C B) ^ B
  let G := (R + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V + F + G)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := 3 * (u + 1)
  let e := 2 * u + 3 * r + 4
  let t := (p + e + A) ^ A
  let v := 2 * u + 2 + 3 * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v + (v + B) ^ B + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, F, G, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have hF : 0 ≤ (v + B) ^ B := by positivity
  have hG : 0 ≤ (r + D) ^ D := by positivity
  have htC : t ≤ (p + C) ^ C := by linarith
  have hFC : (v + B) ^ B ≤ (p + C) ^ C := by linarith
  have hGC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, H, _hH, hdense, M, i, hderiv, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  let W := M.quadraticRoot
  have hroot : tensorPowerBudget 2 q ≤ r := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat, show (2 : ℝ) + 1 = 3 by norm_num]
    dsimp only [r]
    linarith
  have hroot0 : 0 ≤ tensorPowerBudget 2 q := by
    unfold tensorPowerBudget
    positivity
  have hdim : (W.outputDim : ℝ) ≤ Real.exp r :=
    W.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hdim3 : (W.outputDim : ℝ) ^ 3 ≤ Real.exp (3 * r) := by
    calc
      _ ≤ Real.exp r ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hdim 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  let J := (Fin W.outputDim × Fin W.outputDim) × Fin W.outputDim
  let z (ac : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] *
      star (K ac.1 i ac.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp (3 * r) := by
    have hcount : (Fintype.card J : ℝ) = (W.outputDim : ℝ) ^ 3 := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ring
    rw [hcount]
    exact hdim3
  have hmass : Real.exp (-(2 * u)) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖ := by
    have hh := dense_set_mean_lower_bound H
      (fun h : ZMod N => ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-q))
      (by simpa only [ZMod.card] using hdense) hderiv
    have heq : Real.exp (-q) * Real.exp (-q) = Real.exp (-(2 * q)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by dsimp [u]; linarith)).trans hh
  have htransfer := M.original_diagonal_row_correlation_bound i f hf
    (fun a c => K a i c) (fun a c => herr a i c)
  change _ ≤ (∑ ac : J, z ac) + (W.outputDim : ℝ) ^ 3 * Real.exp (-e) at htransfer
  let δ := Real.exp (-(2 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (W.outputDim : ℝ) ^ 3 * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp (3 * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hdim3 (Real.exp_nonneg _)
      _ = Real.exp (-(2 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(2 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ ac : J, z ac := by linarith
  obtain ⟨ac, hac⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have hac' : Real.exp (-(2 * u + 2 + 3 * r)) ≤ z ac := by
    have heq : δ / Real.exp (3 * r) = Real.exp (-(2 * u + 2 + 3 * r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hac
  let expansion := Classical.choice (hK ac.1 i ac.2)
  obtain ⟨j, hj⟩ := expansion.select_mean_row_correlation
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n : ZMod N => multiplicativeDerivative f h n *
      W.cyclicDiagonalDerivative ac.1 ![h, n]) (Real.exp_pos _) hac'
  let f₀ (n : ZMod N) := f n * W.eval ac.1.1 (fun _ => (n.val : ℤ))
  let f₁ (n : ZMod N) := f n * W.eval ac.1.2 (fun _ => (n.val : ℤ))
  have hf₀ (n : ZMod N) : ‖f₀ n‖ ≤ 1 := by
    dsimp only [f₀]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hf₁ (n : ZMod N) : ‖f₁ n‖ ≤ 1 := by
    dsimp only [f₁]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)
  have hid (h n : ZMod N) :
      multiplicativeDerivative f h n * W.cyclicDiagonalDerivative ac.1 ![h, n] =
        f₀ n * star (f₁ (n + h)) := by
    simp only [multiplicativeDerivative, NativeMultidegreeNilcharacter.cyclicDiagonalDerivative,
      Matrix.cons_val_zero, Matrix.cons_val_one, f₀, f₁, star_mul]
    rw [add_comm h n]
    ring
  have htest : Real.exp (-v) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f₀ n * star (f₁ (n + h)) *
        star ((expansion.test j).eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t = Real.exp (-v) := by
      rw [← Real.exp_sub]
      congr 1
      dsimp [v]
      ring
    change Real.exp (-(2 * u + 2 + 3 * r)) / Real.exp t ≤ _ at hj
    simpa only [heq, hid] using hj
  obtain ⟨χ, hχ⟩ := hfourier (expansion.model j) hv (expansion.test j)
    ((expansion.complexity j).mono (by dsimp [v]; linarith)) f₀ f₁ hf₀ hf₁ htest
  let g (n : ZMod N) := star (W.eval ac.1.2 (fun _ => (n.val : ℤ))) * χ n
  have hg : g ∈ nativeCyclicFunctions 2 N ((p + C) ^ C) := by
    obtain ⟨model⟩ := hprimitive hroot0 W ac.1.2 χ
    have hcost : (tensorPowerBudget 2 q + D) ^ D ≤ (p + C) ^ C :=
      (pow_le_pow_left₀ (by positivity) (add_le_add hroot le_rfl) D).trans hGC
    exact ⟨{ model with complexity := model.complexity.mono hcost }⟩
  refine ⟨g, hg, (Real.exp_le_exp.mpr (neg_le_neg hFC)).trans ?_⟩
  have heq : finiteFourierCoeff f₁ χ = 𝔼 n, f n * star (g n) := by
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    simp only [f₁, g, star_mul, star_star]
    ring
  rwa [heq] at hχ

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_two : ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse 2 C := by
  obtain ⟨A, _, hlarge⟩ := exists_quadratic_primitive_correlation_large_modulus
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 8 * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 8 * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨model⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨model⟩, hcorr⟩ :=
      exists_quadratic_small_modulus_correlation (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : 8 * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ model with complexity := model.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_unit_row_family_with_differences (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → ∀ (F : H → ZMod N → ℂ) (R : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖) →
      ∃ g : H → (Unit → ℤ) → ℂ,
        (∀ h x, ‖g h x‖ ≤ 1) ∧
        (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (g h))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) ∧
        ∀ {e : ℝ}, 0 ≤ e → Real.exp (e + 16) ≤ (N : ℝ) →
          ∀ (h : H) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
            Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
            (𝔼 n : ZMod N,
              ‖g h (fun _ => (n.val : ℤ)) * star (g h (fun _ => ((n + k).val : ℤ))) -
                K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hmodel⟩ := exists_unit_row_model_with_differences s hs
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 2
  let U := (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + U + 2)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F R hF hR hE hcorr
  classical
  let t := p + 2
  let a := (t + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : t + a + 2 ≤ (p + C) ^ C := by
    simpa [X, T, U, t, a, Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have htaC : t + a ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  have hcost (e : ℝ) (he : 0 ≤ e) : (t + e + A) ^ A ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have heq : t + e + A = p + e + 2 + A := by dsimp [t]; ring
    rw [heq]
    linarith
  have htwo' (e : ℝ) (he : 0 ≤ e) : 2 ≤ (p + e + C) ^ C := by
    have hh : (p + e + 2) + (p + e + 2 + A) ^ A + 2 ≤ (p + e + C) ^ C := by
      simpa [X, T, U, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
    have hpow : 0 ≤ (p + e + 2 + A) ^ A := by positivity
    linarith
  let c (h : H) := ‖𝔼 n : ZMod N, F h n * star (R h (fun _ => (n.val : ℤ)))‖
  have hcap (h : H) : c h ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set c (Real.exp_nonneg (-p)) hcap hcorr
  have hhalf : Real.exp (-t) ≤ Real.exp (-p) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hgood (h : H) (hh : h ∈ S) :=
    hmodel ht (F h) (R h) (hF h) ⟨(Classical.choice (hE h)).mono hpt⟩
      (hhalf.trans (hlarge h hh))
  let g₀ (h : H) (hh : h ∈ S) := Classical.choose (hgood h hh)
  have hg₀ (h : H) (hh : h ∈ S) := Classical.choose_spec (hgood h hh)
  let g : H → (Unit → ℤ) → ℂ := fun h => if hh : h ∈ S then g₀ h hh else fun _ => 1
  have hg (h : H) (hh : h ∈ S) : g h = g₀ h hh := dite_eq_left hh
  have hgnot (h : H) (hh : h ∉ S) : g h = fun _ => 1 := dite_eq_right hh
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro h x
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact (hg₀ h hh).1 x
    · rw [hgnot h hh]
      simp
  · intro h
    by_cases hh : h ∈ S
    · rw [hg h hh]
      exact ⟨(Classical.choice (hg₀ h hh).2.1).mono haC⟩
    · rw [hgnot h hh]
      exact ⟨NativeIntegerExpansion.constOne _ _ htwo⟩
  · have hmass := dense_set_mean_lower_bound S
      (fun h => ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖)
      (fun _ => norm_nonneg _) (Real.exp_nonneg (-a))
      ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) (by
        intro h hh
        rw [hg h hh]
        exact (hg₀ h hh).2.2.1)
    apply (Real.exp_le_exp.mpr (neg_le_neg htaC)).trans
    have heq : Real.exp (-(t + a)) = Real.exp (-t) * Real.exp (-a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rwa [heq]
  · intro e he hN h k
    by_cases hh : h ∈ S
    · obtain ⟨K, ⟨E⟩, herr⟩ := (hg₀ h hh).2.2.2 he hN k
      refine ⟨K, ⟨E.mono (hcost e he)⟩, ?_⟩
      simpa only [hg h hh] using herr
    · refine ⟨fun _ => 1, ⟨NativeIntegerExpansion.constOne _ _ (htwo' e he)⟩, ?_⟩
      simp only [hgnot h hh, star_one, mul_one, sub_self, norm_zero, Finset.expect_const_zero]
      exact Real.exp_nonneg _

end Erdos3

end

section

namespace Erdos3

theorem exists_native_mixed_from_inverse {s A : ℕ} (hs : 2 ≤ s)
    (hI : CyclicNativeInverse s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeMixedCorrelation s N ((p + C) ^ C) f) := by
  obtain ⟨B, _, hinitial⟩ := exists_initial_native_correlation_structure hI
  obtain ⟨D, _, heliminate⟩ := exists_native_rank_elimination s hs s
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : q + (q + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (q + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hinitial hp f hf hGowers
  obtain ⟨V⟩ := heliminate W hf ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨V.mono hcost⟩

theorem exists_cubic_native_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      Nonempty (NativeMixedCorrelation 2 N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hI⟩ := exists_cyclicNativeInverse_two
  exact exists_native_mixed_from_inverse (by omega : 2 ≤ 2) hI

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_residual_row_differences_degree (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 3) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (F : ZMod N → ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 2) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        (F h n * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
      ∃ J : ZMod N → ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) ((p + C) ^ C) (K k))) ∧
        (∀ k h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) ((p + C) ^ C) (J k h))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
            star (J k h (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 3)
  obtain ⟨B, _, hrows⟩ := exists_unit_row_family_with_differences (s + 1) (by omega)
  obtain ⟨D₀, _, hcyclic⟩ :=
    UnitVerticalObservable.exists_cyclic_second_difference_models_degree (s + 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let T₀ := X + Q + 4
  let V₀ := (T₀ + Polynomial.C B) ^ B
  let E₁ := 2 * V₀ + 4
  let A₀ := (Q + E₁ + Polynomial.C D₀) ^ D₀
  let E₂ := E₁ + 2 * A₀
  let B₀ := (T₀ + E₂ + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (A₀ + B₀ + 2 * V₀ + E₂ + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN F R hF hR hRE hcorr
  classical
  let q := (p + A) ^ A
  let t := p + q + 4
  let v := (t + B) ^ B
  let e₁ := 2 * v + 4
  let a := (q + e₁ + D₀) ^ D₀
  let e₂ := e₁ + 2 * a
  let b := (t + e₂ + B) ^ B
  let z := 2 * v + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have he₁ : 0 ≤ e₁ := by dsimp [e₁]; linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he₂ : 0 ≤ e₂ := by dsimp [e₂]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hsum : a + b + 2 * v + e₂ + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, T₀, V₀, E₁, A₀, E₂, B₀, q, t, v, e₁, a, e₂, b,
      Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := by linarith
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hzC : z ≤ (p + C) ^ C := by dsimp [z]; linarith
  have hN₁ : Real.exp (e₁ + 16) ≤ (N : ℝ) := by
    apply (Real.exp_le_exp.mpr ?_).trans hN
    dsimp [e₂] at hsum
    linarith
  have hN₂ : Real.exp (e₂ + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
    (fun h n => F h n * star (R h (fun _ => (n.val : ℤ)))) (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hR h n)) hcorr
  let u (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hu (h n : ZMod N) : ‖u h n‖ ≤ 1 := (V.test T.orbit 0).norm_eval_le _
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hrowcorr : Real.exp (-t) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      (F h n * star (u h n)) * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hqt)).trans
    apply hVcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨G, hG, _, hGcorr, hGdiff⟩ := hrows ht
    (fun h n => F h n * star (u h n)) R (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hF h n)).trans (hu h n)) hR
    (fun h => ⟨(Classical.choice (hRE h)).mono hpt⟩) hrowcorr
  have hbase : Real.exp (-v) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (u h n * G h (fun _ => (n.val : ℤ)))‖) := by
    simpa only [star_mul, mul_comm, mul_left_comm, mul_assoc] using hGcorr
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) a K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e₁) :=
    hcyclic D V T.orbit hq hD hcard he₁ hN₁ 0 0 k
  choose K hK herrK using hmodels
  have hrowmodels (k h : ZMod N) : ∃ J : (Unit → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) b J) ∧
      (𝔼 n : ZMod N,
        ‖G h (fun _ => (n.val : ℤ)) * star (G h (fun _ => ((n + k).val : ℤ))) -
          J (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e₂) :=
    hGdiff he₂ hN₂ h k
  choose J hJ herrJ using hrowmodels
  have hd := mean_row_correlation_sq_le_product_derivatives F u
    (fun h n => G h (fun _ => (n.val : ℤ)))
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)])
    (fun k h n => J k h (fun _ => (n.val : ℤ)))
    (B := Real.exp (2 * a)) (ε := Real.exp (-e₁)) (δ := Real.exp (-e₂))
    hF (fun h n => hG h _) (Real.exp_nonneg _) (by
      intro k h n
      exact (Classical.choice (hK k)).norm_eval_le _) (by
      intro k h
      simpa only [u, multiplicativeDerivative, cyclicSecondDifference] using herrK k h.val) (by
      intro k h
      simpa only [multiplicativeDerivative] using herrJ k h)
  have hlarge : Real.exp (-(2 * v)) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      multiplicativeDerivative (F h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)]) *
        star (J k h (fun _ => (n.val : ℤ)))‖) +
          (Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂)) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-v)) hbase 2).trans hd
    have hexp : Real.exp (-v) ^ 2 = Real.exp (-(2 * v)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [hexp, star_mul, mul_comm, mul_left_comm, mul_assoc] using hsquare
  have herror : Real.exp (-e₁) + Real.exp (2 * a) * Real.exp (-e₂) ≤ Real.exp (-z) := by
    have hmul : Real.exp (2 * a) * Real.exp (-e₂) = Real.exp (-e₁) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [e₂]
      ring
    rw [hmul]
    calc
      _ = 2 * Real.exp (-e₁) := by ring
      _ ≤ Real.exp 2 * Real.exp (-e₁) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e₁, z]; ring
  have htwo : 2 * Real.exp (-z) ≤ Real.exp (-(2 * v)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-z) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [z]; ring
  refine ⟨K, J, fun k => ⟨(Classical.choice (hK k)).mono haC⟩,
    fun k h => ⟨(Classical.choice (hJ k h)).mono hbC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg hzC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
