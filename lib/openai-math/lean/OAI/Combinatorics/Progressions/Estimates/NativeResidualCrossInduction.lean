/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.CrossRowCharacterDifference
import OAI.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles
import OAI.Combinatorics.Progressions.Fourier.StepOneFamilyFourier

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_fourierCoeff_le_gowers_two {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → ℂ) (χ : AddChar G ℂ) : ‖finiteFourierCoeff f χ‖ ≤ gowersNorm 2 f := by
  classical
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (gowersNorm_nonneg 1 f)
    (by norm_num : (4 : ℕ) ≠ 0)).mp
  rw [gowersNorm_two_fourier]
  exact Finset.single_le_sum (fun ψ _ => pow_nonneg (norm_nonneg _) 4) (Finset.mem_univ χ)

theorem mean_derivative_gowers_power_le {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) :
    (𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) ^ (2 ^ (s + 1)) ≤
      gowersNorm (s + 2) f ^ (2 ^ (s + 2)) := by
  rw [gowersNorm_derivative]
  exact expect_pow_two_pow_le (s + 1) _ (fun k => gowersNorm_nonneg s _)

theorem exp_le_gowers_of_mean_derivative {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) {p : ℝ} (hp : 0 ≤ p)
    (hcorr : Real.exp (-p) ≤ 𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) :
    Real.exp (-p) ≤ gowersNorm (s + 2) f := by
  have hexp : Real.exp (-p) ^ (2 ^ (s + 2)) ≤ Real.exp (-p) ^ (2 ^ (s + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    push_cast
    nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 2 ^ (s + 1) by positivity)]
  have hpower := hexp.trans ((pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans
    (mean_derivative_gowers_power_le s f))
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) (gowersNorm_nonneg (s + 1) f)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp hpower

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ f g : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (f n * star (g (n + h))) * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

def NativeCharacterCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g

theorem exists_native_cross_row_detection_one :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection 1 C := by
  obtain ⟨C, hC, hfourier⟩ := exists_fourier_of_stepOne_cross_correlation
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ _hN f g hf hg hcorr
  obtain ⟨χ, hχ⟩ := hfourier D hp T hT f g hf hg hcorr
  exact hχ.trans (norm_fourierCoeff_le_gowers_two g χ)

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_native_cross_family {s A : ℕ} (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s p (K i))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 1) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K ha hb hK hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    (a i n * star (b i (n + h))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      ((Classical.choice (hK i)).norm_eval_le _)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 1) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (ha i) (hb i) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 1) (b i))
    (fun i => gowersNorm_nonneg s (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_characters_of_stepOne_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H : Type*} [Fintype H] [Nonempty H] {N : ℕ} [NeZero N] {p : ℝ},
      0 ≤ p → ∀ (F : H → ZMod N → ℂ) (g : H → (Unit → ℤ) → ℂ),
      (∀ h n, ‖F h n‖ ≤ Real.exp p) →
      (∀ h (n : ZMod N), ‖g h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 p (g h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖) →
      ∃ χ : H → AddChar (ZMod N) ℂ,
        Real.exp (-((p + C) ^ C)) ≤ 𝔼 h, ‖finiteFourierCoeff (F h) (χ h)‖ := by
  obtain ⟨A, _, hfourier⟩ := exists_fourier_of_stepOne_expansion
  let X : Polynomial ℕ := Polynomial.X
  let T := 2 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro H _ _ N _ p hp F g hF hg hE hcorr
  classical
  let F' : H → ZMod N → ℂ := fun h n => (Real.exp (-p) : ℂ) * F h n
  let t := 2 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hF' (h : H) (n : ZMod N) : ‖F' h n‖ ≤ 1 := by
    simp only [F', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-p) * Real.exp p := mul_le_mul_of_nonneg_left (hF h n) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hscale (h : H) :
      ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ =
        Real.exp (-p) * ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    have heq : (𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))) =
        (Real.exp (-p) : ℂ) * (𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hmean : Real.exp (-(2 * p)) ≤
      𝔼 h, ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    simp only [hscale, ← Finset.mul_expect]
    have heq : Real.exp (-(2 * p)) = Real.exp (-p) * Real.exp (-p) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hcap (h : H) : ‖𝔼 n : ZMod N, F' h n * star (g h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hF' h n)).trans (hg h n)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set _ (Real.exp_nonneg (-(2 * p))) hcap hmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(2 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hcharacter (h : H) (hh : h ∈ S) : ∃ χ : AddChar (ZMod N) ℂ,
      Real.exp (-((t + A) ^ A)) ≤ ‖finiteFourierCoeff (F' h) χ‖ :=
    hfourier ht ((Classical.choice (hE h)).mono hpt) (F' h) (hF' h) (hhalf.trans (hlarge h hh))
  let χ (h : H) : AddChar (ZMod N) ℂ := if hh : h ∈ S then Classical.choose (hcharacter h hh) else 1
  have hmass := dense_set_mean_lower_bound S (fun h => ‖finiteFourierCoeff (F' h) (χ h)‖)
    (fun _ => norm_nonneg _) (Real.exp_nonneg (-((t + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS)
    (fun h hh => by simpa only [χ, dite_eq_left hh] using Classical.choose_spec (hcharacter h hh))
  have hmono (h : H) : ‖finiteFourierCoeff (F' h) (χ h)‖ ≤ ‖finiteFourierCoeff (F h) (χ h)‖ := by
    have heq : finiteFourierCoeff (F' h) (χ h) = (Real.exp (-p) : ℂ) * finiteFourierCoeff (F h) (χ h) := by
      unfold finiteFourierCoeff
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      dsimp [F']
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hp))
  have hcost : t + (t + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨χ, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans ?_⟩
  have heq : Real.exp (-(t + (t + A) ^ A)) = Real.exp (-t) * Real.exp (-((t + A) ^ A)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [heq]
  exact hmass.trans (Finset.expect_le_expect (fun h _ => hmono h))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_character_cross_row_step {s A : ℕ} (hs : 1 ≤ s)
    (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_differenced_rows_degree s hs
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g χ hf hg hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, hK, hKcorr⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (characterCrossRow f g χ)
    (characterCrossRow_norm f g χ hf hg) hcorr
  have hclean : Real.exp (-u) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [characterCrossRow_derivative_correlation_norm] using hKcorr
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (fun k => multiplicativeDerivative f k) (fun k => multiplicativeDerivative g k) K
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative s g hv hmean)

theorem exists_native_cross_row_detection (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection s C := by
  have hall : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection (n + 1) C := by
    intro n
    induction n with
    | zero => exact exists_native_cross_row_detection_one
    | succ n ih =>
        obtain ⟨A, _, hdetect⟩ := ih
        obtain ⟨C, hC, hstep⟩ := exists_native_character_cross_row_step
          (by omega : 1 ≤ n + 1) hdetect
        refine ⟨C, hC, ?_⟩
        intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g hf hg hcorr
        apply hstep M T hp hT hN f g (fun _ => 1) hf hg
        simpa [characterCrossRow] using hcorr
  cases s with
  | zero => omega
  | succ n => exact hall n

theorem exists_native_character_cross_row_detection (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection s C := by
  cases s with
  | zero => omega
  | succ n =>
      have hn : 1 ≤ n := by omega
      obtain ⟨A, _, hdetect⟩ := exists_native_cross_row_detection n hn
      exact exists_native_character_cross_row_step hn hdetect

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def NativeResidualCrossRowDetection (s C : ℕ) : Prop :=
  ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 2) d)
    (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
    ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
    ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
    (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
    (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
    (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R h))) →
    Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
        star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
    Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 3) g

theorem exists_native_residual_cross_row_detection_zero :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection 0 C := by
  obtain ⟨A, _, hlinear⟩ := exists_characters_of_stepOne_rows
  obtain ⟨B, _, hdetect⟩ := exists_native_character_cross_row_detection 2 (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let q := p + (p + A) ^ A
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hscore : (p + A) ^ A ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let F (h n : ZMod N) := (f n * star (g (n + h))) *
    star (T.eval ![(h.val : ℤ), (n.val : ℤ)])
  have hF (h n : ZMod N) : ‖F h n‖ ≤ Real.exp p := by
    have hcross : ‖f n * star (g (n + h))‖ ≤ 1 := by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))
    change ‖(f n * star (g (n + h))) * star (T.eval _)‖ ≤ _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) hcross).trans (T.eval_budget hT _)
  have hFcorr : Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      F h n * star (R h (fun _ => (n.val : ℤ)))‖) := by
    apply hcorr.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    apply Finset.expect_congr rfl
    intro n _
    exact mul_right_comm _ _ _
  obtain ⟨χ, hχ⟩ := hlinear hp F R hF hR hRE hFcorr
  have hchars : Real.exp (-q) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
      characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hscore)).trans
    apply hχ.trans_eq
    apply Finset.expect_congr rfl
    intro h _
    congr 1
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    dsimp [F, characterCrossRow]
    ring
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hdetect D T hq (hT.mono hpq) ((Real.exp_le_exp.mpr hresult).trans hN)
      f g χ hf hg hchars)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_gowers_of_bounded_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i h (n : ZMod N), ‖R i h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  let X : Polynomial ℕ := Polynomial.X
  let T := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (T + X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hR hK hRE hcorr
  classical
  let c (i : I) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
      star (K i ![(h.val : ℤ), (n.val : ℤ)])‖
  let z (i : I) := Real.exp (-(2 * p)) * c i
  let t := 3 * p + 2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hc0 (i : I) : 0 ≤ c i := Finset.expect_nonneg (fun _ _ => norm_nonneg _)
  have hunit (i : I) (h n : ZMod N) :
      ‖(a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hR i h n)
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha i n)).trans (hb i (n + h))
  have hcap (i : I) : c i ≤ Real.exp (2 * p) := by
    apply Finset.expect_le Finset.univ_nonempty
    intro h _
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hunit i h n)).trans
      ((Classical.choice (hK i)).norm_eval_le _)
  have hzcap (i : I) : z i ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left (hcap i) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * p)) ≤ 𝔼 i, z i := by
    change Real.exp (-(3 * p)) ≤ 𝔼 i, Real.exp (-(2 * p)) * c i
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  obtain ⟨S, hS, hlarge⟩ := exists_dense_level_set z (Real.exp_nonneg (-(3 * p))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * p)) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      _ ≤ Real.exp (-t) * Real.exp 2 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [t]; ring
  have hzle (i : I) : z i ≤ c i := mul_le_of_le_one_left (hc0 i)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hcost : t + (t + p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hN' : Real.exp ((t + p + A) ^ A) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith)).trans hN
  have hnorm (i : I) (hi : i ∈ S) :
      Real.exp (-((t + p + A) ^ A)) ≤ gowersNorm (s + 3) (b i) := by
    have hc : Real.exp (-t) ≤ c i := hhalf.trans ((hlarge i hi).trans (hzle i))
    obtain ⟨V⟩ := NativeMeanRowCorrelation.exists_of_expansion
      (Classical.choice (hK i)) ht hc
    exact hdetect V.model V.test (by linarith : 0 ≤ t + p) V.complexity hN'
      (a i) (b i) (R i) (ha i) (hb i) (hR i)
      (fun h => ⟨(Classical.choice (hRE i h)).mono (by linarith)⟩) V.correlation
  have hmass := dense_set_mean_lower_bound S (fun i => gowersNorm (s + 3) (b i))
    (fun i => gowersNorm_nonneg (s + 2) (b i)) (Real.exp_nonneg (-((t + p + A) ^ A)))
    ((mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg _)).trans hS) hnorm
  apply (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
  have heq : Real.exp (-(t + (t + p + A) ^ A)) =
      Real.exp (-t) * Real.exp (-((t + p + A) ^ A)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [heq]

theorem exists_gowers_of_native_residual_cross_family {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} [Fintype I] [Nonempty I] {N : ℕ} [NeZero N]
      {p : ℝ}, 0 ≤ p → Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (a b : I → ZMod N → ℂ) (K : I → (Fin 2 → ℤ) → ℂ)
        (R : I → ZMod N → (Unit → ℤ) → ℂ),
      (∀ i n, ‖a i n‖ ≤ 1) → (∀ i n, ‖b i n‖ ≤ 1) →
      (∀ i, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) (s + 2) p (K i))) →
      (∀ i h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) p (R i h))) →
      Real.exp (-p) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        ((a i n * star (b i (n + h))) * star (R i h (fun _ => (n.val : ℤ)))) *
          star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ 𝔼 i, gowersNorm (s + 3) (b i) := by
  obtain ⟨B, _, hfamily⟩ := exists_gowers_of_bounded_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let Q := 3 * X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro I _ _ N _ p hp hN a b K R ha hb hK hRE hcorr
  classical
  let q := 3 * p + 2
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hresult : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  let R₀ : I → ZMod N → (Unit → ℤ) → ℂ := fun i h x =>
    (Real.exp (-(2 * p)) : ℂ) * R i h x
  have hR₀ (i : I) (h n : ZMod N) : ‖R₀ i h (fun _ => (n.val : ℤ))‖ ≤ 1 := by
    simp only [R₀, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(2 * p)) * Real.exp (2 * p) :=
        mul_le_mul_of_nonneg_left ((Classical.choice (hRE i h)).norm_eval_le _)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hR₀E (i : I) (h : ZMod N) :
      Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s + 1) q (R₀ i h)) := by
    apply Nonempty.intro
    apply NativeIntegerExpansion.mono _ hpq
    apply (Classical.choice (hRE i h)).scaleNormLeOne
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr (by linarith : -(2 * p) ≤ 0))
  have hscale (i : I) (h : ZMod N) :
      ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ =
      Real.exp (-(2 * p)) * ‖𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    have heq : (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R₀ i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) =
      (Real.exp (-(2 * p)) : ℂ) * (𝔼 n : ZMod N, ((a i n * star (b i (n + h))) *
        star (R i h (fun _ => (n.val : ℤ)))) * star (K i ![(h.val : ℤ), (n.val : ℤ)])) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [R₀, star_mul]
      rw [show star ((Real.exp (-(2 * p))) : ℂ) = (Real.exp (-(2 * p)) : ℂ) from
        Complex.conj_ofReal _]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hscaled : Real.exp (-q) ≤ (𝔼 i, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      ((a i n * star (b i (n + h))) * star (R₀ i h (fun _ => (n.val : ℤ)))) *
        star (K i ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simp only [hscale, ← Finset.mul_expect]
    apply (Real.exp_le_exp.mpr (show -q ≤ -(3 * p) by dsimp [q]; linarith)).trans
    have heq : Real.exp (-(3 * p)) = Real.exp (-(2 * p)) * Real.exp (-p) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  exact (Real.exp_le_exp.mpr (neg_le_neg hresult)).trans
    (hfamily hq ((Real.exp_le_exp.mpr hresult).trans hN) a b K R₀ ha hb hR₀
      (fun i => ⟨(Classical.choice (hK i)).mono hpq⟩) hR₀E hscaled)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_residual_cross_row_step {s A : ℕ}
    (hdetect : NativeResidualCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_residual_row_differences_degree s
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_residual_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g R hf hg hR hRE hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, J, hK, hJ, hdiff⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (fun h n => f n * star (g (n + h))) R
    (by
      intro h n
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (hg (n + h))) hR hRE hcorr
  have hderiv (h k n : ZMod N) :
      multiplicativeDerivative (fun n => f n * star (g (n + h))) k n =
        multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h)) := by
    simp only [multiplicativeDerivative, star_mul, star_star]
    rw [add_right_comm n k h]
    ring
  have hclean : Real.exp (-u) ≤ (𝔼 k, 𝔼 h, ‖𝔼 n : ZMod N,
      ((multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (J k h (fun _ => (n.val : ℤ)))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [hderiv, mul_comm, mul_left_comm, mul_assoc] using hdiff
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (multiplicativeDerivative f) (multiplicativeDerivative g) K J
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hJ hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative (s + 2) g hv hmean)

theorem exists_native_residual_cross_row_detection (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeResidualCrossRowDetection s C := by
  induction s with
  | zero => exact exists_native_residual_cross_row_detection_zero
  | succ s ih =>
      obtain ⟨A, _, hdetect⟩ := ih
      exact exists_native_residual_cross_row_step hdetect

theorem RationalFilteredNilmanifold.exists_gowers_of_residual_cross_rows (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (R : ZMod N → (Unit → ℤ) → ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      (∀ h (n : ZMod N), ‖R h (fun _ => (n.val : ℤ))‖ ≤ 1) →
      (∀ h, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) p (R h))) →
      Real.exp (-p) ≤ (𝔼 h, ‖𝔼 n : ZMod N,
        ((f n * star (g (n + h))) * star (R h (fun _ => (n.val : ℤ)))) *
          star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm (s + 1) g := by
  cases s with
  | zero => omega
  | succ s =>
      cases s with
      | zero => omega
      | succ s => exact exists_native_residual_cross_row_detection s

end Erdos3

end

end OAI
