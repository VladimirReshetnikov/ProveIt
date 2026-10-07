import OAI.Combinatorics.Progressions.Estimates.LinearDerivativeRemoval
import OAI.Combinatorics.Progressions.Lattices.IntegerSectionFactorization

namespace OAI

section

open scoped Matrix NNReal

namespace Erdos3

theorem real_matrix_image_section_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ) (hS : A * S * A = A)
    (y : ι → ℝ) (hy : y ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ)))) :
    (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ y) = y := by
  obtain ⟨x, rfl⟩ := hy
  change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
    (Matrix.of (fun i j => (S i j : ℝ)) *ᵥ
      (Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x)) =
    Matrix.of (fun i j => (A i j : ℝ)) *ᵥ x
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, real_matrix_image_section A S hS]

theorem norm_matrix_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : Matrix ι κ ℝ) (H : ℝ≥0) (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) :
    ‖Q *ᵥ x‖ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_matrix_mulVec_le Q H hQ x i

theorem real_image_section_norm_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) (x : ι → ℝ) :
    ‖(fun i j => (S i j : ℝ)) *ᵥ x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ := by
  have hnorm := norm_matrix_mulVec_le (fun i j => (S i j : ℝ))
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le) x
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH))
    (norm_nonneg _))

theorem real_image_section_denominator_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (S : Matrix κ ι ℚ) (H l : ℕ)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ((matrixDenominator S * l : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 36) := by
  have hpq : p ≤ (p + 2) ^ 7 := le_power_budget hp (by decide)
  have h := matrixDenominator_allowance_le_exp S l (rationalKernelHeight (Fintype.card ι) H)
    hS (by positivity : 0 ≤ (p + 2) ^ 7) (hκ.trans hpq) (hι.trans hpq)
    (rationalKernelHeight_le_budget (Fintype.card ι) H hp hι hH)
    (hl.trans (Real.exp_le_exp.mpr hpq))
  rw [Nat.mul_comm] at h
  exact h.trans (Real.exp_le_exp.mpr (shifted_power_budget_le hp 7 4))

end Erdos3

end

section

open scoped Matrix NNReal

namespace Erdos3

theorem controlled_real_column_span_separation
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / monomialScale T α)
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  obtain ⟨Q, hQ, hker⟩ := exists_real_span_defining_matrix A hH hA
  have hscale : Real.exp (separationBudget p) ≤ monomialScale T α :=
    le_monomialScale_of_ne_zero T (Real.one_le_exp (separationBudget_nonneg hp)) hT hα
  have hasmall : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) :=
    ha.trans (div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) hscale)
  have hden := imageDefiningDenominator_le_exp Q (Fintype.card κ) H l hQ hp hκ hι hHp hlp
  have hrow := imageDefiningRow_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hHp
  have hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card ι : ℝ) + 1) *
        ((imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ) + 1)) *
      dist b (a + b) < 1 := by
    have he : b - (a + b) = -a := by abel
    rw [dist_eq_norm, he, norm_neg]
    exact separationBudget_small hden hrow (by positivity) (norm_nonneg _) hasmall
  have hsumker : (fun i j => (Q i j : ℝ)) *ᵥ (a + b) = 0 := by
    have h := (real_column_span_mem_iff A (a + b)).mp hsum
    rw [← hker] at h
    exact h
  have hbker := rational_matrix_kernel_separation Q
    (imageDefiningHeight (Fintype.card κ) (Fintype.card ι) H : ℝ≥0)
    (fun i j => (hQ i j).abs_real_le) l hl b (a + b) hb hsumker hnear
  have hbrange : b ∈ LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
    rw [← hker]
    exact hbker
  have hbspan := (real_column_span_mem_iff A b).mpr hbrange
  refine ⟨?_, hbspan⟩
  simpa only [add_sub_cancel_right] using
    (Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))).sub_mem hsum hbspan

end Erdos3

end

section

namespace Erdos3

open Polynomial
open scoped Matrix BigOperators

theorem exists_common_site_denominator :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I S : Type*}
    [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (E : Matrix S I ℚ) {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ s i, RationalHeightLE (E s i) H)
    {P : ℝ} (_hP : 0 ≤ P) (_hI : (Fintype.card I : ℝ) ≤ P)
    (_hS : (Fintype.card S : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ i a, |(frequency i a : ℝ)| ≤ C)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (_hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)),
    ∃ b : Matrix S J ℤ, (∀ s a, |(b s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ x : I → U, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
        subspaceArrayFunctional U (fun s a => (b s a : ℝ))
          (matrixModuleAction (fun s i => (E s i : ℝ)) ((q : ℝ)⁻¹ • x)) := by
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + 2) ^ 36 + (X + 2) ^ 7)
  refine ⟨A, hA, ?_⟩
  intro I S _ _ _ _ E H hH hE P hP hI hS hHP
  obtain ⟨T, hT, hTH⟩ := exists_bounded_rational_image_section E hH hE
  have hq : (matrixDenominator T : ℝ) ≤ Real.exp ((P + 2) ^ 36) := by
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hTH hP hS hI hHP
      (by simpa using Real.one_le_exp hP)
  have hK := rationalKernelHeight_le_budget (Fintype.card S) H hP hS hHP
  have hb : 2 * P + (P + 2) ^ 36 + (P + 2) ^ 7 ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  have hseven : 0 ≤ (P + 2) ^ 7 := by positivity
  refine ⟨matrixDenominator T, matrixDenominator_pos T,
    hq.trans (Real.exp_le_exp.mpr (by linarith)), ?_⟩
  intro J _ U frequency C hC hCP hfrequency M hfactor
  refine ⟨sectionIntegerFrequency T frequency, ?_, ?_⟩
  · intro s a
    apply (sectionIntegerFrequency_bound T frequency (Nat.cast_nonneg _) hfrequency
      (fun i s => (hTH i s).abs_real_le) s a).trans
    have hIP : (Fintype.card I : ℝ) ≤ Real.exp P := hI.trans (by linarith [Real.add_one_le_exp P])
    calc
      _ ≤ Real.exp P * Real.exp P * Real.exp ((P + 2) ^ 36) * Real.exp ((P + 2) ^ 7) := by
        gcongr
      _ = Real.exp (2 * P + (P + 2) ^ 36 + (P + 2) ^ 7) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((P + A) ^ A) := Real.exp_le_exp.mpr hb
  · exact subspaceArrayFunctional_integer_section U E T hT frequency M hfactor

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

theorem weighted_matrix_mulVec_bound {ι κ δ : Type*} [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℝ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    (H : ℝ≥0) (hA : ∀ i j, |A i j| ≤ H)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : κ → ℝ) (hx : ∀ j, |x j| ≤ M / W (c j)) (i : ι) :
    |(A *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * M / W (r i) := by
  classical
  have hdiv : 0 ≤ M / W (r i) := div_nonneg hM (hW _).le
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * (M / W (r i)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : r i = c j
      · rw [abs_mul]
        exact mul_le_mul (hA i j) (by simpa only [h] using hx j) (abs_nonneg _) H.coe_nonneg
      · rw [hblock i j h, zero_mul, abs_zero]
        exact mul_nonneg H.coe_nonneg hdiv
    _ = (Fintype.card κ : ℝ) * H * (M / W (r i)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * (M / W (r i)) := by
      gcongr <;> linarith
    _ = _ := by ring

theorem real_image_section_weighted_bound {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (S : Matrix κ ι ℚ) (H : ℕ)
    (hblock : ∀ i j, c i ≠ r j → S i j = 0)
    (hS : ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight (Fintype.card ι) H))
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (W : δ → ℝ) (hW : ∀ d, 0 < W d) {M : ℝ} (hM : 0 ≤ M)
    (x : ι → ℝ) (hx : ∀ j, |x j| ≤ M / W (r j)) (i : κ) :
    |((fun i j => (S i j : ℝ)) *ᵥ x) i| ≤
      Real.exp ((p + 2) ^ 18) * M / W (c i) := by
  have hbound := weighted_matrix_mulVec_bound c r (fun i j => (S i j : ℝ))
    (fun i j h => by rw [hblock i j h, Rat.cast_zero])
    (rationalKernelHeight (Fintype.card ι) H : ℝ≥0) (fun i j => (hS i j).abs_real_le)
    W hW hM x hx i
  have hfac : ((Fintype.card ι : ℝ) + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1) ≤
      (coordinateLipschitzBound (Fintype.card κ) (Fintype.card ι)
        (rationalKernelHeight (Fintype.card ι) H) : ℝ) := by
    change _ ≤ ((Fintype.card κ : ℝ) + Fintype.card ι + 1) *
      ((rationalKernelHeight (Fintype.card ι) H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (hW _).le
  exact mul_le_mul_of_nonneg_right
    (hfac.trans (imageSection_bound_le_exp (Fintype.card κ) (Fintype.card ι) H hp hκ hι hH)) hM

end Erdos3

end

section

open scoped Matrix

namespace Erdos3

theorem exists_controlled_linear_splitting
    {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ), 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (a b : ι → ℝ) (v : κ → ℝ),
      ‖a‖ ≤ Real.exp p / monomialScale T α → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      ‖(fun i j => (S i j : ℝ)) *ᵥ a‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_image_section A hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp, ?_⟩
  intro α hα a b v ha hb hv
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_real_column_span_separation A hH hl hA hp hι hκ
    hHp hlp T hT hα a b ha hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb, ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · calc
      _ ≤ Real.exp ((p + 2) ^ 18) * ‖a‖ := real_image_section_norm_bound S H hSH hp hι hκ hHp a
      _ ≤ Real.exp ((p + 2) ^ 18) * (Real.exp p / monomialScale T α) :=
        mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
      _ = _ := by rw [← mul_div_assoc, ← Real.exp_add]
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a -
        Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb).trans (by abel)

end Erdos3

end

section

namespace Erdos3

section Algebra

variable {R E H : Type*} [Field R] [AddCommGroup E] [Module R E]
  [AddCommGroup H] [Module R H]

theorem horizontal_parts_mem_sum (U K : Submodule R H) (P : E →ₗ[R] H)
    (f : E →ₗ[R] E) (hf : P.comp f = P) (S : K →ₗ[R] E)
    (hS : P.comp S = K.subtype) (y s r : E) (k : K)
    (hsystem : y = s + f r + S k) (hy : P y ∈ U) : P s + P r ∈ U ⊔ K := by
  have he : P y = P s + P r + k.val := by
    rw [hsystem, map_add, map_add]
    rw [show P (f r) = P r from DFunLike.congr_fun hf r,
      show P (S k) = k.val from DFunLike.congr_fun hS k]
  have hmem := (U ⊔ K).sub_mem ((show U ≤ U ⊔ K from le_sup_left) hy)
    ((show K ≤ U ⊔ K from le_sup_right) k.property)
  simpa only [he, add_sub_cancel_right] using hmem

theorem horizontal_absorption_into_subspace (U K : Submodule R H) (P : E →ₗ[R] H)
    (f : E →ₗ[R] E) (hf : P.comp f = P) (S T : K →ₗ[R] E)
    (hST : S = f.comp T) (hS : P.comp S = K.subtype) (hT : P.comp T = K.subtype)
    (y s r : E) (k : K) (hsystem : y = s + f r + S k) (hy : P y ∈ U)
    (hs : P s ∈ U ⊔ K) (hr : P r ∈ U ⊔ K) :
    ∃ ks kr : K,
      P (s - S ks) ∈ U ∧ P (r - T kr) ∈ U ∧ (k + ks + kr).val ∈ U ∧
      y = (s - S ks) + f (r - T kr) + S (k + ks + kr) := by
  obtain ⟨u, hu, ks, hks, hes⟩ := Submodule.mem_sup.mp hs
  obtain ⟨v, hv, kr, hkr, her⟩ := Submodule.mem_sup.mp hr
  let ks' : K := ⟨ks, hks⟩
  let kr' : K := ⟨kr, hkr⟩
  have hparts := horizontal_derivative_absorb P S T K.subtype hS hT s r ks' kr' u v hes.symm her.symm
  have hnew := linear_derivative_absorb f S T hST y s r k ks' kr' hsystem
  refine ⟨ks', kr', hparts.1.symm ▸ hu, hparts.2.symm ▸ hv, ?_, hnew⟩
  have he : P y = u + v + (k + ks' + kr').val := by
    rw [hnew, map_add, map_add,
      show P (f (r - T kr')) = P (r - T kr') from DFunLike.congr_fun hf _,
      hparts.1, hparts.2,
      show P (S (k + ks' + kr')) = (k + ks' + kr').val from DFunLike.congr_fun hS _]
  have hmem := U.sub_mem (U.sub_mem hy hu) hv
  have he' : P y - u - v = (k + ks' + kr').val := by rw [he]; abel
  exact he' ▸ hmem

theorem horizontal_remove_zero (P : E →ₗ[R] H) (a b : E ≃ₗ[R] E)
    (ha : ∀ x, P (a x) = P x) (hb : ∀ x, P (b x) = P x)
    (s r ya yb : E) (hya : P ya = P s) (hyb : P yb = P r) :
    P (a.symm (s - ya)) = 0 ∧ P (b r - yb) = 0 := by
  constructor
  · have he := ha (a.symm (s - ya))
    rw [LinearEquiv.apply_symm_apply] at he
    rw [← he, map_sub, hya, sub_self]
  · rw [map_sub, hb, hyb, sub_self]

theorem horizontal_derivative_of_zero_parts (U K : Submodule R H) (P : E →ₗ[R] H)
    (f : E →ₗ[R] E) (hf : P.comp f = P) (S : K →ₗ[R] E)
    (hS : P.comp S = K.subtype) (y s r : E) (k : K)
    (hsystem : y = s + f r + S k) (hs : P s = 0) (hr : P r = 0) (hk : k.val ∈ U) :
    P y = k.val ∧ P y ∈ U ⊓ K := by
  have he : P y = k.val := by
    rw [hsystem, map_add, map_add, hs,
      show P (f r) = P r from DFunLike.congr_fun hf r, hr,
      show P (S k) = k.val from DFunLike.congr_fun hS k, zero_add, zero_add]
  exact ⟨he, he.symm ▸ ⟨hk, k.property⟩⟩

end Algebra

theorem horizontal_parts_separation {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ)
    (hspan : Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) = U ⊔ K)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (y s r k : ι → ℝ)
    (hsystem : y = s + r + k) (hy : y ∈ U) (hk : k ∈ K)
    (hs : ‖s‖ ≤ Real.exp p / monomialScale T α) (hr : r ∈ realDenominatorGrid l) :
    s ∈ U ⊔ K ∧ r ∈ U ⊔ K := by
  have hsum : s + r ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
    rw [hspan]
    have hmem := (U ⊔ K).sub_mem ((show U ≤ U ⊔ K from le_sup_left) hy)
      ((show K ≤ U ⊔ K from le_sup_right) hk)
    simpa only [hsystem, add_sub_cancel_right] using hmem
  have he := controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp T hT hα s r hs hr hsum
  simpa only [hspan] using he

end Erdos3

end

section

namespace Erdos3

theorem controlled_small_vector_separation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  apply controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp
    (fun _ : Unit => Real.exp (separationBudget p)) (fun _ => le_rfl)
    (α := Finsupp.single () 1) (by simp) a b
  · simpa only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one] using ha
  · exact hb
  · exact hsum

end Erdos3

end

section

namespace Erdos3

variable {σ G E H R : Type*} [Group G] [Field R]
  [AddCommGroup E] [Module R E] [AddCommGroup H] [Module R H]

theorem cocycle_horizontal_normalization
    (ρ : G →* (E ≃ₗ[R] E)) (Y : G → σ → E)
    (hY : ∀ g h i, Y (g * h) i = Y g i + ρ g (Y h i))
    (P : E →ₗ[R] H) (hρ : ∀ g x, P (ρ g x) = P x)
    (U K : Submodule R H) (B a c : G) (S T : K →ₗ[R] E)
    (hST : S = (ρ B).toLinearMap.comp T)
    (hS : P.comp S = K.subtype) (hT : P.comp T = K.subtype)
    (small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, Y B i = small i + ρ B (rational i) + S (k i))
    (ha : ∀ i, P (Y a i) = P (small i)) (hc : ∀ i, P (Y c i) = P (rational i))
    (hk : ∀ i, (k i).val ∈ U) :
    let B' := a⁻¹ * B * c⁻¹
    let S' := (ρ a).symm.toLinearMap.comp S
    let T' := (ρ c).toLinearMap.comp T
    let small' := fun i => (ρ a).symm (small i - Y a i)
    let rational' := fun i => ρ c (rational i) - Y c i
    a * B' * c = B ∧ S' = (ρ B').toLinearMap.comp T' ∧
      P.comp S' = K.subtype ∧ P.comp T' = K.subtype ∧
      ∀ i, Y B' i = small' i + ρ B' (rational' i) + S' (k i) ∧
        P (small' i) = 0 ∧ P (rational' i) = 0 ∧ P (Y B' i) = (k i).val ∧
        P (Y B' i) ∈ U ⊓ K := by
  let B' := a⁻¹ * B * c⁻¹
  let S' := (ρ a).symm.toLinearMap.comp S
  let T' := (ρ c).toLinearMap.comp T
  let small' := fun i => (ρ a).symm (small i - Y a i)
  let rational' := fun i => ρ c (rational i) - Y c i
  have hprod : a * B' * c = B := by dsimp [B']; group
  have haction (x : E) : ρ B x = ρ a (ρ B' (ρ c x)) := by
    rw [← hprod]
    exact linear_action_triple ρ a B' c x
  have hfac : S' = (ρ B').toLinearMap.comp T' :=
    linear_lift_remove (ρ a) (ρ c) (ρ B) (ρ B') haction S T hST
  have hhor := horizontal_lift_remove P (ρ a) (ρ c) (hρ a) (hρ c) S T K.subtype hS hT
  refine ⟨hprod, hfac, hhor.1, hhor.2, fun i => ?_⟩
  have htriple := linear_cocycle_triple ρ (fun g => Y g i)
    (fun g h => hY g h i) a B' c
  rw [hprod] at htriple
  have hnew : Y B' i = small' i + ρ B' (rational' i) + S' (k i) :=
    linear_derivative_remove (ρ a) (ρ c) (ρ B) (ρ B') haction
      (Y B i) (Y a i) (Y B' i) (Y c i) (small i) (rational i) (S (k i)) htriple (hsystem i)
  have hzero := horizontal_remove_zero P (ρ a) (ρ c) (hρ a) (hρ c)
    (small i) (rational i) (Y a i) (Y c i) (ha i) (hc i)
  have hPB : P.comp (ρ B').toLinearMap = P := by
    ext x
    exact hρ B' x
  have hfinal := horizontal_derivative_of_zero_parts U K P (ρ B').toLinearMap hPB S'
    hhor.1 (Y B' i) (small' i) (rational' i) (k i) hnew hzero.1 hzero.2 (hk i)
  exact ⟨hnew, hzero.1, hzero.2, hfinal.1, hfinal.2⟩

end Erdos3

end

end OAI
