/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree
import OAI.Combinatorics.Progressions.Linear.AugmentedMatrixSection

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_defining_matrix
    {ι κ δ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H) :
    ∃ Q : Matrix ι ι ℚ,
      (∀ i j, RationalHeightLE (Q i j)
        (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H)) ∧
      (∀ i j, c i ≠ c j → Q i j = 0) ∧
      ∀ x : ℝ ⊗[ℚ] L,
        (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = 0 ↔ x ∈ U.baseChange ℝ := by
  classical
  let v' := blockSpanningFamily b c v
  let A : Matrix ι (ι × κ) ℚ := fun i z => b.repr (v' z) i
  have hA : ∀ i z, RationalHeightLE (A i z) H :=
    fun i z => blockSpanningFamily_height b c v hH hv z i
  have hAb : ∀ i z, c i ≠ c z.1 → A i z = 0 := by
    intro i z hz
    change b.repr (blockSpanningFamily b c v z) i = 0
    rw [blockSpanningFamily_repr, ite_eq_right hz]
  obtain ⟨Q, hQ, hQb, hker⟩ := exists_real_block_span_defining_matrix c (fun z : ι × κ => c z.1) A hAb hH hA
  refine ⟨Q, ?_, hQb, ?_⟩
  · simpa only [Fintype.card_prod] using hQ
  · intro x
    have hsp := blockSpanningFamily_span b c U v hspan hU
    rw [← real_span_rational_family U v' hsp, real_span_family_mem_iff_coordinates b v' x,
      real_column_span_mem_iff A]
    change (b.baseChange ℝ).equivFun x ∈ LinearMap.ker (Matrix.mulVecLin (fun i j => (Q i j : ℝ))) ↔ _
    rw [hker]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_weighted_linear_splitting
    {ι κ δ : Type*} [Fintype ι] [Fintype κ]
    (r : ι → δ) (c : κ → δ) (A : Matrix ι κ ℚ)
    (hblock : ∀ i j, r i ≠ c j → A i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (S : Matrix κ ι ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → S i j = 0) ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) → (∀ i, Real.exp (separationBudget p) ≤ W (r i)) →
      ∀ (a b : ι → ℝ) (v : κ → ℝ),
      (∀ i, |a i| ≤ Real.exp p / W (r i)) → b ∈ realDenominatorGrid l →
      (fun i j => (A i j : ℝ)) *ᵥ v = a + b →
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ a) = a ∧
      (fun i j => (A i j : ℝ)) *ᵥ ((fun i j => (S i j : ℝ)) *ᵥ b) = b ∧
      (∀ i, |((fun i j => (S i j : ℝ)) *ᵥ a) i| ≤
        Real.exp ((p + 2) ^ 18 + p) / W (c i)) ∧
      (fun i j => (S i j : ℝ)) *ᵥ b ∈ realDenominatorGrid m ∧
      (fun i j => (A i j : ℝ)) *ᵥ
        (v - (fun i j => (S i j : ℝ)) *ᵥ a - (fun i j => (S i j : ℝ)) *ᵥ b) = 0 := by
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section r c A hblock hH hA
  refine ⟨S, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hι hκ hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩, hSb, ?_⟩
  intro W hW hWmin a b v ha hb hv
  have hanorm : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (show ‖a i‖ ≤ Real.exp p / W (r i) by simpa only [Real.norm_eq_abs] using ha i).trans
    exact div_le_div_of_nonneg_left (Real.exp_nonneg p) (Real.exp_pos _) (hWmin i)
  have hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) :=
    (real_column_span_mem_iff A (a + b)).mpr ⟨v, hv⟩
  obtain ⟨haspan, hbspan⟩ := controlled_small_vector_separation A hH hl hA hp hι hκ hHp hlp a b hanorm hb hsum
  have hSa := real_matrix_image_section_apply A S hS a ((real_column_span_mem_iff A a).mp haspan)
  have hSb' := real_matrix_image_section_apply A S hS b ((real_column_span_mem_iff A b).mp hbspan)
  refine ⟨hSa, hSb', ?_, real_matrix_denominator_grid S l b hb, ?_⟩
  · intro i
    simpa only [← Real.exp_add] using
      real_image_section_weighted_bound r c S H hSb hSH hp hι hκ hHp W hW (Real.exp_nonneg p) a ha i
  · change Matrix.of (fun i j => (A i j : ℝ)) *ᵥ
      (v - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ a - Matrix.of (fun i j => (S i j : ℝ)) *ᵥ b) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
    exact (congrArg₂ (fun x y : ι → ℝ => x - y)
      (congrArg₂ (fun x y : ι → ℝ => x - y) hv hSa) hSb').trans (by abel)

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_constraint_section
    {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (r : ι → δ) (c : κ → δ) (t : μ → δ)
    (Q : Matrix ι κ ℚ) (P : Matrix μ κ ℚ)
    (hQblock : ∀ i j, r i ≠ c j → Q i j = 0)
    (hPblock : ∀ i j, t i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (T : Matrix κ μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ t j → T i j = 0) ∧
      (∀ i j, RationalHeightLE (T i j) (rationalKernelHeight (Fintype.card (ι ⊕ μ)) H)) ∧
      (∀ y : μ → ℝ,
        (∃ x : κ → ℝ, (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ x = y) →
        (fun i j => (Q i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (t i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((p + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let A := constraintProjectionMatrix Q P
  have hAblock : ∀ i j, Sum.elim r t i ≠ c j → A i j = 0 := by
    intro i j hij
    cases i with
    | inl i => exact hQblock i j hij
    | inr i => exact hPblock i j hij
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    cases i with
    | inl i => exact hQ i j
    | inr i => exact hP i j
  obtain ⟨S, hS, hSblock, hSH⟩ :=
    exists_bounded_block_image_section (Sum.elim r t) c A hAblock hH hA
  let T : Matrix κ μ ℚ := fun i j => S i (Sum.inr j)
  have hTS (y : μ → ℝ) :
      (fun i j => (S i j : ℝ)) *ᵥ constraintProjectionInput (ι := ι) y =
        (fun i j => (T i j : ℝ)) *ᵥ y :=
    mulVec_constraintProjectionInput _ y
  refine ⟨T, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hrows hcols hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩,
    (fun i j hij => hSblock i (Sum.inr j) hij), (fun i j => hSH i (Sum.inr j)), ?_, ?_, ?_⟩
  · intro y hy
    have hAy : constraintProjectionInput (ι := ι) y ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      obtain ⟨x, hxQ, hxP⟩ := hy
      refine ⟨x, ?_⟩
      funext i
      cases i with
      | inl i => exact congrFun hxQ i
      | inr i => exact congrFun hxP i
    have he := real_matrix_image_section_apply A S hS _ hAy
    rw [hTS] at he
    constructor
    · funext i
      exact congrFun he (Sum.inl i)
    · funext i
      exact congrFun he (Sum.inr i)
  · intro W hW M hM y hy i
    have hh := real_image_section_weighted_bound (Sum.elim r t) c S H hSblock hSH
      hp hrows hcols hHp W hW hM (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_weighted r t W hW hM y hy) i
    rwa [hTS] at hh
  · intro y hy
    have hh := real_matrix_denominator_grid S l (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_grid l y hy)
    rwa [hTS] at hh

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

variable {η ι δ : Type*} [Fintype ι]

noncomputable def jointMatrixImages (Q : η → Matrix ι ι ℚ) (x : η → ι → ℝ) : (Σ _ : η, ι) → ℝ :=
  fun bi => ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2

theorem jointMatrixImages_grid [Fintype η] (Q : η → Matrix ι ι ℚ) (l : ℕ)
    (x : η → ι → ℝ) (hx : ∀ b, x b ∈ realDenominatorGrid l) :
    jointMatrixImages Q x ∈ realDenominatorGrid (matrixDenominator (jointMatrix Q) * l) := by
  classical
  choose z hz using hx
  let A := jointMatrix Q
  have hcoef (bi : Σ _ : η, ι) (j : ι) :
      ((clearedMatrix A bi j : ℤ) : ℝ) = (matrixDenominator A : ℝ) * (Q bi.1 bi.2 j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast A) bi) j
    change ((clearedMatrix A bi j : ℤ) : ℚ) = (matrixDenominator A : ℚ) * Q bi.1 bi.2 j at h
    exact_mod_cast h
  refine ⟨fun bi => ∑ j, clearedMatrix A bi j * z bi.1 j, ?_⟩
  funext bi
  change ((∑ j, clearedMatrix A bi j * z bi.1 j : ℤ) : ℝ) =
    ((matrixDenominator A * l : ℕ) : ℝ) * ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ x bi.1) bi.2
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z bi.1 j : ℝ) = (l : ℝ) * x bi.1 j := congrFun (hz bi.1) j
  rw [hcoef, hj]
  ring

theorem jointMatrixImages_equation (Q : η → Matrix ι ι ℚ) (e r : η → ι → ℝ) (v : ι → ℝ)
    (h : ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) :
    (fun bi j => (jointMatrix Q bi j : ℝ)) *ᵥ v = jointMatrixImages Q e + jointMatrixImages Q r := by
  funext bi
  have hb := h bi.1
  change Matrix.of (fun i j => (Q bi.1 i j : ℝ)) *ᵥ (v - e bi.1 - r bi.1) = 0 at hb
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub] at hb
  have hb' := congrFun hb bi.2
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 -
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2 = 0 at hb'
  change ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ v) bi.2 =
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ e bi.1) bi.2 +
    ((fun i j => (Q bi.1 i j : ℝ)) *ᵥ r bi.1) bi.2
  linarith

theorem exists_joint_weighted_corrections [Fintype η]
    (c : ι → δ) (Q : η → Matrix ι ι ℚ)
    (hblock : ∀ b i j, c i ≠ c j → Q b i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ b i j, RationalHeightLE (Q b i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((p + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ι → ℝ) (v : ι → ℝ),
      (∀ b i, |e b i| ≤ Real.exp p / W (c i)) →
      (∀ b, r b ∈ realDenominatorGrid l) →
      (∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - e b - r b) = 0) →
      ∃ u d : ι → ℝ,
        (∀ i, |u i| ≤ Real.exp (((p + 2) ^ 4 + 2) ^ 18 + (p + 2) ^ 4) / W (c i)) ∧
        d ∈ realDenominatorGrid m ∧
        ∀ b, (fun i j => (Q b i j : ℝ)) *ᵥ (v - u - d) = 0 := by
  let A := jointMatrix Q
  let q : ℝ := (p + 2) ^ 4
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 4)
  have hAh : ∀ bi j, RationalHeightLE (A bi j) H := fun bi j => hQ bi.1 bi.2 j
  have hAb : ∀ bi j, c bi.2 ≠ c j → A bi j = 0 := fun bi j h => hblock bi.1 bi.2 j h
  have hDen : ((matrixDenominator A * l : ℕ) : ℝ) ≤ Real.exp q := by
    simpa only [Nat.mul_comm] using matrixDenominator_allowance_le_exp A l H hAh hp hrows hι hHp hlp
  obtain ⟨S, m, hm, hmp, hdm, _, hsplit⟩ := exists_controlled_weighted_linear_splitting
    (fun bi : Σ _ : η, ι => c bi.2) c A hAb hH
    (Nat.mul_pos (matrixDenominator_pos A) hl) hAh hq (hrows.trans hpq) (hι.trans hpq)
    (hHp.trans (Real.exp_le_exp.mpr hpq)) hDen
  refine ⟨m, hm, hmp, dvd_trans ⟨matrixDenominator A, Nat.mul_comm _ _⟩ hdm, ?_⟩
  intro W hW hWmin e r v he hr hres
  have hfac : ((Fintype.card ι : ℝ) + 1) * ((H : ℝ) + 1) ≤ Real.exp ((p + 2) ^ 2) := by
    apply le_trans _ (coordinateLipschitzBound_le_exp (Fintype.card ι) (Fintype.card ι)
      (H : ℝ≥0) hp hι hι hHp)
    change _ ≤ ((Fintype.card ι : ℝ) + Fintype.card ι + 1) * ((H : ℝ) + 1)
    gcongr
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hcost : (p + 2) ^ 2 + p ≤ q := by
    have hp2 : p ≤ (p + 2) ^ 2 := le_power_budget hp (by decide : 1 ≤ 2)
    calc
      _ ≤ 2 * (p + 2) ^ 2 := by linarith
      _ ≤ (p + 2) ^ 2 * (p + 2) ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg p]
      _ = q := by dsimp [q]; ring
  have hslow : ∀ bi, |jointMatrixImages Q e bi| ≤ Real.exp q / W (c bi.2) := by
    intro bi
    have h := weighted_matrix_mulVec_bound c c (fun i j => (Q bi.1 i j : ℝ))
      (fun i j hij => by rw [hblock bi.1 i j hij, Rat.cast_zero])
      (H : ℝ≥0) (fun i j => (hQ bi.1 i j).abs_real_le) W hW (Real.exp_nonneg p) (e bi.1) (he bi.1) bi.2
    apply h.trans
    apply div_le_div_of_nonneg_right _ (hW _).le
    calc
      _ ≤ Real.exp ((p + 2) ^ 2) * Real.exp p := mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg p)
      _ = Real.exp ((p + 2) ^ 2 + p) := (Real.exp_add _ _).symm
      _ ≤ Real.exp q := Real.exp_le_exp.mpr hcost
  obtain ⟨_, _, hu, hd, hker⟩ := hsplit W hW (fun bi => hWmin bi.2)
    (jointMatrixImages Q e) (jointMatrixImages Q r) v hslow (jointMatrixImages_grid Q l r hr)
    (jointMatrixImages_equation Q e r v hres)
  refine ⟨(fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q e,
    (fun i j => (S i j : ℝ)) *ᵥ jointMatrixImages Q r, hu, hd, ?_⟩
  intro b
  funext i
  exact congrFun hker ⟨b, i⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_block_subspace_lift
    {ι κ μ δ L : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (r : μ → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    (P : Matrix μ ι ℚ) (hPblock : ∀ i j, r i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (T : Matrix ι μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → T i j = 0) ∧
      (∀ y : μ → ℝ,
        (∃ x ∈ U.baseChange ℝ, (fun i j => (P i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = y) →
        (b.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ y) ∈ U.baseChange ℝ ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (r i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((q + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hι : (Fintype.card ι : ℝ) ≤ p := by
    have hsum : (Fintype.card ι : ℝ) + Fintype.card μ ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hrows
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  let H' := max (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) H
  have hH' : 1 ≤ H' := hH.trans (Nat.le_max_right _ _)
  have hH'q : (H' : ℝ) ≤ Real.exp q := by
    dsimp only [H']
    rw [Nat.cast_max]
    exact max_le (imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp)
      (hHp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨Q, hQ, hQblock, hQker⟩ :=
    exists_block_subspace_defining_matrix b c U v hspan hU hH hv
  obtain ⟨T, m, hm, hmp, hlm, hTblock, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_constraint_section c c r Q P hQblock hPblock hH' hl
      (fun i j => (hQ i j).mono (Nat.le_max_left _ _))
      (fun i j => (hP i j).mono (Nat.le_max_right _ _))
      hq (hrows.trans hpq) (hι.trans hpq) hH'q (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨T, m, hm, hmp, hlm, hTblock, ?_, hslow, hgrid⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨hzero, hright⟩ := hsolve y
    ⟨(b.baseChange ℝ).equivFun x, (hQker x).mpr hx, hxy⟩
  refine ⟨(hQker _).mp ?_, hright⟩
  simpa only [LinearEquiv.apply_symm_apply] using hzero

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_block_subspace_corrections
    {η ι κ δ L : Type*} [Fintype η] [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (U : η → Submodule ℚ L) (v : η → κ → L)
    (hspan : ∀ j, Submodule.span ℚ (Set.range (v j)) = U j)
    (hU : ∀ j, BasisBlockInvariant b c (U j))
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j z i, RationalHeightLE (b.repr (v j z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hrows : (Fintype.card (Σ _ : η, ι) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 36) ∧ l ∣ m ∧
      ∀ (W : δ → ℝ), (∀ d, 0 < W d) →
      (∀ i, Real.exp (separationBudget ((q + 2) ^ 4)) ≤ W (c i)) →
      ∀ (e r : η → ℝ ⊗[ℚ] L) (x : ℝ ⊗[ℚ] L),
      (∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp p / W (c i)) →
      (∀ j, (b.baseChange ℝ).equivFun (r j) ∈ realDenominatorGrid l) →
      (∀ j, x - e j - r j ∈ (U j).baseChange ℝ) →
      ∃ u d : ℝ ⊗[ℚ] L,
        (∀ i, |(b.baseChange ℝ).equivFun u i| ≤ Real.exp (((q + 2) ^ 4 + 2) ^ 18 + (q + 2) ^ 4) / W (c i)) ∧
        (b.baseChange ℝ).equivFun d ∈ realDenominatorGrid m ∧
        ∀ j, x - u - d ∈ (U j).baseChange ℝ := by
  classical
  let H' := imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hH' : 1 ≤ H' := by
    have hk := rationalKernelHeight_pos (Fintype.card ι) hH
    have hHpos : 0 < H := hH
    have hpos : 0 < H' := by
      dsimp [H', imageDefiningHeight]
      positivity
    exact hpos
  have hH'p : (H' : ℝ) ≤ Real.exp q := imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp
  choose Q hQ hQb hQker using fun j =>
    exists_block_subspace_defining_matrix b c (U j) (v j) (hspan j) (hU j) hH (hv j)
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_joint_weighted_corrections c Q hQb hH' hl hQ hq
    (hι.trans hpq) (hrows.trans hpq) hH'p (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro W hW hWmin e r x he hr hres
  have he' : ∀ j i, |(b.baseChange ℝ).equivFun (e j) i| ≤ Real.exp q / W (c i) := by
    intro j i
    exact (he j i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hpq) (hW _).le)
  have hsys : ∀ j, (fun i k => (Q j i k : ℝ)) *ᵥ
      ((b.baseChange ℝ).equivFun x - (b.baseChange ℝ).equivFun (e j) - (b.baseChange ℝ).equivFun (r j)) = 0 := by
    intro j
    simpa only [map_sub] using (hQker j (x - e j - r j)).mpr (hres j)
  obtain ⟨u, d, hu, hd, hker⟩ := hsolve W hW hWmin
    (fun j => (b.baseChange ℝ).equivFun (e j)) (fun j => (b.baseChange ℝ).equivFun (r j))
    ((b.baseChange ℝ).equivFun x) he' hr hsys
  refine ⟨(b.baseChange ℝ).equivFun.symm u, (b.baseChange ℝ).equivFun.symm d, ?_, ?_, ?_⟩
  · simpa only [LinearEquiv.apply_symm_apply] using hu
  · simpa only [LinearEquiv.apply_symm_apply] using hd
  · intro j
    apply (hQker j _).mp
    simpa only [map_sub, LinearEquiv.apply_symm_apply] using hker j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_linear_subspace_lift
    {ι κ μ δ L M : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant e c U)
    (φ : L →ₗ[ℚ] M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → e.repr (σ (f j)) i = 0) ∧
      (∀ y ∈ (U.map φ).baseChange ℝ,
        σ.baseChange ℝ y ∈ U.baseChange ℝ ∧ φ.baseChange ℝ (σ.baseChange ℝ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ y : ℝ ⊗[ℚ] M, (∀ i, |(f.baseChange ℝ).equivFun y i| ≤ B / W (r i)) →
          ∀ i, |(e.baseChange ℝ).equivFun (σ.baseChange ℝ y) i| ≤
            Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ y : ℝ ⊗[ℚ] M, (f.baseChange ℝ).equivFun y ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) ∈ realDenominatorGrid m) := by
  classical
  let P := LinearMap.toMatrix e f φ
  obtain ⟨T, m, hm, hmp, hlm, hTblock, hsolve, hslow, hgrid⟩ :=
    exists_controlled_block_subspace_lift e c r U v hspan hU P
      (by intro i j hij; simpa only [P, LinearMap.toMatrix_apply] using hblock i j hij) hH hl hv
      (by intro i j; simpa only [P, LinearMap.toMatrix_apply] using hφ i j) hp hrows hcols hHp hlp
  let σ := Matrix.toLin f e T
  have hcoord (y : ℝ ⊗[ℚ] M) :
      (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) =
        (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y :=
    toLin_baseChange_coordinates e f T y
  have hlift (y : ℝ ⊗[ℚ] M) : σ.baseChange ℝ y =
      (e.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y) := by
    apply (e.baseChange ℝ).equivFun.injective
    rw [hcoord, LinearEquiv.apply_symm_apply]
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have he := LinearMap.toMatrix_apply f e σ i j
    rw [LinearMap.toMatrix_toLin] at he
    exact he.symm.trans (hTblock i j hij)
  · intro y hy
    rw [realification_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨hmem, hright⟩ := hsolve ((f.baseChange ℝ).equivFun y)
      ⟨x, hx, (baseChange_matrix_apply e f φ x).trans (congrArg (f.baseChange ℝ).equivFun hxy)⟩
    constructor
    · rwa [hlift]
    · apply (f.baseChange ℝ).equivFun.injective
      rw [← baseChange_matrix_apply e f φ, hcoord]
      exact hright
  · intro W hW B hB y hy i
    rw [hcoord]
    exact hslow W hW B hB ((f.baseChange ℝ).equivFun y) hy i
  · intro y hy
    rw [hcoord]
    exact hgrid ((f.baseChange ℝ).equivFun y) hy

end Erdos3

end

end OAI
