import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def tripleBoxSlice {X : Type*} (a z : Fin 3 → X) : Fin 6 → X :=
  ![z 0, a 0, z 1, a 1, z 2, a 2]

def tripleBoxSliceEquiv (X : Type*) : ((Fin 3 → X) × (Fin 3 → X)) ≃ (Fin 6 → X) where
  toFun p := tripleBoxSlice p.1 p.2
  invFun x := (![x 1, x 3, x 5], ![x 0, x 2, x 4])
  left_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

theorem expect_tripleBoxSlice {X M : Type*} [Fintype X] [AddCommMonoid M] [Module ℚ≥0 M]
    (F : (Fin 6 → X) → M) :
    (𝔼 x, F x) = 𝔼 a : Fin 3 → X, 𝔼 z : Fin 3 → X, F (tripleBoxSlice a z) := by
  calc
    _ = 𝔼 p : (Fin 3 → X) × (Fin 3 → X), F (tripleBoxSlice p.1 p.2) :=
      (Fintype.expect_equiv (tripleBoxSliceEquiv X) _ F (fun _ => rfl)).symm
    _ = _ := by
      simpa using (Finset.expect_product' Finset.univ Finset.univ
        (fun a z => F (tripleBoxSlice a z)))

noncomputable def tripleBoxKernel {X : Type*} (K : X → X → X → ℂ) (x : Fin 6 → X) : ℂ :=
  let G := fun h y => K (x 0) h y * star (K (x 1) h y)
  G (x 2) (x 4) * star (G (x 3) (x 4)) * star (G (x 2) (x 5)) * G (x 3) (x 5)

noncomputable def tripleBoxAnchorFactor {X : Type*} (K : X → X → X → ℂ)
    (a z : Fin 3 → X) : ℂ :=
  ((star (K (a 0) (z 1) (z 2)) * star (K (z 0) (a 1) (z 2))) *
    (K (a 0) (a 1) (z 2) * star (K (z 0) (z 1) (a 2)))) *
      ((K (a 0) (z 1) (a 2) * K (z 0) (a 1) (a 2)) * star (K (a 0) (a 1) (a 2)))

theorem tripleBoxKernel_slice {X : Type*} (K : X → X → X → ℂ) (a z : Fin 3 → X) :
    tripleBoxKernel K (tripleBoxSlice a z) = K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z := by
  have hlast : (![z 0, a 0, z 1, a 1, z 2, a 2] : Fin 6 → X) 5 = a 2 := rfl
  simp only [tripleBoxKernel, tripleBoxSlice, tripleBoxAnchorFactor, star_mul, star_star,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, hlast]
  ring

theorem tripleBoxKernel_mean {X : Type*} [Fintype X] (K : X → X → X → ℂ) :
    (𝔼 x : Fin 6 → X, tripleBoxKernel K x) = finiteTripleBoxCorrelation K := by
  simp_rw [expect_fin_cons]
  unfold finiteTripleBoxCorrelation finiteBoxCorrelation
  apply Finset.expect_congr rfl
  intro k _
  apply Finset.expect_congr rfl
  intro k' _
  apply Finset.expect_congr rfl
  intro h _
  apply Finset.expect_congr rfl
  intro h' _
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro y' _
  change (𝔼 _ : Fin 0 → X, (K k h y * star (K k' h y)) *
    star (K k h' y * star (K k' h' y)) * star (K k h y' * star (K k' h y')) *
      (K k h' y' * star (K k' h' y'))) = _
  rw [Fintype.expect_const]

theorem tripleBoxAnchorFactor_norm_le_one {X : Type*} (K : X → X → X → ℂ)
    (hK : ∀ k h y, ‖K k h y‖ ≤ 1) (a z : Fin 3 → X) : ‖tripleBoxAnchorFactor K a z‖ ≤ 1 := by
  simp only [tripleBoxAnchorFactor, norm_mul, norm_star]
  calc
    _ ≤ (((1 : ℝ) * 1) * (1 * 1)) * ((1 * 1) * 1) := by gcongr <;> apply hK
    _ = 1 := by norm_num

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_triple_box_anchor_approximation {X : Type*} [Fintype X] [Nonempty X]
    (K : X → X → X → ℂ) (hK : ∀ k x y, ‖K k x y‖ ≤ 1) (F : (Fin 6 → X) → ℂ)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hbias : δ ≤ (finiteTripleBoxCorrelation K).re)
    (herr : (𝔼 x : Fin 6 → X, ‖tripleBoxKernel K x - F x‖) ≤ ε) :
    ∃ a : Fin 3 → X,
      δ ^ 2 / 2 ≤ (𝔼 z : Fin 3 → X, ‖tripleBoxAnchorFactor K a z‖ ^ 2) ∧
      δ ^ 2 / 2 ≤ (𝔼 z : Fin 3 → X, ‖K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z‖ ^ 2) ∧
      (𝔼 z : Fin 3 → X,
        ‖K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z - F (tripleBoxSlice a z)‖) ≤ 2 * ε / δ ^ 2 := by
  let A := fun a : Fin 3 → X =>
    𝔼 z : Fin 3 → X, ‖K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z‖ ^ 2
  let B := fun a : Fin 3 → X => 𝔼 z : Fin 3 → X, ‖tripleBoxKernel K (tripleBoxSlice a z) - F (tripleBoxSlice a z)‖
  have hA : ∀ a, A a ≤ 1 := by
    intro a
    have hnorm (z : Fin 3 → X) : ‖K (z 0) (z 1) (z 2) * tripleBoxAnchorFactor K a z‖ ≤ 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _)).trans
        (tripleBoxAnchorFactor_norm_le_one K hK a z)
    exact (Finset.expect_le_expect (fun z _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2)).trans_eq (by simp)
  have hB : ∀ a, 0 ≤ B a := fun a => Finset.expect_nonneg (fun z _ => norm_nonneg _)
  have hmass : δ ^ 2 ≤ 𝔼 a, A a := by
    calc
      _ ≤ ‖finiteTripleBoxCorrelation K‖ ^ 2 :=
        pow_le_pow_left₀ hδ.le (hbias.trans (Complex.re_le_norm _)) 2
      _ ≤ 𝔼 x : Fin 6 → X, ‖tripleBoxKernel K x‖ ^ 2 := by
        rw [← tripleBoxKernel_mean]
        exact norm_expect_sq_le_expect_norm_sq _
      _ = _ := by simpa only [A, tripleBoxKernel_slice] using expect_tripleBoxSlice (fun x => ‖tripleBoxKernel K x‖ ^ 2)
  have herror : (𝔼 a, B a) ≤ ε := by
    rw [expect_tripleBoxSlice] at herr
    exact herr
  obtain ⟨a, ha, he⟩ := exists_mass_error_point A B (sq_pos_of_pos hδ) hε hA hB hmass herror
  refine ⟨a, ha.trans ?_, ha, by simpa only [B, tripleBoxKernel_slice] using he⟩
  apply Finset.expect_le_expect
  intro z _
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _)

end Erdos3

end

end OAI
