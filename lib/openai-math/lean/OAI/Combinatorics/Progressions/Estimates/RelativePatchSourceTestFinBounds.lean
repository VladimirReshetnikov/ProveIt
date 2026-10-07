import OAI.Combinatorics.Progressions.Geometry.RelativePatchBoxRestriction

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativePatchSourceTest {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (y : X → ℝ) : ℝ :=
  (relativeBoxInput N f (fun i => ⌊y i⌋) - a) * A.value y

@[simp] theorem relativePatchSourceTest_integer {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (x : X → ℤ) :
    relativePatchSourceTest N f a A (fun i => (x i : ℝ)) =
      (relativeBoxInput N f x - a) * A.value (fun i => (x i : ℝ)) := by
  simp only [relativePatchSourceTest, Int.floor_intCast]

theorem relativePatchSourceTest_abs_le_one {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (y : X → ℝ) :
    |relativePatchSourceTest N f a A y| ≤ 1 := by
  have hinput := relativeBoxInput_unitInterval N f hf (fun i => ⌊y i⌋)
  have hpatch := A.value_mem_Icc y
  have hdiff : |relativeBoxInput N f (fun i => ⌊y i⌋) - a| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hinput.1, ha.2], by linarith only [hinput.2, ha.1]⟩
  unfold relativePatchSourceTest
  rw [abs_mul, abs_of_nonneg hpatch.1]
  exact (mul_le_mul_of_nonneg_right hdiff hpatch.1).trans (by simpa only [one_mul] using hpatch.2)

theorem relativePatchSourceTest_mean {X : Type*} [Fintype X] {s d : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d) :
    (𝔼 x ∈ integerBox N, relativePatchSourceTest N f a A (fun i => (x i : ℝ))) =
      relativePatchBoxScore N f a A := by
  unfold relativePatchBoxScore
  apply Finset.expect_congr rfl
  intro x hx
  rw [relativePatchSourceTest_integer, relativeBoxInput_eq N f hx]

theorem relativePatchSourceTest_productive_data {X : Type*} [Fintype X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ) (A : PolynomialPatch X s d)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) {gain : ℝ}
    (hscore : gain ≤ relativePatchBoxScore N f a A) :
    (∀ y, |relativePatchSourceTest N f a A y| ≤ 1) ∧
      gain ≤ 𝔼 x ∈ integerBox N, relativePatchSourceTest N f a A (fun i => (x i : ℝ)) := by
  exact ⟨relativePatchSourceTest_abs_le_one N f a A hf ha,
    by rwa [relativePatchSourceTest_mean N f a A]⟩

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem relativePatchSourceTest_fin_mean {nX s d : ℕ}
    (N : Fin nX → ℕ) (f : (Fin nX → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch (Fin nX) s d) :
    (𝔼 x ∈ integerBox N, relativePatchSourceTest N f a A (fun i => (x i : ℝ))) =
      relativePatchBoxScore N f a A := by
  unfold relativePatchBoxScore
  apply Finset.expect_congr rfl
  intro x hx
  rw [relativePatchSourceTest_integer,
    relativeBoxInput_eq N f (by simpa only [mem_integerBox] using hx)]

theorem relativePatchSourceTest_fin_productive_data {nX s d : ℕ}
    (N : Fin nX → ℕ) (f : (Fin nX → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch (Fin nX) s d)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) {gain : ℝ}
    (hscore : gain ≤ relativePatchBoxScore N f a A) :
    (∀ y, |relativePatchSourceTest N f a A y| ≤ 1) ∧
      gain ≤ 𝔼 x ∈ integerBox N, relativePatchSourceTest N f a A (fun i => (x i : ℝ)) := by
  refine ⟨relativePatchSourceTest_abs_le_one N f a A (fun x _ => hf x) ha, ?_⟩
  rwa [relativePatchSourceTest_fin_mean]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

attribute [local irreducible] integerBox

theorem relativePatchSourceTest_fin_productive_data_of_box {nX s d : ℕ}
    (N : Fin nX → ℕ) (f : (Fin nX → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch (Fin nX) s d)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) {gain : ℝ}
    (hscore : gain ≤ relativePatchBoxScore N f a A) :
    (∀ y, |relativePatchSourceTest N f a A y| ≤ 1) ∧
      gain ≤ 𝔼 x ∈ integerBox N,
        relativePatchSourceTest N f a A (fun i => (x i : ℝ)) := by
  refine ⟨relativePatchSourceTest_abs_le_one N f a A ?_ ha, ?_⟩
  · intro x hx
    exact hf x (by simpa only [mem_integerBox] using hx)
  · rwa [relativePatchSourceTest_fin_mean]

theorem relativePatchSourceTrim_bounds {gainLog : ℝ} (hgainLog : 0 ≤ gainLog)
    (nX : ℕ) :
    0 < Real.exp (-(gainLog + (nX : ℝ) + 8)) ∧
      Real.exp (-(gainLog + (nX : ℝ) + 8)) ≤ 1 / 2 := by
  refine ⟨Real.exp_pos _, ?_⟩
  rw [Real.exp_neg, ← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.add_one_le_exp (gainLog + (nX : ℝ) + 8)
  have hnX : 0 ≤ (nX : ℝ) := Nat.cast_nonneg _
  linarith only [h, hgainLog, hnX]

theorem relativePatchSourceGain_pos {gainLog gain : ℝ}
    (hgain : Real.exp (-gainLog) ≤ gain) : 0 < gain :=
  (Real.exp_pos _).trans_le hgain

end Erdos3

end

end OAI
