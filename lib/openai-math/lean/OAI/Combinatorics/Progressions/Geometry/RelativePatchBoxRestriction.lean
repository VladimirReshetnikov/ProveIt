/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def relativeBoxInput {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (x : X → ℤ) : ℝ :=
  if x ∈ integerBox N then f x else 0

@[simp] theorem relativeBoxInput_eq {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {x : X → ℤ} (hx : x ∈ integerBox N) :
    relativeBoxInput N f x = f x := by
  simp only [relativeBoxInput, ite_eq_left hx]

theorem relativeBoxInput_unitInterval {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x, relativeBoxInput N f x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x
  by_cases hx : x ∈ integerBox N
  · simpa only [relativeBoxInput_eq N f hx] using hf x hx
  · simp only [relativeBoxInput, ite_eq_right hx, Set.mem_Icc]
    constructor <;> norm_num

theorem relativeBoxInput_signed_norm {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (x : X → ℤ) :
    ‖((relativeBoxInput N f x - lam : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  have hx := relativeBoxInput_unitInterval N f hf x
  constructor <;> linarith only [hx.1, hx.2, hlam.1, hlam.2]

theorem relativeBoxInput_progressionFree {X : Type*} [Fintype X]
    (N : X → ℕ) (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree {x | x ∈ integerBox N ∧ relativeBoxInput N f x ≠ 0} k := by
  convert hfree using 1
  ext x
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by simpa only [relativeBoxInput_eq N f hx] using h⟩

theorem relativePatchBoxScore_congr_input {X : Type*} [Fintype X] [DecidableEq X]
    {s d : ℕ} (N : X → ℕ) {f g : (X → ℤ) → ℝ}
    (hfg : ∀ x ∈ integerBox N, f x = g x) (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchBoxScore N f target A = relativePatchBoxScore N g target A := by
  apply Finset.expect_congr rfl
  intro x hx
  rw [hfg x hx]

theorem relativePatchSliceScore_congr_input {X : Type*} [Fintype X]
    {s d q : ℕ} {N : X → ℕ} (S : ResidueBoxSlice N q)
    {f g : (X → ℤ) → ℝ} (hfg : ∀ x ∈ integerBox N, f x = g x)
    (target : ℝ) (A : PolynomialPatch X s d) :
    relativePatchSliceScore S f target A = relativePatchSliceScore S g target A := by
  apply Finset.expect_congr rfl
  intro x _
  have hx : (fun i => ((S.point x i).val : ℤ)) ∈ integerBox N := by
    rw [mem_integerBox]
    intro i
    exact ⟨by positivity, by exact_mod_cast (S.point x i).isLt⟩
  rw [hfg _ hx]

theorem RelativePatchSliceConclusion.congr_input {X : Type*} [Fintype X]
    {s : ℕ} {N : X → ℕ} {f g : (X → ℤ) → ℝ}
    {target cost : ℝ} {rankBound : ℕ}
    (h : RelativePatchSliceConclusion s N f target rankBound cost)
    (hfg : ∀ x ∈ integerBox N, f x = g x) :
    RelativePatchSliceConclusion s N g target rankBound cost := by
  obtain ⟨q, hq, S, d, A, hlength, hrank, hcost, hscore⟩ := h
  refine ⟨q, hq, S, d, A, hlength, hrank, hcost, ?_⟩
  rwa [relativePatchSliceScore_congr_input S hfg target A] at hscore

end Erdos3

end

end OAI
