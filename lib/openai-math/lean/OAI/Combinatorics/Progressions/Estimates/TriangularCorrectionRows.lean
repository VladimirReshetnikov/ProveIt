/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def triangularCorrectionSolutions {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (B : ℝ) (q : ℕ) :
    Set ((Fin n → ℝ) × (Fin n → ℚ)) :=
  {sr | (∀ i, |sr.1 i| ≤ B) ∧
    (∀ i, ∃ z : ℤ, sr.2 i = (z : ℚ) / q) ∧
    ∀ i, c i = ∑ j, A i j * sr.1 j + (sr.2 i : ℝ)}

theorem triangularCorrectionSolutions_prefix {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (htri : ∀ i j, i < j → A i j = 0)
    (hsr : sr ∈ triangularCorrectionSolutions A c B q) :
    ((fun i : Fin n => sr.1 i.castSucc), (fun i : Fin n => sr.2 i.castSucc)) ∈
      triangularCorrectionSolutions (fun i j => A i.castSucc j.castSucc)
        (fun i => c i.castSucc) B q := by
  refine ⟨fun i => hsr.1 i.castSucc, fun i => hsr.2.1 i.castSucc, ?_⟩
  intro i
  have hi := hsr.2.2 i.castSucc
  rw [Fin.sum_univ_castSucc] at hi
  simpa only [htri i.castSucc (Fin.last n) i.castSucc_lt_last, zero_mul, add_zero]
    using hi

theorem triangularCorrectionSolutions_last_eq {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (hdiag : A (Fin.last n) (Fin.last n) ≠ 0) :
    sr.1 (Fin.last n) =
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc -
        (sr.2 (Fin.last n) : ℝ)) / A (Fin.last n) (Fin.last n) := by
  apply (eq_div_iff hdiag).2
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  linarith

theorem triangularCorrectionSolutions_last_window {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c : Fin (n + 1) → ℝ} {B : ℝ} {q : ℕ}
    {sr : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℚ)}
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (_hB : 0 ≤ B) (hdiag : |A (Fin.last n) (Fin.last n)| ≤ 1) :
    |(sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc)| ≤ B := by
  have hi := hsr.2.2 (Fin.last n)
  rw [Fin.sum_univ_castSucc] at hi
  have heq : (sr.2 (Fin.last n) : ℝ) -
      (c (Fin.last n) - ∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc) =
      -(A (Fin.last n) (Fin.last n) * sr.1 (Fin.last n)) := by linarith
  rw [heq, abs_neg, abs_mul]
  calc
    _ ≤ 1 * |sr.1 (Fin.last n)| :=
      mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
    _ ≤ B := by simpa only [one_mul] using hsr.1 (Fin.last n)

theorem triangularCorrectionSolutions_slow_unique {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {c : Fin n → ℝ} {B : ℝ} {q : ℕ}
    {sr tr : (Fin n → ℝ) × (Fin n → ℚ)}
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0)
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (htr : tr ∈ triangularCorrectionSolutions A c B q)
    (hr : sr.2 = tr.2) : sr.1 = tr.1 := by
  induction n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have hp : (fun i : Fin n => sr.1 i.castSucc) =
          (fun i : Fin n => tr.1 i.castSucc) := by
        apply ih (fun i j hij => htri i.castSucc j.castSucc hij)
          (fun i => hdiag i.castSucc)
          (triangularCorrectionSolutions_prefix htri hsr)
          (triangularCorrectionSolutions_prefix htri htr)
        exact congrArg (fun r => fun i : Fin n => r i.castSucc) hr
      funext i
      refine Fin.lastCases ?_ (fun j => congrFun hp j) i
      rw [triangularCorrectionSolutions_last_eq hsr (hdiag (Fin.last n)),
        triangularCorrectionSolutions_last_eq htr (hdiag (Fin.last n)), hr]
      have hsum : (∑ j : Fin n, A (Fin.last n) j.castSucc * sr.1 j.castSucc) =
          ∑ j : Fin n, A (Fin.last n) j.castSucc * tr.1 j.castSucc := by
        apply Finset.sum_congr rfl
        intro j _
        rw [congrFun hp j]
      rw [hsum]

theorem triangularCorrectionSolutions_eq_of_rational_eq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {c : Fin n → ℝ} {B : ℝ} {q : ℕ}
    {sr tr : (Fin n → ℝ) × (Fin n → ℚ)}
    (htri : ∀ i j, i < j → A i j = 0)
    (hdiag : ∀ i, A i i ≠ 0)
    (hsr : sr ∈ triangularCorrectionSolutions A c B q)
    (htr : tr ∈ triangularCorrectionSolutions A c B q)
    (hr : sr.2 = tr.2) : sr = tr :=
  Prod.ext (triangularCorrectionSolutions_slow_unique htri hdiag hsr htr hr) hr

end Erdos3

end

end OAI
