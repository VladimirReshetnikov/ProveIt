import Diophantine.Common.MathlibDiophFinite
import Diophantine.Common.PositiveSquareTest
import Mathlib.Tactic

/-!
# Positive values of a polynomial for a Diophantine function graph

An integer polynomial whose natural zero set represents the graph of `f`
gives a polynomial whose positive values, with the input fixed, are exactly
the positive value of `f` at that input. Move the graph's output coordinate
to one additional natural witness `y` and use `y * (1 - Q^2)`.

This is the positive-value construction of Putnam. It supplies a finite
witness family without a numerical bound on its size. No positivity of
`f` is assumed, and the original graph may have no auxiliary witnesses.
-/

namespace Diophantine

open MvPolynomial

private def putnamGraphInputs (n y : ℕ) : Fin 2 → ℕ :=
  fun i => if i = 0 then n else y

/-- Keep the input coordinate and move the graph's output to the first witness. -/
private def putnamRename (r : ℕ) : Fin 2 ⊕ Fin r → Unit ⊕ Fin (r + 1) :=
  Sum.elim
    (fun idx => if idx = 0 then Sum.inl () else Sum.inr 0)
    (fun idx => Sum.inr idx.succ)

private noncomputable def putnamPolynomial {r : ℕ} (Q : MvPolynomial (Fin 2 ⊕ Fin r) ℤ) :
    MvPolynomial (Unit ⊕ Fin (r + 1)) ℤ :=
  X (Sum.inr 0) * (1 - (rename (putnamRename r) Q) ^ 2)

/-- Renaming is checked separately from the arithmetic of the square test.
Keeping this identity outside the existential construction avoids repeatedly
unfolding the local polynomial and its coordinate maps during elaboration. -/
private theorem putnamRename_eval {r : ℕ} (Q : MvPolynomial (Fin 2 ⊕ Fin r) ℤ)
    (n : ℕ) (w : Fin (r + 1) → ℕ) :
    eval (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ))
        (rename (putnamRename r) Q) =
      eval (fun idx =>
        ((Sum.elim (putnamGraphInputs n (w 0)) (fun idx => w idx.succ) idx : ℕ) : ℤ))
        Q := by
  rw [eval_rename]
  apply congrArg (fun v : Fin 2 ⊕ Fin r → ℤ => eval v Q)
  funext idx
  cases idx with
  | inl idx =>
      by_cases hidx : idx = 0
      · subst idx
        rfl
      · simp only [Function.comp_apply, putnamRename, putnamGraphInputs,
          Sum.elim_inl, if_neg hidx, Sum.elim_inr]
  | inr idx => rfl

private theorem putnamPolynomial_eval {r : ℕ}
    (Q : MvPolynomial (Fin 2 ⊕ Fin r) ℤ) (n : ℕ) (w : Fin (r + 1) → ℕ) :
    eval (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ))
        (putnamPolynomial Q) =
      (w 0 : ℤ) * (1 -
        (eval (fun idx =>
          ((Sum.elim (putnamGraphInputs n (w 0)) (fun idx => w idx.succ) idx : ℕ) : ℤ))
          Q) ^ 2) := by
  simp only [putnamPolynomial, eval_mul, eval_X, eval_sub, map_one, eval_pow,
    Sum.elim_inr]
  rw [putnamRename_eval]

/-- A positive value of the integer square test forces its residual to vanish. -/
private theorem putnam_eq_of_pos {y m : ℕ} {q : ℤ} (hm : 0 < m)
    (h : (y : ℤ) * (1 - q ^ 2) = (m : ℤ)) : q = 0 ∧ y = m := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hq : q = 0 :=
    eq_zero_of_mul_one_sub_sq_pos (Nat.cast_nonneg y) (by simpa only [h] using hm')
  refine ⟨hq, ?_⟩
  have hym : (y : ℤ) = (m : ℤ) := by simpa [hq] using h
  exact_mod_cast hym

/-- Putnam's construction for a given polynomial representation of the graph with `r`
witnesses: the positive values use `r + 1` witnesses. -/
theorem exists_polynomial_of_graph_polynomial {f : ℕ → ℕ} {r : ℕ}
    (Q : MvPolynomial (Fin 2 ⊕ Fin r) ℤ)
    (hQ : ∀ v : Fin 2 → ℕ, f (v 0) = v 1 ↔ ∃ t : Fin r → ℕ,
      eval (fun idx => ((Sum.elim v t idx : ℕ) : ℤ)) Q = 0) :
    ∃ P : MvPolynomial (Unit ⊕ Fin (r + 1)) ℤ,
      ∀ n m : ℕ, 0 < m →
        (f n = m ↔ ∃ w : Fin (r + 1) → ℕ,
          MvPolynomial.eval
            (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P =
              (m : ℤ)) := by
  classical
  have hgraph (n y : ℕ) :
      f n = y ↔ ∃ t : Fin r → ℕ,
        eval (fun idx => ((Sum.elim (putnamGraphInputs n y) t idx : ℕ) : ℤ)) Q = 0 := by
    exact hQ (putnamGraphInputs n y)
  refine ⟨putnamPolynomial Q, fun n m hm => ?_⟩
  constructor
  · intro hfm
    obtain ⟨t, ht⟩ := (hgraph n m).mp hfm
    refine ⟨Fin.cases (motive := fun _ => ℕ) m t, ?_⟩
    rw [putnamPolynomial_eval]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [ht]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
  · rintro ⟨w, hw⟩
    obtain ⟨hq, hy⟩ := putnam_eq_of_pos hm ((putnamPolynomial_eval Q n w).symm.trans hw)
    exact ((hgraph n (w 0)).mpr ⟨fun j => w j.succ, hq⟩).trans hy

/-- A function with Diophantine graph has an integer polynomial whose
positive values at each fixed input are exactly that function's positive
output. The output becomes one additional natural witness. -/
theorem exists_polynomial_of_dioph_graph {f : ℕ → ℕ}
    (h : Dioph {v : Fin 2 → ℕ | f (v 0) = v 1}) :
    ∃ k : ℕ, ∃ P : MvPolynomial (Unit ⊕ Fin k) ℤ,
      ∀ n m : ℕ, 0 < m →
        (f n = m ↔ ∃ w : Fin k → ℕ,
          MvPolynomial.eval
            (fun idx => ((Sum.elim (fun _ : Unit => n) w idx : ℕ) : ℤ)) P =
              (m : ℤ)) := by
  obtain ⟨r, Q, hQ⟩ := dioph_iff_exists_fin_polynomial.mp h
  obtain ⟨P, hP⟩ := exists_polynomial_of_graph_polynomial (f := f) Q hQ
  exact ⟨r + 1, P, hP⟩

end Diophantine
