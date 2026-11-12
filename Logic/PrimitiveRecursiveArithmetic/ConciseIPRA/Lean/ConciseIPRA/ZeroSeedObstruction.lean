import ConciseIPRA.NativeModels

/-!
# The seed of the iterator cannot be fixed to zero

The iterator `I(c, a; u.h)` carries a counter, a seed and an update.  A
tempting simplification deletes the seed: `R(c; k, u.h)` with

  `R(0; k, u.h) = 0`,  `R(S c; k, u.h) = h[c/k, R(c; k, u.h)/u]`.

The update may even see the counter `k`.  The package
`Research/scope_and_closure` (`theory/zero_start_obstruction.tex`) observes
that this is not a free simplification, by a property of the standard model:

* `ZTm.mono`: every term of the zero-seeded language denotes a function that
  is nondecreasing in each of its variables.

So no such term is the zero test (`ZTm.no_zero_test`), whereas the term
`sel(x, 1, 0)` of the kernel's language is (`Tm.val_zf`).  The selector is
what the kernel uses to place two formulas in one matrix, so the logical
bootstrap of the kernel is not available on the zero-seeded terms as it
stands.

The statement is about denotations in the natural numbers only; it does not
say that no calculus on zero-seeded terms is equivalent to iPRA.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open Tm (zero succ iter)

variable {n : ℕ}

/-- Terms with a recursor whose seed is fixed to zero.  The update binds the
counter (index `0`) and the previous value (index `1`). -/
inductive ZTm : ℕ → Type
  | var {n : ℕ} (i : Fin n) : ZTm n
  | zero {n : ℕ} : ZTm n
  | succ {n : ℕ} (t : ZTm n) : ZTm n
  | recur {n : ℕ} (c : ZTm n) (h : ZTm (n + 2)) : ZTm n

namespace ZTm

/-- The value of a term in the natural numbers. -/
def val : {n : ℕ} → ZTm n → (Fin n → ℕ) → ℕ
  | _, .var i, ρ => ρ i
  | _, .zero, _ => 0
  | _, .succ t, ρ => val t ρ + 1
  | _, .recur c h, ρ =>
    Nat.rec 0 (fun j u => val h (Fin.cases j (Fin.cases u ρ))) (val c ρ)

/-- The state of a zero-seeded recursion after `j` updates. -/
def run (h : ZTm (n + 2)) (ρ : Fin n → ℕ) (j : ℕ) : ℕ :=
  Nat.rec 0 (fun j u => h.val (Fin.cases j (Fin.cases u ρ))) j

theorem run_succ (h : ZTm (n + 2)) (ρ : Fin n → ℕ) (j : ℕ) :
    run h ρ (j + 1) = h.val (Fin.cases j (Fin.cases (run h ρ j) ρ)) := rfl

theorem val_rec (c : ZTm n) (h : ZTm (n + 2)) (ρ : Fin n → ℕ) :
    (ZTm.recur c h).val ρ = run h ρ (c.val ρ) := rfl

/-- **Monotonicity.**  Every term of the zero-seeded language denotes a
function that is nondecreasing in each of its variables. -/
theorem mono (t : ZTm n) : ∀ {ρ σ : Fin n → ℕ}, (∀ i, ρ i ≤ σ i) → t.val ρ ≤ t.val σ := by
  induction t with
  | var i => intro ρ σ h; exact h i
  | zero => intro ρ σ _; exact le_rfl
  | succ t ih => intro ρ σ h; exact Nat.succ_le_succ (ih h)
  | recur c h ihc ihh =>
    intro ρ σ hρσ
    have le2 : ∀ {j j' u u' : ℕ} {τ τ' : Fin _ → ℕ}, j ≤ j' → u ≤ u' → (∀ i, τ i ≤ τ' i) →
        h.val (Fin.cases j (Fin.cases u τ)) ≤ h.val (Fin.cases j' (Fin.cases u' τ')) := by
      intro j j' u u' τ τ' hj hu hτ
      refine ihh (Fin.cases ?_ fun i => ?_)
      · exact hj
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact hu
        · exact hτ i
    -- the states of one run are nondecreasing
    have inc : ∀ (τ : Fin _ → ℕ) (j : ℕ), run h τ j ≤ run h τ (j + 1) := by
      intro τ j
      induction j with
      | zero => exact Nat.zero_le _
      | succ j ih =>
        rw [run_succ h τ (j + 1), run_succ h τ j]
        exact le2 (Nat.le_succ j) ih fun _ => le_rfl
    have monoJ : ∀ (τ : Fin _ → ℕ) {j k : ℕ}, j ≤ k → run h τ j ≤ run h τ k := by
      intro τ j k hjk
      induction hjk with
      | refl => exact le_rfl
      | step _ ih => exact le_trans ih (inc τ _)
    -- two runs with comparable parameters are comparable at every stage
    have par : ∀ j : ℕ, run h ρ j ≤ run h σ j := by
      intro j
      induction j with
      | zero => exact le_rfl
      | succ j ih =>
        rw [run_succ, run_succ]
        exact le2 le_rfl ih hρσ
    rw [val_rec, val_rec]
    exact le_trans (par _) (monoJ σ (ihc hρσ))

/-- No term of the zero-seeded language is the zero test. -/
theorem no_zero_test :
    ¬ ∃ t : ZTm 1, t.val (fun _ => 0) = 1 ∧ t.val (fun _ => 1) = 0 := by
  rintro ⟨t, h0, h1⟩
  have h := t.mono (ρ := fun _ => 0) (σ := fun _ => 1) (fun _ => Nat.zero_le _)
  rw [h0, h1] at h
  exact absurd h (by decide)

end ZTm

/-- The zero test is a term of the kernel's language: `sel(x, 1, 0)` has the
value `1` at `0` and `0` at a successor. -/
theorem Tm.val_zf (x : ℕ) :
    (Tm.zf (Syn.var 0) : Tm 1).val .std (fun _ => x) = if x = 0 then 1 else 0 := by
  cases x <;> rfl

end LeanProofs.ConciseIPRA
