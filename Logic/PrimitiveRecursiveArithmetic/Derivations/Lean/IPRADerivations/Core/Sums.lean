import IPRADerivations.Core.Definitions

/-!
# Finite sums by induction inside iPRA

Theorems whose summation bound is a free variable of the iPRA formula, each
derived by quantifier-free induction on that variable:

* Gauss: `2 ∑_{i<n} i + n = n²`, and `∑_{i<n} (2i + 1) = n²`;
* telescoping, for every unary primitive recursive symbol `f`:
  `∑_{i<n} f(i + 1) + f(0) = f(n) + ∑_{i<n} f(i)`;
* summation by parts (Abel), for all unary primitive recursive `a, b`, with
  `A(n) = ∑_{i<n} a(i)`:
  `∑_{i<n} a(i) b(i) + ∑_{i<n} A(i+1) b(i+1) = A(n) b(n) + ∑_{i<n} A(i+1) b(i)`,
  the natural-number form of
  `∑ a(i) b(i) = A(n) b(n) − ∑_{i<n} A(i+1) (b(i+1) − b(i))`.

The sums take a parameter `x`; here it is unused and instantiated by `0`.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

/-- The simp set normalising substitutions into the terms built here. -/
macro "ipra_subst" : tactic =>
  `(tactic| simp only [Fm.subst_eq, Fm.subst_imp, PTm.subst_add, PTm.subst_mul, subst_ap1,
      subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_succ, Syn.repl_zero, Syn.repl_succ,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, inst_two, repl_one, repl_two])

namespace Sums

/-- `T(n) = ∑_{i<n} i`. -/
abbrev triF : PR 2 := sumF (var 0)

/-- `2 T(n) + n = n²`. -/
abbrev gaussFormula : Fm PTm 1 :=
  succ (succ zero) * ap2 triF (var 0) zero + var 0 ≐ var 0 * var 0

theorem gauss_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] gaussFormula := by
  refine ind _ trivial ?_ ?_
  · ipra_subst
    apply deriveNat
    have e := natEq (sum_zero (Γ := []) (var 0) (zero : PTm 0))
    ipra_simps
    linear_combination 2 * e
  · ipra_subst
    apply deriveNat
    have h := natEq (Γ := [gaussFormula]) Prf.hyp0
    have e := natEq (sum_succ (Γ := [gaussFormula]) (var 0) (var 0) zero)
    simp only [Syn.subst_var, Matrix.cons_val_zero] at e
    ipra_simps
    linear_combination h + 2 * e

/-- Gauss's sum, as a closed iPRA theorem. -/
theorem gauss : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 gaussFormula := closeUniv 1 gauss_open

/-- `∑_{i<n} (2i + 1)`. -/
abbrev oddF : PR 2 := sumF (succ (succ zero) * var 0 + succ zero)

/-- `∑_{i<n} (2i + 1) = n²`. -/
abbrev oddFormula : Fm PTm 1 := ap2 oddF (var 0) zero ≐ var 0 * var 0

theorem odd_sum : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 oddFormula := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · ipra_subst
    apply deriveNat
    have e := natEq (sum_zero (Γ := []) (succ (succ zero) * var 0 + succ zero) (zero : PTm 0))
    ipra_simps
    linear_combination e
  · ipra_subst
    apply deriveNat
    have h := natEq (Γ := [oddFormula]) Prf.hyp0
    have e := natEq (sum_succ (Γ := [oddFormula]) (succ (succ zero) * var 0 + succ zero) (var 0) zero)
    simp only [PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_zero] at e
    ipra_simps
    linear_combination h + e

/-! ## Telescoping and summation by parts, for arbitrary symbols -/

section Schemas

variable (f a b : PR 1)

/-- `∑_{i<n} f(i + 1)`. -/
abbrev shiftSumF : PR 2 := sumF (ap1 f (succ (var 0)))
/-- `∑_{i<n} f(i)`. -/
abbrev plainSumF : PR 2 := sumF (ap1 f (var 0))

/-- `∑_{i<n} f(i + 1) + f(0) = f(n) + ∑_{i<n} f(i)`. -/
abbrev telescopeFormula : Fm PTm 1 :=
  ap2 (shiftSumF f) (var 0) zero + ap1 f zero ≐ ap1 f (var 0) + ap2 (plainSumF f) (var 0) zero

theorem telescope : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (telescopeFormula f) := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · ipra_subst
    apply deriveNat
    have e₁ := natEq (sum_zero (Γ := []) (ap1 f (succ (var 0))) (zero : PTm 0))
    have e₂ := natEq (sum_zero (Γ := []) (ap1 f (var 0)) (zero : PTm 0))
    ipra_simps
    linear_combination e₁ - e₂
  · ipra_subst
    apply deriveNat
    have h := natEq (Γ := [telescopeFormula f]) Prf.hyp0
    have e₁ := natEq (sum_succ (Γ := [telescopeFormula f]) (ap1 f (succ (var 0))) (var 0) zero)
    have e₂ := natEq (sum_succ (Γ := [telescopeFormula f]) (ap1 f (var 0)) (var 0) zero)
    simp only [subst_ap1, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Matrix.cons_val_zero] at e₁ e₂
    ipra_simps
    linear_combination h + e₁ - e₂

/-- `A(n) = ∑_{i<n} a(i)`. -/
abbrev partialF : PR 2 := sumF (ap1 a (var 0))
/-- `∑_{i<n} a(i) b(i)`. -/
abbrev abF : PR 2 := sumF (ap1 a (var 0) * ap1 b (var 0))
/-- `∑_{i<n} A(i+1) b(i+1)`. -/
abbrev AbNextF : PR 2 := sumF (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (succ (var 0)))
/-- `∑_{i<n} A(i+1) b(i)`. -/
abbrev AbHereF : PR 2 := sumF (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (var 0))

/-- Summation by parts. -/
abbrev abelFormula : Fm PTm 1 :=
  ap2 (abF a b) (var 0) zero + ap2 (AbNextF a b) (var 0) zero
    ≐ ap2 (partialF a) (var 0) zero * ap1 b (var 0) + ap2 (AbHereF a b) (var 0) zero

theorem abel_summation : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (abelFormula a b) := by
  refine closeUniv 1 (ind _ trivial ?_ ?_)
  · ipra_subst
    apply deriveNat
    have e₁ := natEq (sum_zero (Γ := []) (ap1 a (var 0) * ap1 b (var 0)) (zero : PTm 0))
    have e₂ := natEq (sum_zero (Γ := [])
      (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (succ (var 0))) (zero : PTm 0))
    have e₃ := natEq (sum_zero (Γ := []) (ap1 a (var 0)) (zero : PTm 0))
    have e₄ := natEq (sum_zero (Γ := [])
      (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (var 0)) (zero : PTm 0))
    ipra_simps
    linear_combination e₁ + e₂ - Groth.ι (Q.mk [] (ap1 b zero)) * e₃ - e₄
  · ipra_subst
    apply deriveNat
    have h := natEq (Γ := [abelFormula a b]) Prf.hyp0
    have e₁ := natEq (sum_succ (Γ := [abelFormula a b]) (ap1 a (var 0) * ap1 b (var 0)) (var 0) zero)
    have e₂ := natEq (sum_succ (Γ := [abelFormula a b])
      (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (succ (var 0))) (var 0) zero)
    have e₃ := natEq (sum_succ (Γ := [abelFormula a b])
      (ap2 (partialF a) (succ (var 0)) (var 1) * ap1 b (var 0)) (var 0) zero)
    have e₄ := natEq (sum_succ (Γ := [abelFormula a b]) (ap1 a (var 0)) (var 0) zero)
    simp only [PTm.subst_mul, subst_ap1, subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] at e₁ e₂ e₃ e₄
    ipra_simps
    linear_combination h + e₁ + e₂ - e₃ -
      Groth.ι (Q.mk [abelFormula a b] (ap1 b (var 0))) * e₄

end Schemas

end Sums

end LeanProofs.IPRA
