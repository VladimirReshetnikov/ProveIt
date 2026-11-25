import IPRADerivations.Combinatorics.LucasIdentities
import IPRADerivations.Core.LinearCombination

/-!
# The generating functions of the Fibonacci and Lucas numbers

Packet: `combinatorics/fibonacci_lucas_ipra` (theorem "Formal power series, coefficientwise", (16)):
`∑ F_n xⁿ = x/(1 − x − x²)` and `∑ L_n xⁿ = (2 − x)/(1 − x − x²)`, where the division is a finite
coefficient equation. Here they are finite polynomial identities, for an arbitrary `x` and every
truncation `N`, with the remainder written out:

  `(1 − x − x²) ∑_{n ≤ N} F_n xⁿ + F_{N+1} x^{N+1} + F_N x^{N+2} = x`,
  `(1 − x − x²) ∑_{n ≤ N} L_n xⁿ + L_{N+1} x^{N+1} + L_N x^{N+2} = 2 − x`,

in natural-number form (`fib_series`, `luc_series`), by induction on `N`. Comparing coefficients of
`xⁿ` for `n ≤ N` gives the coefficient identities of (16).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciSeries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.LucasIdentities (luc_zero luc_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `F_n xⁿ`, over `0 = n`, `1 = x`. -/
abbrev fxB : PTm 2 := fib (var 0) * pw (var 1) (var 0)
/-- `L_n xⁿ`. -/
abbrev lxB : PTm 2 := luc (var 0) * pw (var 1) (var 0)

theorem inst2_fx (k x : PTm n) : inst2 fxB k x = fib k * pw x k := by simp [inst2]
theorem inst2_lx (k x : PTm n) : inst2 lxB k x = luc k * pw x k := by simp [inst2]

/-- `P(N) = ∑_{n ≤ N} F_n xⁿ`. -/
abbrev Pf {n : ℕ} (N x : PTm n) : PTm n := ap2 (sumF fxB) (succ N) x
/-- `Q(N) = ∑_{n ≤ N} L_n xⁿ`. -/
abbrev Ql {n : ℕ} (N x : PTm n) : PTm n := ap2 (sumF lxB) (succ N) x

/-- The Fibonacci identity at `N`, cleared of subtraction. -/
abbrev fibF {n : ℕ} (N x : PTm n) : Fm PTm n :=
  Pf N x + fib (succ N) * pw x (succ N) + fib N * pw x (succ (succ N)) ≐ x + x * Pf N x + x * x * Pf N x

/-- The Lucas identity at `N`, cleared of subtraction. -/
abbrev lucF {n : ℕ} (N x : PTm n) : Fm PTm n :=
  Ql N x + luc (succ N) * pw x (succ N) + luc N * pw x (succ (succ N)) + x ≐ two + x * Ql N x + x * x * Ql N x

theorem fib_base (x : PTm n) : Γ ⊢[PRAAx] fibF zero x := by
  have s := sum_succ' (Γ := Γ) fxB zero x
  rw [inst2_fx] at s
  ipra_lc (1 - 𝔞 x - 𝔞 x * 𝔞 x) * (natEq s + natEq (sum_zero (Γ := Γ) fxB x)) +
    ((1 - 𝔞 x - 𝔞 x * 𝔞 x) * 𝔞 (pw x zero) + 𝔞 (pw x (succ (succ zero)))) * natEq (fib_zero (Γ := Γ) (n := n)) +
    𝔞 (pw x (succ zero)) * natEq ((fib_succ (Γ := Γ) (zero : PTm n)).eqTrans fibS_zero) + natEq (pw_one (Γ := Γ) x)

theorem fib_step {N x : PTm n} (ih : Γ ⊢[PRAAx] fibF N x) : Γ ⊢[PRAAx] fibF (succ N) x := by
  have s := sum_succ' (Γ := Γ) fxB (succ N) x
  rw [inst2_fx] at s
  ipra_lc (1 - 𝔞 x - 𝔞 x * 𝔞 x) * natEq s + natEq ih +
    𝔞 (pw x (succ (succ N))) * (natEq (fib_succ (Γ := Γ) (succ N)) + natEq (fibS_succ (Γ := Γ) N) - natEq (fib_succ (Γ := Γ) N)) +
    𝔞 (fib (succ N)) * (natEq (pw_succ (Γ := Γ) x (succ (succ N))) + natEq (pw_succ (Γ := Γ) x (succ N)) + 𝔞 x * natEq (pw_succ (Γ := Γ) x (succ N)))

theorem luc_base (x : PTm n) : Γ ⊢[PRAAx] lucF zero x := by
  have s := sum_succ' (Γ := Γ) lxB zero x
  rw [inst2_lx] at s
  ipra_lc (1 - 𝔞 x - 𝔞 x * 𝔞 x) * (natEq s + natEq (sum_zero (Γ := Γ) lxB x) + 𝔞 (pw x zero) * natEq (luc_zero (Γ := Γ) (n := n)) + 2 * natEq (pw_zero (Γ := Γ) x)) +
    𝔞 (pw x (succ zero)) * natEq (luc_one (Γ := Γ) (n := n)) + natEq (pw_one (Γ := Γ) x) +
    𝔞 (pw x (succ (succ zero))) * natEq (luc_zero (Γ := Γ) (n := n)) + 2 * natEq (pw_succ (Γ := Γ) x (succ zero)) +
    2 * 𝔞 x * natEq (pw_one (Γ := Γ) x)

theorem luc_step {N x : PTm n} (ih : Γ ⊢[PRAAx] lucF N x) : Γ ⊢[PRAAx] lucF (succ N) x := by
  have s := sum_succ' (Γ := Γ) lxB (succ N) x
  rw [inst2_lx] at s
  ipra_lc (1 - 𝔞 x - 𝔞 x * 𝔞 x) * natEq s + natEq ih + 𝔞 (pw x (succ (succ N))) * natEq (luc_rec (Γ := Γ) N) +
    (𝔞 (fibS (succ N)) + 𝔞 (monus (fibS (succ N)) (fib (succ N)))) * (natEq (pw_succ (Γ := Γ) x (succ (succ N))) + natEq (pw_succ (Γ := Γ) x (succ N)) + 𝔞 x * natEq (pw_succ (Γ := Γ) x (succ N)))

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev fibSF : Fm PTm 2 := fibF (var 0) (var 1)
private abbrev lucSF : Fm PTm 2 := lucF (var 0) (var 1)

private theorem fib₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] fibSF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, subst_fib, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fib_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, subst_fib, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fib_step Prf.hyp0

private theorem luc₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] lucSF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fib, subst_fibS,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact luc_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fib, subst_fibS,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact luc_step Prf.hyp0

/-- (16) for `F`: `(1 − x − x²) ∑_{n ≤ N} F_n xⁿ + F_{N+1} x^{N+1} + F_N x^{N+2} = x`. -/
theorem fib_series (N x : PTm n) : Γ ⊢[PRAAx] fibF N x := by
  have h := inst (Γ := Γ) fib₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

/-- (16) for `L`: `(1 − x − x²) ∑_{n ≤ N} L_n xⁿ + L_{N+1} x^{N+1} + L_N x^{N+2} = 2 − x`. -/
theorem luc_series (N x : PTm n) : Γ ⊢[PRAAx] lucF N x := by
  have h := inst (Γ := Γ) luc₀ (![N, x] : Fin 2 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.FibonacciSeries
