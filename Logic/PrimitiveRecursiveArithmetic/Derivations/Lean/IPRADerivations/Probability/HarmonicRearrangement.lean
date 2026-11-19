import IPRADerivations.Probability.Independence
import IPRADerivations.Core.OrderCertificates

/-!
# Finite harmonic identities behind the rearranged alternating series

Packet: `probability/expected_value_ipra_2026-11-16`, Theorem `thm:rearrange` ("A concrete rearrangement
changes the sum"), the finite identity of its proof: after `N` blocks of two positive terms and one
negative term,

`R_N = ∑_{k=1}^{2N} 1/(2k − 1) − ½ H_N = H_{4N} − ½ H_{2N} − ½ H_N`,

and the companion identity for the alternating harmonic sums of `prop:alt-harmonic`,
`A_{2N} = H_{2N} − H_N`.

The unit fractions are a body `g(k, x)` standing for `F/(k + 1)` (cleared by a common multiple `F`); the
only property used is the halving `g(k) = 2 g(2k + 1)`, i.e. `F/(k + 1) = 2 F/(2k + 2)`.

* `evB g`, `odB g`: the terms `g(2k)` (odd denominators) and `g(2k + 1)` (even denominators);
* `parity_split`: `∑_{k<M} g(2k) + ∑_{k<M} g(2k + 1) = ∑_{k<2M} g(k)` for every body `g`;
* `halving`: if `g(k) = 2 g(2k + 1)` for `k < M`, then `∑_{k<M} g(k) = 2 ∑_{k<M} g(2k + 1)`, i.e. the
  even denominators through `2M` sum to `½ H_M`;
* `alt_harmonic`: `∑_{k<N} g(2k) + ∑_{k<N} g(k) = ∑_{k<N} g(2k + 1) + ∑_{k<2N} g(k)`, i.e.
  `A_{2N} = H_{2N} − H_N`;
* `odd_sum`: `2 ∑_{k<M} g(2k) + ∑_{k<M} g(k) = 2 ∑_{k<2M} g(k)`, i.e.
  `∑_{k ≤ M} 1/(2k − 1) = H_{2M} − ½ H_M`; at `M = 2N` this is the first equality above, and subtracting
  `½ H_N` gives `R_N`.

The limits (`log 2` and `(3/2) log 2`) are not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.HarmonicRearrangement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

section Harmonic

variable (g : PTm 2)

/-- `g(2k, x)`. -/
def evB : PTm 2 := Syn.subst ![two * var 0, var 1] g
/-- `g(2k + 1, x)`. -/
def odB : PTm 2 := Syn.subst ![succ (two * var 0), var 1] g

theorem inst2_evB (k x : PTm n) : inst2 (evB g) k x = inst2 g (two * k) x := by
  simp only [inst2, evB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem inst2_odB (k x : PTm n) : inst2 (odB g) k x = inst2 g (succ (two * k)) x := by
  simp only [inst2, odB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem split_base (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (evB g)) zero x + ap2 (sumF (odB g)) zero x ≐ ap2 (sumF g) (two * zero) x := by
  have z₁ := natEq (sum_zero (Γ := Γ) (evB g) x)
  have z₂ := natEq (sum_zero (Γ := Γ) (odB g) x)
  have z₃ := natEq ((congrAp2 (sumF g) (mul_zero (Γ := Γ) (two : PTm n)) (.eqRefl x)).eqTrans
    (sum_zero g x))
  apply deriveNat; ipra_simps
  linear_combination z₁ + z₂ - z₃

theorem split_step {M x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (evB g)) M x + ap2 (sumF (odB g)) M x ≐ ap2 (sumF g) (two * M) x) :
    Γ ⊢[PRAAx] ap2 (sumF (evB g)) (succ M) x + ap2 (sumF (odB g)) (succ M) x ≐
      ap2 (sumF g) (two * succ M) x := by
  have s₁ := sum_succ' (Γ := Γ) (evB g) M x
  rw [inst2_evB] at s₁
  have s₂ := sum_succ' (Γ := Γ) (odB g) M x
  rw [inst2_odB] at s₂
  have e₂ : Γ ⊢[PRAAx] two * succ M ≐ succ (succ (two * M)) := by
    apply deriveNat; ipra_simps; ring
  have c := natEq (congrAp2 (sumF g) e₂ (.eqRefl x))
  have t₁ := natEq (sum_succ' (Γ := Γ) g (succ (two * M)) x)
  have t₂ := natEq (sum_succ' (Γ := Γ) g (two * M) x)
  have a₁ := natEq s₁; have a₂ := natEq s₂
  have h := natEq ih
  apply deriveNat; ipra_simps
  linear_combination a₁ + a₂ + h - c - t₁ - t₂

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev splitF : Fm PTm 2 :=
  ap2 (sumF (evB g)) (var 0) (var 1) + ap2 (sumF (odB g)) (var 0) (var 1) ≐
    ap2 (sumF g) (two * var 0) (var 1)

private theorem split₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] splitF g := by
  refine ind _ trivial ?_ ?_
  · have e : (splitF g).subst (Syn.inst zero) =
        (ap2 (sumF (evB g)) zero (var 0) + ap2 (sumF (odB g)) zero (var 0) ≐
          ap2 (sumF g) (two * zero) (var 0) : Fm PTm 1) := by
      simp
    rw [e]
    exact split_base g _
  · have e : (splitF g).subst (repl (succ (var 0))) =
        (ap2 (sumF (evB g)) (succ (var 0)) (var 1) + ap2 (sumF (odB g)) (succ (var 0)) (var 1) ≐
          ap2 (sumF g) (two * succ (var 0)) (var 1) : Fm PTm 2) := by
      simp
    rw [e]
    exact split_step g Prf.hyp0

/-- `∑_{k<M} g(2k) + ∑_{k<M} g(2k + 1) = ∑_{k<2M} g(k)`. -/
theorem parity_split (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (evB g)) M x + ap2 (sumF (odB g)) M x ≐ ap2 (sumF g) (two * M) x := by
  have h := inst (Γ := Γ) (split₀ g) (![M, x] : Fin 2 → PTm n)
  simpa using h

/-- If `g(k) = 2 g(2k + 1)` for `k < M`, then `∑_{k<M} g(k) = 2 ∑_{k<M} g(2k + 1)`. -/
theorem halving {M x : PTm n}
    (hh : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (inst2 g (var 0) (Syn.shift x) ≐ two * inst2 g (succ (two * var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF g) M x ≐ two * ap2 (sumF (odB g)) M x := by
  refine sum_scale g (odB g) M two x x (.allI (.impI ?_))
  have e : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
  rw [e, inst2_odB]
  exact Prf.impE hh.allOpen.wk Prf.hyp0

/-- `A_{2N} = H_{2N} − H_N`:
`∑_{k<N} g(2k) + ∑_{k<N} g(k) = ∑_{k<N} g(2k + 1) + ∑_{k<2N} g(k)`. -/
theorem alt_harmonic {N x : PTm n}
    (hh : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 g (var 0) (Syn.shift x) ≐ two * inst2 g (succ (two * var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] ap2 (sumF (evB g)) N x + ap2 (sumF g) N x ≐
      ap2 (sumF (odB g)) N x + ap2 (sumF g) (two * N) x := by
  have s := natEq (parity_split (Γ := Γ) g N x)
  have h := natEq (halving g hh)
  apply deriveNat; ipra_simps
  linear_combination s + h

/-- `∑_{k ≤ M} 1/(2k − 1) = H_{2M} − ½ H_M`:
`2 ∑_{k<M} g(2k) + ∑_{k<M} g(k) = 2 ∑_{k<2M} g(k)`. -/
theorem odd_sum {M x : PTm n}
    (hh : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      (inst2 g (var 0) (Syn.shift x) ≐ two * inst2 g (succ (two * var 0)) (Syn.shift x)))) :
    Γ ⊢[PRAAx] two * ap2 (sumF (evB g)) M x + ap2 (sumF g) M x ≐ two * ap2 (sumF g) (two * M) x := by
  have s := natEq (parity_split (Γ := Γ) g M x)
  have h := natEq (halving g hh)
  apply deriveNat; ipra_simps
  linear_combination 2 * s + h

end Harmonic

end LeanProofs.IPRA.Probability.HarmonicRearrangement
