import IPRADerivations.Combinatorics.CatalanGrowth
import IPRADerivations.Core.LinearCombination

/-!
# The Wallis bounds for the central binomial coefficient

Packet: `combinatorics/Combinatorics-iPRA`, `analytic.tex`, result 14 ("Wallis bounds and relative error"). With
`a_n = 4^n / C(2n, n)`, `L_n = 2 a_n² / (2n + 1)` and `U_n = a_n² / n`, the proof uses: "Also
`a_{n+1}/a_n = 2(n + 1)/(2n + 1)`, so `L_{n+1}/L_n = (2n + 2)²/((2n + 1)(2n + 3)) > 1` and
`U_{n+1}/U_n = 4n(n + 1)/(2n + 1)² < 1`. The width is `U_n/(2n + 1) ≤ U_1/(2n + 1) = 4/(2n + 1)`."

Cleared of denominators, with `cb n = C(2n, n)` of `Combinatorics/Catalan` and its recurrence
`(n + 1) C(2n + 2, n + 1) = 2 (2n + 1) C(2n, n)` (`cb_rec`), uniformly in the term `k` (`n = k + 1 ≥ 1`), by
induction in iPRA:

* `cb_one`: `C(2, 1) = 2`;
* `wallis_upper`: `U_n ≤ U_1 = 4`, that is `16^n ≤ 4 n C(2n, n)²`;
* `wallis_lower`: `L_n ≥ L_1 = 8/3`, that is `4 (2n + 1) C(2n, n)² ≤ 3 · 16^n`.

Together: `4^n / (2 √n) ≤ C(2n, n)` and `C(2n, n)² ≤ 3 · 16^n / (4 (2n + 1))`, sharper than the bounds
`4^n/(2n + 1) ≤ C(2n, n) ≤ 4^n` of `Combinatorics/CentralBinomial`. Not derived: the integrals `I_j`, the
identification of the limit with `π`, and the relative-error estimates for the Catalan numbers.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.WallisCentral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Catalan
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `4`. -/
abbrev four : PTm n := two * two

/-- `16`. -/
abbrev sixteen : PTm n := (two * two) * (two * two)

/-- `3`. -/
abbrev three : PTm n := succ two

/-- `C(2, 1) = 2`. -/
theorem cb_one : Γ ⊢[PRAAx] cb (succ (zero : PTm n)) ≐ two := by
  ipra_lc natEq (cb_rec (Γ := Γ) zero) + 2 * natEq (cb_zero (Γ := Γ))

/-! ## The upper bound -/

theorem upper_base :
    Γ ⊢[PRAAx] le (pw sixteen (succ (zero : PTm n)))
      (four * succ zero * (cb (succ zero) * cb (succ zero))) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc -natEq (pw_succ (Γ := Γ) sixteen zero) - 16 * natEq (pw_zero (Γ := Γ) sixteen) +
    4 * (𝔞 (cb (succ (zero : PTm n))) + 2) * natEq (cb_one (Γ := Γ))

theorem upper_step {k : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw sixteen (succ k)) (four * succ k * (cb (succ k) * cb (succ k)))) :
    Γ ⊢[PRAAx] le (pw sixteen (succ (succ k)))
      (four * succ (succ k) * (cb (succ (succ k)) * cb (succ (succ k)))) := by
  refine mul_le_cancel (d' := succ k) (le_of_eq_add (d := sixteen * (cb (succ k) * cb (succ k)) +
    sixteen * succ (succ k) *
      monus (four * succ k * (cb (succ k) * cb (succ k))) (pw sixteen (succ k))) ?_)
  ipra_lc (-(𝔞 k + 2)) * natEq (pw_succ (Γ := Γ) sixteen (succ k)) + 16 * (𝔞 k + 2) * natEq (eq_add_of_le ih) +
    4 * ((𝔞 k + 2) * 𝔞 (cb (succ (succ k))) + 2 * (2 * 𝔞 k + 3) * 𝔞 (cb (succ k))) * natEq (cb_rec (Γ := Γ) (succ k))

/-- Variable: `0 = k`. -/
private abbrev upF : Fm PTm 1 :=
  le (pw sixteen (succ (var 0))) (four * succ (var 0) * (cb (succ (var 0)) * cb (succ (var 0))))

private theorem up₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] upF := by
  refine ind _ trivial ?_ ?_
  · simp only [subst_le, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact upper_base
  · simp only [subst_le, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact upper_step Prf.hyp0

/-- `16^n ≤ 4 n C(2n, n)²` for `n = k + 1`. -/
theorem wallis_upper (k : PTm n) :
    Γ ⊢[PRAAx] le (pw sixteen (succ k)) (four * succ k * (cb (succ k) * cb (succ k))) := by
  have h := inst (Γ := Γ) up₀ (![k] : Fin 1 → PTm n)
  simpa using h

/-! ## The lower bound -/

theorem lower_base :
    Γ ⊢[PRAAx] le (four * succ (two * succ (zero : PTm n)) * (cb (succ zero) * cb (succ zero)))
      (three * pw sixteen (succ zero)) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc 3 * natEq (pw_succ (Γ := Γ) sixteen zero) + 48 * natEq (pw_zero (Γ := Γ) sixteen) -
    12 * (𝔞 (cb (succ (zero : PTm n))) + 2) * natEq (cb_one (Γ := Γ))

theorem lower_step {k : PTm n}
    (ih : Γ ⊢[PRAAx] le (four * succ (two * succ k) * (cb (succ k) * cb (succ k)))
      (three * pw sixteen (succ k))) :
    Γ ⊢[PRAAx] le (four * succ (two * succ (succ k)) * (cb (succ (succ k)) * cb (succ (succ k))))
      (three * pw sixteen (succ (succ k))) := by
  refine mul_le_cancel (d' := succ k) (mul_le_cancel (d' := succ k)
    (le_of_eq_add (d := sixteen * succ (two * succ k) * (cb (succ k) * cb (succ k)) +
      sixteen * (succ (succ k) * succ (succ k)) *
        monus (three * pw sixteen (succ k))
          (four * succ (two * succ k) * (cb (succ k) * cb (succ k)))) ?_))
  ipra_lc (3 * (𝔞 k + 2) ^ 2) * natEq (pw_succ (Γ := Γ) sixteen (succ k)) +
    (16 * (𝔞 k + 2) ^ 2) * natEq (eq_add_of_le ih) -
    (4 * (2 * (𝔞 k + 2) + 1) * ((𝔞 k + 2) * 𝔞 (cb (succ (succ k))) + 2 * (2 * 𝔞 k + 3) * 𝔞 (cb (succ k)))) * natEq (cb_rec (Γ := Γ) (succ k))

/-- Variable: `0 = k`. -/
private abbrev loF : Fm PTm 1 :=
  le (four * succ (two * succ (var 0)) * (cb (succ (var 0)) * cb (succ (var 0))))
    (three * pw sixteen (succ (var 0)))

private theorem lo₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] loF := by
  refine ind _ trivial ?_ ?_
  · simp only [subst_le, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lower_base
  · simp only [subst_le, Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2,
      Syn.subst_var, Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact lower_step Prf.hyp0

/-- `4 (2n + 1) C(2n, n)² ≤ 3 · 16^n` for `n = k + 1`. -/
theorem wallis_lower (k : PTm n) :
    Γ ⊢[PRAAx] le (four * succ (two * succ k) * (cb (succ k) * cb (succ k)))
      (three * pw sixteen (succ k)) := by
  have h := inst (Γ := Γ) lo₀ (![k] : Fin 1 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.WallisCentral
