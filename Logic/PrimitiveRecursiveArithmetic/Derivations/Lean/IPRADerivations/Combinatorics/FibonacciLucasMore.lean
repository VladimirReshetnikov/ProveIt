import IPRADerivations.Combinatorics.LucasIdentities
import IPRADerivations.Core.ParityArith

/-!
# Further Fibonacci and Lucas identities (`fibonacci_lucas_ipra`, (11), (17), (25))

Packet: `combinatorics/fibonacci_lucas_ipra`. With `fib n = F_n`, `fibS n = F_{n+1}` and
`luc n = L_n` of `Combinatorics/Fibonacci`, in natural numbers and for arbitrary terms:

* `luc_add` ((11)): `L_{m+1+n} = L_{m+1} F_{n+1} + L_m F_n`, the addition law
  `L_{m+n} = L_m F_{n+1} + L_{m−1} F_n` for `m ≥ 1` with the index shifted;
* `luc_parity_eq`: `L_k` and `F_k` have the same parity, because `L_k + F_k = 2 F_{k+1}`;
* `luc_parity_zero`, `luc_parity_one`, `luc_parity_two` ((17) for the Lucas numbers):
  `L_{3k}` is even, `L_{3k+1}` and `L_{3k+2}` are odd;
* `fib_luc_sum` ((25)): `∑_{k≤N} F_k L_k + 1 = F_{2N+1}`, from `F_k L_k = F_{2k}`;
* `fib_strict` ((25)): `F_{m+2} + 1 ≤ F_{m+3}`, that is `F_n < F_{n+1}` for `n ≥ 2`.

Closed forms: `luc_add_closed`, `luc_parity_closed`, `fib_luc_sum_closed`,
`fib_strict_closed`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FibonacciLucasMore

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.FibonacciGcd (fibS_pos)
open LeanProofs.IPRA.Combinatorics.LucasIdentities (fib_parity fib_parity_one fib_parity_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The addition law of the Lucas numbers -/

/-- `L_{m+1+n} = L_{m+1} F_{n+1} + L_m F_n`. -/
theorem luc_add (m k : PTm n) :
    Γ ⊢[PRAAx] luc (succ (m + k)) ≐ luc (succ m) * fibS k + luc m * fib k := by
  ipra_lc natEq (luc_succ (Γ := Γ) (m + k)) + natEq (fibS_add (Γ := Γ) (succ m) k) -
    natEq (congrFibS (succ_add (Γ := Γ) m k)) + 𝔞 (fib k) * natEq (fib_succ (Γ := Γ) m) +
    natEq (fib_add_sym (Γ := Γ) m k) - 𝔞 (fibS k) * natEq (luc_succ (Γ := Γ) m) -
    𝔞 (fib k) * natEq (luc_eq (Γ := Γ) m)

/-! ## Parities -/

/-- `L_k` and `F_k` have the same parity. -/
theorem luc_parity_eq (k : PTm n) : Γ ⊢[PRAAx] par (luc k) ≐ par (fib k) :=
  par_eq_of_add_even ((congrAp1 parF (luc_eq k)).eqTrans (par_double _))

/-- `L_{3k}` is even. -/
theorem luc_parity_zero (k : PTm n) : Γ ⊢[PRAAx] par (luc (k + k + k)) ≐ zero :=
  (luc_parity_eq _).eqTrans (Prf.andE₁ (fib_parity k))

/-- `L_{3k+1}` is odd. -/
theorem luc_parity_one (k : PTm n) : Γ ⊢[PRAAx] par (luc (succ (k + k + k))) ≐ one :=
  (luc_parity_eq _).eqTrans (fib_parity_one k)

/-- `L_{3k+2}` is odd. -/
theorem luc_parity_two (k : PTm n) : Γ ⊢[PRAAx] par (luc (succ (succ (k + k + k)))) ≐ one :=
  (luc_parity_eq _).eqTrans (fib_parity_two k)

/-! ## The sum of the products `F_k L_k` -/

/-- The body `F_k L_k`. -/
abbrev flB : PTm 2 := fib (var 0) * luc (var 0)

theorem inst2_fl (k x : PTm n) : inst2 flB k x = fib k * luc k := by simp [inst2]

theorem fib_luc_term (k : PTm n) : Γ ⊢[PRAAx] fib k * luc k ≐ fib (two * k) := by
  have e : Γ ⊢[PRAAx] two * k ≐ k + k := by ipra_ring
  exact (fib_double_luc k).eqSymm.eqTrans (congrFib e.eqSymm)

/-- `∑_{k≤N} F_k L_k + 1 = F_{2N+1}`. -/
theorem fib_luc_sum (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF flB) (succ N) zero + one ≐ fibS (two * N) := by
  have hc : Γ ⊢[PRAAx] ap2 (sumF flB) (succ N) zero ≐ ap2 (sumF feB) (succ N) zero := by
    refine sum_congr_bounded flB feB zero zero (succ N) (.allI (.impI ?_))
    rw [inst2_fl, inst2_fe]
    exact fib_luc_term _
  exact (congrAdd hc (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (fib_sums N))))

/-! ## Strict growth -/

/-- `F_{m+2} + 1 ≤ F_{m+3}`. -/
theorem fib_strict (m : PTm n) :
    Γ ⊢[PRAAx] le (succ (fibS (succ m))) (fibS (succ (succ m))) := by
  refine le_of_eq_add (d := pred (fibS m)) ?_
  ipra_lc natEq (fibS_succ (Γ := Γ) (succ m)) + natEq (fib_succ (Γ := Γ) m) + natEq (fibS_pos (Γ := Γ) m)

/-! ## Closed forms -/

/-- Variables: `0 = m`, `1 = k`. -/
abbrev lucAddFormula : Fm PTm 2 :=
  luc (succ (var 0 + var 1)) ≐ luc (succ (var 0)) * fibS (var 1) + luc (var 0) * fib (var 1)

theorem luc_add_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 lucAddFormula :=
  closeUniv 2 (luc_add (var 0) (var 1))

/-- Variable: `0 = k`. -/
abbrev lucParityFormula : Fm PTm 1 :=
  (par (luc (var 0 + var 0 + var 0)) ≐ zero) ⋏
    ((par (luc (succ (var 0 + var 0 + var 0))) ≐ one) ⋏
      (par (luc (succ (succ (var 0 + var 0 + var 0)))) ≐ one))

theorem luc_parity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 lucParityFormula :=
  closeUniv 1 (.andI (luc_parity_zero _) (.andI (luc_parity_one _) (luc_parity_two _)))

/-- Variable: `0 = N`. -/
abbrev fibLucSumFormula : Fm PTm 1 :=
  ap2 (sumF flB) (succ (var 0)) zero + one ≐ fibS (two * var 0)

theorem fib_luc_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 fibLucSumFormula :=
  closeUniv 1 (fib_luc_sum (var 0))

/-- Variable: `0 = m`. -/
abbrev fibStrictFormula : Fm PTm 1 :=
  le (succ (fibS (succ (var 0)))) (fibS (succ (succ (var 0))))

theorem fib_strict_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 fibStrictFormula :=
  closeUniv 1 (fib_strict (var 0))

end LeanProofs.IPRA.Combinatorics.FibonacciLucasMore
