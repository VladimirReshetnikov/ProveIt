import IPRADerivations.Combinatorics.FibonacciGcd
import IPRADerivations.Core.Powers
import IPRADerivations.DiophantineNumberTheory.Hurwitz

/-!
# Lucas-number identities

Packet: `combinatorics/fibonacci_lucas_ipra` (the theorems "Basic Lucas relations", "Lucas
multiplication and mixed addition", "d'Ocagne and doubling", "Triple arguments and mixed
determinants" and "Additional sums and a positive inequality"). Notation as in
`Combinatorics/Fibonacci`: `fib k = F_k`, `fibS k = F_{k+1}`, `luc k = L_k`, and the sign `(−1)^k`
is carried by `par k = [k odd]` and `1 ∸ par k = [k even]`, each subtracted term moved to the other
side.

* `luc_zero`, `luc_one`: `L_0 = 2`, `L_1 = 1`;
* `luc_five` (8): `L_{k+2} + L_k = 5 F_{k+1}`;
* `luc_fib_det` (23): `L_k F_{k+1} − L_{k+1} F_k = 2(−1)^k`;
* `luc_double` (5): `L_{2k} = L_k² − 2(−1)^k`;
* `docagne_succ`: d'Ocagne's identity one index up,
  `F_{k+d+1} F_{k+1} − F_{k+d+2} F_k = (−1)^k F_{d+1}`;
* `fib_luc_mul` (10): `F_{k+d} L_k = F_{2k+d} + (−1)^k F_d`;
* `luc_mul` (9): `L_{k+d} L_k = L_{2k+d} + (−1)^k L_d`;
* `sum_luc_sq` (25): `∑_{j≤N} L_j² = L_N L_{N+1} + 2`;
* `fibS_le_pow`, `fib_le_pow`, `luc_le_pow`: `F_{k+1} ≤ 2^k`, `F_k ≤ 2^k`, `L_k ≤ 2^{k+1}`.

All but the last two groups are ring consequences of the addition laws, Cassini's and d'Ocagne's
identities; the sum and the bound are inductions.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.LucasIdentities

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.FibonacciGcd (docagne)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA (par par_succ par_cases par_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Initial values and linear relations -/

theorem luc_zero : Γ ⊢[PRAAx] luc (zero : PTm n) ≐ two := by
  have l := natEq (luc_eq (Γ := Γ) (zero : PTm n))
  have z₁ := natEq (fibS_zero (Γ := Γ)); have z₂ := natEq (fib_zero (Γ := Γ))
  apply deriveNat; ipra_simps
  linear_combination l - z₂ + 2 * z₁

theorem luc_one : Γ ⊢[PRAAx] luc (succ (zero : PTm n)) ≐ one := by
  have l := natEq (luc_succ (Γ := Γ) (zero : PTm n))
  have s₁ := natEq (fibS_succ (Γ := Γ) (zero : PTm n))
  have z₁ := natEq (fibS_zero (Γ := Γ)); have z₂ := natEq (fib_zero (Γ := Γ))
  apply deriveNat; ipra_simps
  linear_combination l + s₁ + z₁ + 2 * z₂

/-- `L_{k+2} + L_k = 5 F_{k+1}`. -/
theorem luc_five (k : PTm n) : Γ ⊢[PRAAx] luc (succ (succ k)) + luc k ≐ (two * two + one) * fibS k := by
  have l₂ := natEq (luc_eq (Γ := Γ) (succ (succ k))); have l₀ := natEq (luc_eq (Γ := Γ) k)
  have t₂ := natEq (fib_succ (Γ := Γ) (succ k)); have s₂ := natEq (fibS_succ (Γ := Γ) (succ k))
  have s₁ := natEq (fibS_succ (Γ := Γ) k); have s₃ := natEq (fib_succ (Γ := Γ) k)
  apply deriveNat; ipra_simps
  linear_combination l₂ + l₀ - t₂ + 2 * s₂ + s₁ + 2 * s₃

/-! ## Determinants and doubling -/

/-- `L_k F_{k+1} + 2[k odd] = L_{k+1} F_k + 2[k even]`, i.e. `L_k F_{k+1} − L_{k+1} F_k = 2(−1)^k`. -/
theorem luc_fib_det (k : PTm n) :
    Γ ⊢[PRAAx] luc k * fibS k + two * par k ≐ luc (succ k) * fib k + two * monus one (par k) := by
  have c := natEq (cassini (Γ := Γ) k); have l := natEq (luc_eq (Γ := Γ) k)
  have ls := natEq (luc_succ (Γ := Γ) k); have s₁ := natEq (fibS_succ (Γ := Γ) k)
  apply deriveNat; ipra_simps
  linear_combination 𝔞(fibS k) * l - 𝔞(fib k) * ls + 𝔞(fib k) * s₁ - 2 * c

/-- `L_{2k} + 2[k even] = L_k² + 2[k odd]`, i.e. `L_{2k} = L_k² − 2(−1)^k`. -/
theorem luc_double (k : PTm n) :
    Γ ⊢[PRAAx] luc (k + k) + two * monus one (par k) ≐ luc k * luc k + two * par k := by
  have l₂ := natEq (luc_eq (Γ := Γ) (k + k)); have d := natEq (fib_double (Γ := Γ) k)
  have fd := natEq (fibS_double (Γ := Γ) k); have l := natEq (luc_eq (Γ := Γ) k)
  have c := natEq (cassini (Γ := Γ) k); have s₁ := natEq (fibS_succ (Γ := Γ) k)
  apply deriveNat; ipra_simps
  linear_combination l₂ - d + 2 * fd -
    (𝔞(fibS k) + 𝔞(monus (fibS k) (fib k)) + 2 * 𝔞(fibS k) - 𝔞(fib k)) * l - 2 * 𝔞(fib k) * s₁ + 2 * c

/-! ## Multiplication laws -/

/-- d'Ocagne one index up:
`F_{k+d+1} F_{k+1} + [k odd] F_{d+1} = F_{k+d+2} F_k + [k even] F_{d+1}`. -/
theorem docagne_succ (k d : PTm n) :
    Γ ⊢[PRAAx] fibS (k + d) * fibS k + par k * fibS d ≐
      fibS (succ (k + d)) * fib k + monus one (par k) * fibS d := by
  have e₁ : Γ ⊢[PRAAx] fib (k + succ d) ≐ fibS (k + d) := (congrFib (add_succ k d)).eqTrans (fib_succ (k + d))
  have e₂ : Γ ⊢[PRAAx] fibS (k + succ d) ≐ fibS (succ (k + d)) := congrFibS (add_succ k d)
  have e₃ : Γ ⊢[PRAAx] fib (succ d) ≐ fibS d := fib_succ d
  exact (congrAdd (congrMul e₁ (.eqRefl _)) (congrMul (.eqRefl _) e₃)).eqSymm.eqTrans
    ((docagne k (succ d)).eqTrans (congrAdd (congrMul e₂ (.eqRefl _)) (congrMul (.eqRefl _) e₃)))

/-- `F_{k+d} L_k + [k odd] F_d = F_{2k+d} + [k even] F_d`, i.e.
`F_m L_k = F_{m+k} + (−1)^k F_{m−k}` for `m = k + d`. -/
theorem fib_luc_mul (k d : PTm n) :
    Γ ⊢[PRAAx] fib (k + d) * luc k + par k * fib d ≐ fib ((k + d) + k) + monus one (par k) * fib d := by
  have as := natEq (fib_add_sym (Γ := Γ) (k + d) k); have doc := natEq (docagne (Γ := Γ) k d)
  have l := natEq (luc_eq (Γ := Γ) k)
  apply deriveNat; ipra_simps
  linear_combination 𝔞(fib (k + d)) * l + doc - as

/-- `L_{k+d} L_k + [k odd] L_d = L_{2k+d} + [k even] L_d`, i.e.
`L_m L_k = L_{m+k} + (−1)^k L_{m−k}` for `m = k + d`. -/
theorem luc_mul (k d : PTm n) :
    Γ ⊢[PRAAx] luc (k + d) * luc k + par k * luc d ≐ luc ((k + d) + k) + monus one (par k) * luc d := by
  have lm := natEq (luc_eq (Γ := Γ) (k + d)); have l := natEq (luc_eq (Γ := Γ) k)
  have ld := natEq (luc_eq (Γ := Γ) d); have lmk := natEq (luc_eq (Γ := Γ) ((k + d) + k))
  have fa := natEq (fibS_add (Γ := Γ) (k + d) k); have as := natEq (fib_add_sym (Γ := Γ) (k + d) k)
  have doc := natEq (docagne (Γ := Γ) k d); have doc' := natEq (docagne_succ (Γ := Γ) k d)
  have sm := natEq (fibS_succ (Γ := Γ) (k + d))
  apply deriveNat; ipra_simps
  linear_combination (𝔞(fibS k) + 𝔞(monus (fibS k) (fib k))) * lm +
    (2 * 𝔞(fibS (k + d)) - 𝔞(fib (k + d))) * l + (𝔞(par k) - 𝔞(monus one (par k))) * ld - lmk + as -
    2 * fa + 2 * doc' - doc + 2 * 𝔞(fib k) * sm

/-! ## The sum of squares -/

abbrev lsqB : PTm 2 := luc (var 0) * luc (var 0)

theorem inst2_lsq (k x : PTm n) : inst2 lsqB k x = luc k * luc k := by simp [inst2]

theorem sum_lsq_base :
    Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ zero) (zero : PTm n) ≐ luc zero * luc (succ zero) + two := by
  have e := sum_succ' (Γ := Γ) lsqB (zero : PTm n) zero
  rw [inst2_lsq] at e
  have a := natEq e; have z := natEq (sum_zero (Γ := Γ) lsqB (zero : PTm n))
  have a₀ := natEq (luc_zero (Γ := Γ)); have a₁ := natEq (luc_one (Γ := Γ))
  apply deriveNat; ipra_simps
  linear_combination a + z + (𝔞(fibS zero) + 𝔞(monus (fibS zero) (fib zero)) + 1) * a₀ -
    (𝔞(fibS zero) + 𝔞(monus (fibS zero) (fib zero))) * a₁

theorem sum_lsq_step {N : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ N) zero ≐ luc N * luc (succ N) + two) :
    Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ (succ N)) zero ≐ luc (succ N) * luc (succ (succ N)) + two := by
  have e := sum_succ' (Γ := Γ) lsqB (succ N) zero
  rw [inst2_lsq] at e
  have a := natEq e; have b := natEq ih; have r := natEq (luc_rec (Γ := Γ) N)
  apply deriveNat; ipra_simps
  linear_combination a + b - (𝔞(fibS (succ N)) + 𝔞(monus (fibS (succ N)) (fib (succ N)))) * r

private abbrev sumLsqF : Fm PTm 1 :=
  ap2 (sumF lsqB) (succ (var 0)) zero ≐ luc (var 0) * luc (succ (var 0)) + two

private theorem sumLsq₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] sumLsqF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_fibS, subst_fib,
      Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact sum_lsq_base
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_fibS, subst_fib,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact sum_lsq_step Prf.hyp0

/-- `∑_{j≤N} L_j² = L_N L_{N+1} + 2`. -/
theorem sum_luc_sq (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ N) zero ≐ luc N * luc (succ N) + two := by
  have h := inst (Γ := Γ) sumLsq₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## Power bounds -/

theorem fibS_pow_step {k : PTm n} (ih : Γ ⊢[PRAAx] le (fibS k) (pw two k)) :
    Γ ⊢[PRAAx] le (fibS (succ k)) (pw two (succ k)) := by
  have e : Γ ⊢[PRAAx] pw two k + pw two k ≐ pw two (succ k) :=
    ((pw_succ two k).eqTrans (by apply deriveNat; ipra_simps; ring)).eqSymm
  exact le_congr (fibS_succ k).eqSymm e (add_le_add ih (le_trans (fib_le k) ih))

private abbrev fpowF : Fm PTm 1 := le (fibS (var 0)) (pw two (var 0))

private theorem fpow₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fpowF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_fibS, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact le_congr fibS_zero.eqSymm (pw_zero two).eqSymm (le_refl one)
  · simp only [subst_le, subst_fibS, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact fibS_pow_step Prf.hyp0

/-- `F_{k+1} ≤ 2^k`. -/
theorem fibS_le_pow (k : PTm n) : Γ ⊢[PRAAx] le (fibS k) (pw two k) := by
  have h := inst (Γ := Γ) fpow₀ (![k] : Fin 1 → PTm n)
  simpa using h

/-- `F_k ≤ 2^k`. -/
theorem fib_le_pow (k : PTm n) : Γ ⊢[PRAAx] le (fib k) (pw two k) := le_trans (fib_le k) (fibS_le_pow k)

/-- `L_k ≤ 2^{k+1}`. -/
theorem luc_le_pow (k : PTm n) : Γ ⊢[PRAAx] le (luc k) (pw two (succ k)) := by
  have e : Γ ⊢[PRAAx] pw two k + pw two k ≐ pw two (succ k) :=
    ((pw_succ two k).eqTrans (by apply deriveNat; ipra_simps; ring)).eqSymm
  have d : Γ ⊢[PRAAx] fibS k + fibS k ≐ two * fibS k := by apply deriveNat; ipra_simps; ring
  exact le_trans (le_of_eq_add (luc_eq k).eqSymm)
    (le_congr d e (add_le_add (fibS_le_pow k) (fibS_le_pow k)))

end LeanProofs.IPRA.Combinatorics.LucasIdentities
