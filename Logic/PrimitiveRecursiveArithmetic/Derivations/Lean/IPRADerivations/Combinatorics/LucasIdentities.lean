import IPRADerivations.Combinatorics.FibonacciGcd
import IPRADerivations.Core.Powers
import IPRADerivations.DiophantineNumberTheory.Hurwitz
import IPRADerivations.Core.LinearCombination

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
* `fibS_le_pow`, `fib_le_pow`, `luc_le_pow`: `F_{k+1} ≤ 2^k`, `F_k ≤ 2^k`, `L_k ≤ 2^{k+1}`;
* `fib_triple`, `luc_triple` (22): `F_{3k} = F_k (L_k² − (−1)^k)`, `L_{3k} = L_k³ − 3(−1)^k L_k`;
* `luc_fib_mixed` (24): `L_{k+d} F_{k+1} − L_{k+d+1} F_k = (−1)^k L_d`;
* `alt_sum` (14): `∑_{j≤N} (−1)^j F_{j+1} = 1 + (−1)^N F_N`, with the even and odd parts separated;
* `fib_parity`, `fib_parity_one`, `fib_parity_two` (17): `F_{3k}` is even, `F_{3k+1}` and
  `F_{3k+2}` are odd.

The recurrences (26) along an arithmetic progression are `fib_luc_mul` and `luc_mul` at `d = j·k`.

The algebraic identities are ring consequences of the addition laws, Cassini's and d'Ocagne's
identities; the sums, the bound and the parity pattern are inductions.
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
  ipra_lc natEq (luc_eq (Γ := Γ) (zero : PTm n)) - natEq (fib_zero (Γ := Γ)) + 2 * natEq (fibS_zero (Γ := Γ))

theorem luc_one : Γ ⊢[PRAAx] luc (succ (zero : PTm n)) ≐ one := by
  ipra_lc natEq (luc_succ (Γ := Γ) (zero : PTm n)) + natEq (fibS_succ (Γ := Γ) (zero : PTm n)) +
    natEq (fibS_zero (Γ := Γ)) + 2 * natEq (fib_zero (Γ := Γ))

/-- `L_{k+2} + L_k = 5 F_{k+1}`. -/
theorem luc_five (k : PTm n) : Γ ⊢[PRAAx] luc (succ (succ k)) + luc k ≐ (two * two + one) * fibS k := by
  ipra_lc natEq (luc_eq (Γ := Γ) (succ (succ k))) + natEq (luc_eq (Γ := Γ) k) - natEq (fib_succ (Γ := Γ) (succ k)) +
    2 * natEq (fibS_succ (Γ := Γ) (succ k)) + natEq (fibS_succ (Γ := Γ) k) + 2 * natEq (fib_succ (Γ := Γ) k)

/-! ## Determinants and doubling -/

/-- `L_k F_{k+1} + 2[k odd] = L_{k+1} F_k + 2[k even]`, i.e. `L_k F_{k+1} − L_{k+1} F_k = 2(−1)^k`. -/
theorem luc_fib_det (k : PTm n) :
    Γ ⊢[PRAAx] luc k * fibS k + two * par k ≐ luc (succ k) * fib k + two * monus one (par k) := by
  ipra_lc 𝔞(fibS k) * natEq (luc_eq (Γ := Γ) k) - 𝔞(fib k) * natEq (luc_succ (Γ := Γ) k) +
    𝔞(fib k) * natEq (fibS_succ (Γ := Γ) k) - 2 * natEq (cassini (Γ := Γ) k)

/-- `L_{2k} + 2[k even] = L_k² + 2[k odd]`, i.e. `L_{2k} = L_k² − 2(−1)^k`. -/
theorem luc_double (k : PTm n) :
    Γ ⊢[PRAAx] luc (k + k) + two * monus one (par k) ≐ luc k * luc k + two * par k := by
  ipra_lc natEq (luc_eq (Γ := Γ) (k + k)) - natEq (fib_double (Γ := Γ) k) + 2 * natEq (fibS_double (Γ := Γ) k) -
    (𝔞(fibS k) + 𝔞(monus (fibS k) (fib k)) + 2 * 𝔞(fibS k) - 𝔞(fib k)) * natEq (luc_eq (Γ := Γ) k) -
    2 * 𝔞(fib k) * natEq (fibS_succ (Γ := Γ) k) + 2 * natEq (cassini (Γ := Γ) k)

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
  ipra_lc 𝔞(fib (k + d)) * natEq (luc_eq (Γ := Γ) k) + natEq (docagne (Γ := Γ) k d) -
    natEq (fib_add_sym (Γ := Γ) (k + d) k)

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
  ipra_lc natEq e + natEq (sum_zero (Γ := Γ) lsqB (zero : PTm n)) +
    (𝔞(fibS zero) + 𝔞(monus (fibS zero) (fib zero)) + 1) * natEq (luc_zero (Γ := Γ)) -
    (𝔞(fibS zero) + 𝔞(monus (fibS zero) (fib zero))) * natEq (luc_one (Γ := Γ))

theorem sum_lsq_step {N : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ N) zero ≐ luc N * luc (succ N) + two) :
    Γ ⊢[PRAAx] ap2 (sumF lsqB) (succ (succ N)) zero ≐ luc (succ N) * luc (succ (succ N)) + two := by
  have e := sum_succ' (Γ := Γ) lsqB (succ N) zero
  rw [inst2_lsq] at e
  ipra_lc natEq e + natEq ih -
    (𝔞(fibS (succ N)) + 𝔞(monus (fibS (succ N)) (fib (succ N)))) * natEq (luc_rec (Γ := Γ) N)

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
    ((pw_succ two k).eqTrans (by ipra_ring)).eqSymm
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
    ((pw_succ two k).eqTrans (by ipra_ring)).eqSymm
  have d : Γ ⊢[PRAAx] fibS k + fibS k ≐ two * fibS k := by ipra_ring
  exact le_trans (le_of_eq_add (luc_eq k).eqSymm)
    (le_congr d e (add_le_add (fibS_le_pow k) (fibS_le_pow k)))

/-! ## Triple arguments and the mixed determinant -/

/-- `F_{3k} + [k even] F_k = F_k L_k² + [k odd] F_k`, i.e. `F_{3k} = F_k (L_k² − (−1)^k)`. -/
theorem fib_triple (k : PTm n) :
    Γ ⊢[PRAAx] fib ((k + k) + k) + monus one (par k) * fib k ≐ fib k * (luc k * luc k) + par k * fib k := by
  ipra_lc -natEq (fib_luc_mul (Γ := Γ) k k) +
    (𝔞(fibS k) + 𝔞(monus (fibS k) (fib k))) * natEq (fib_double_luc (Γ := Γ) k)

/-- `L_{3k} + 3[k even] L_k = L_k³ + 3[k odd] L_k`, i.e. `L_{3k} = L_k³ − 3(−1)^k L_k`. -/
theorem luc_triple (k : PTm n) :
    Γ ⊢[PRAAx] luc ((k + k) + k) + (two + one) * (monus one (par k) * luc k) ≐
      luc k * luc k * luc k + (two + one) * (par k * luc k) := by
  ipra_lc -natEq (luc_mul (Γ := Γ) k k) + (𝔞(fibS k) + 𝔞(monus (fibS k) (fib k))) * natEq (luc_double (Γ := Γ) k)

/-- `L_{k+d} F_{k+1} + [k odd] L_d = L_{k+d+1} F_k + [k even] L_d`, i.e.
`L_m F_{k+1} − L_{m+1} F_k = (−1)^k L_{m−k}` for `m = k + d`. -/
theorem luc_fib_mixed (k d : PTm n) :
    Γ ⊢[PRAAx] luc (k + d) * fibS k + par k * luc d ≐
      luc (succ (k + d)) * fib k + monus one (par k) * luc d := by
  have lm := natEq (luc_eq (Γ := Γ) (k + d)); have lms := natEq (luc_succ (Γ := Γ) (k + d))
  have sm := natEq (fibS_succ (Γ := Γ) (k + d)); have ld := natEq (luc_eq (Γ := Γ) d)
  have doc := natEq (docagne (Γ := Γ) k d); have doc' := natEq (docagne_succ (Γ := Γ) k d)
  apply deriveNat; ipra_simps
  linear_combination 𝔞(fibS k) * lm - 𝔞(fib k) * lms + (𝔞(par k) - 𝔞(monus one (par k))) * ld - doc +
    2 * doc' + 𝔞(fib k) * sm

/-! ## The alternating sum -/

/-- `[j even] F_{j+1}`. -/
abbrev evfB : PTm 2 := monus one (par (var 0)) * fibS (var 0)
/-- `[j odd] F_{j+1}`. -/
abbrev odfB : PTm 2 := par (var 0) * fibS (var 0)

theorem inst2_evf (k x : PTm n) : inst2 evfB k x = monus one (par k) * fibS k := by simp [inst2]
theorem inst2_odf (k x : PTm n) : inst2 odfB k x = par k * fibS k := by simp [inst2]

theorem alt_base :
    Γ ⊢[PRAAx] ap2 (sumF evfB) (succ zero) (zero : PTm n) + par zero * fib zero ≐
      ap2 (sumF odfB) (succ zero) zero + one + monus one (par zero) * fib zero := by
  have e₁ := sum_succ' (Γ := Γ) evfB (zero : PTm n) zero
  rw [inst2_evf] at e₁
  have e₂ := sum_succ' (Γ := Γ) odfB (zero : PTm n) zero
  rw [inst2_odf] at e₂
  ipra_lc natEq e₁ + natEq (sum_zero (Γ := Γ) evfB (zero : PTm n)) - natEq e₂ -
    natEq (sum_zero (Γ := Γ) odfB (zero : PTm n)) + 𝔞(monus one (par zero)) * natEq (fibS_zero (Γ := Γ)) +
    natEq ((congrMonus (.eqRefl one) (par_zero (Γ := Γ))).eqTrans (monus_zero _)) +
    𝔞(par zero) * natEq (fib_zero (Γ := Γ)) - 𝔞(fibS zero) * natEq (par_zero (Γ := Γ)) -
    𝔞(monus one (par zero)) * natEq (fib_zero (Γ := Γ))

theorem alt_step {N : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF evfB) (succ N) zero + par N * fib N ≐
      ap2 (sumF odfB) (succ N) zero + one + monus one (par N) * fib N) :
    Γ ⊢[PRAAx] ap2 (sumF evfB) (succ (succ N)) zero + par (succ N) * fib (succ N) ≐
      ap2 (sumF odfB) (succ (succ N)) zero + one + monus one (par (succ N)) * fib (succ N) := by
  have e₁ := sum_succ' (Γ := Γ) evfB (succ N) zero
  rw [inst2_evf] at e₁
  have e₂ := sum_succ' (Γ := Γ) odfB (succ N) zero
  rw [inst2_odf] at e₂
  ipra_lc natEq e₁ - natEq e₂ + natEq ih +
    (𝔞(monus one (par (succ N))) - 𝔞(par (succ N))) * (natEq (fibS_succ (Γ := Γ) N) - natEq (fib_succ (Γ := Γ) N)) +
    𝔞(fib N) * (natEq ((congrMonus (.eqRefl one) (par_succ (Γ := Γ) N)).eqTrans (compl_compl N)) - natEq (par_succ (Γ := Γ) N))

private abbrev altF : Fm PTm 1 :=
  ap2 (sumF evfB) (succ (var 0)) zero + par (var 0) * fib (var 0) ≐
    ap2 (sumF odfB) (succ (var 0)) zero + one + monus one (par (var 0)) * fib (var 0)

private theorem alt₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] altF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_ap1, subst_fibS,
      subst_fib, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact alt_base
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_ap2, subst_ap1, subst_fibS,
      subst_fib, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact alt_step Prf.hyp0

/-- `∑_{j≤N} (−1)^j F_{j+1} = 1 + (−1)^N F_N`, with the even and odd parts separated:
`∑_{j≤N} [j even] F_{j+1} + [N odd] F_N = ∑_{j≤N} [j odd] F_{j+1} + 1 + [N even] F_N`. -/
theorem alt_sum (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF evfB) (succ N) zero + par N * fib N ≐
      ap2 (sumF odfB) (succ N) zero + one + monus one (par N) * fib N := by
  have h := inst (Γ := Γ) alt₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## The parity pattern -/

theorem even_of_par {x : PTm n} (h : Γ ⊢[PRAAx] par x ≐ zero) : Γ ⊢[PRAAx] x ≐ two * half x :=
  (half_par x).eqTrans ((congrAdd (.eqRefl _) h).eqTrans (add_zero _))

theorem odd_of_par {x : PTm n} (h : Γ ⊢[PRAAx] par x ≐ one) : Γ ⊢[PRAAx] x ≐ two * half x + one :=
  (half_par x).eqTrans (congrAdd (.eqRefl _) h)

theorem par_step {T T' : PTm n} (eT : Γ ⊢[PRAAx] T' ≐ succ (succ (succ T)))
    (h₀ : Γ ⊢[PRAAx] par (fib T) ≐ zero) (h₁ : Γ ⊢[PRAAx] par (fibS T) ≐ one) :
    Γ ⊢[PRAAx] (par (fib T') ≐ zero) ⋏ (par (fibS T') ≐ one) := by
  have a := natEq (even_of_par h₀); have b := natEq (odd_of_par h₁)
  have c₀ := natEq (congrFib eT); have d₀ := natEq (congrFibS eT)
  have c₁ := natEq (fib_succ (Γ := Γ) (succ (succ T))); have d₁ := natEq (fibS_succ (Γ := Γ) (succ (succ T)))
  have c₂ := natEq (fibS_succ (Γ := Γ) (succ T)); have d₂ := natEq (fib_succ (Γ := Γ) (succ T))
  have c₃ := natEq (fibS_succ (Γ := Γ) T); have c₄ := natEq (fib_succ (Γ := Γ) T)
  have e : Γ ⊢[PRAAx] fib T' ≐ two * (half (fibS T) + half (fibS T) + one + half (fib T)) := by
    ipra_lc c₀ + c₁ + c₂ + c₃ + c₄ + 2 * b + a
  have e' : Γ ⊢[PRAAx] fibS T' ≐
      two * (half (fibS T) + half (fibS T) + half (fibS T) + half (fib T) + half (fib T) + one) + one := by
    ipra_lc d₀ + d₁ + d₂ + c₂ + 2 * c₃ + c₄ + 3 * b + 2 * a
  exact .andI ((congrAp1 parF e).eqTrans (par_double _)) ((congrAp1 parF e').eqTrans (par_double_succ _))

private abbrev parF3 : Fm PTm 1 :=
  (par (fib (var 0 + var 0 + var 0)) ≐ zero) ⋏ (par (fibS (var 0 + var 0 + var 0)) ≐ one)

private theorem par₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] parF3 := by
  refine ind _ ⟨trivial, trivial⟩ ?_ ?_
  · simp only [Fm.subst_and, Fm.subst_eq, PTm.subst_add, subst_ap1, subst_fibS, subst_fib, Syn.subst_var,
      Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have z : ([] : List (Fm PTm 0)) ⊢[PRAAx] (zero : PTm 0) + zero + zero ≐ zero := by
      ipra_ring
    exact .andI ((congrAp1 parF ((congrFib z).eqTrans fib_zero)).eqTrans par_zero)
      ((congrAp1 parF ((congrFibS z).eqTrans fibS_zero)).eqTrans
        ((par_succ zero).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _))))
  · simp only [Fm.subst_and, Fm.subst_eq, PTm.subst_add, subst_ap1, subst_fibS, subst_fib, Syn.subst_var,
      Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine par_step ?_ (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)
    ipra_ring

/-- `F_{3k}` is even and `F_{3k+1}` is odd. -/
theorem fib_parity (k : PTm n) :
    Γ ⊢[PRAAx] (par (fib (k + k + k)) ≐ zero) ⋏ (par (fibS (k + k + k)) ≐ one) := by
  have h := inst (Γ := Γ) par₀ (![k] : Fin 1 → PTm n)
  simpa using h

/-- `F_{3k+1}` is odd. -/
theorem fib_parity_one (k : PTm n) : Γ ⊢[PRAAx] par (fib (succ (k + k + k))) ≐ one :=
  (congrAp1 parF (fib_succ _)).eqTrans (Prf.andE₂ (fib_parity k))

/-- `F_{3k+2}` is odd. -/
theorem fib_parity_two (k : PTm n) : Γ ⊢[PRAAx] par (fib (succ (succ (k + k + k)))) ≐ one := by
  have p := fib_parity (Γ := Γ) k
  have a := natEq (even_of_par (Prf.andE₁ p)); have b := natEq (odd_of_par (Prf.andE₂ p))
  have c₁ := natEq (fib_succ (Γ := Γ) (succ (k + k + k))); have c₃ := natEq (fibS_succ (Γ := Γ) (k + k + k))
  have e : Γ ⊢[PRAAx] fib (succ (succ (k + k + k))) ≐
      two * (half (fibS (k + k + k)) + half (fib (k + k + k))) + one := by
    ipra_lc c₁ + c₃ + b + a
  exact (congrAp1 parF e).eqTrans (par_double_succ _)

end LeanProofs.IPRA.Combinatorics.LucasIdentities
