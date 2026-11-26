import IPRADerivations.Analysis.RationalArithmetic.Powers.Pochhammer

/-!
# The Beta function at positive integers

Packet: `analysis/beta_function_ipra_2026-11-16` (Section 4: `thm:pascal`, `lem:balanced-ibp`,
`cor:coordinate-recurrence`, `thm:integer-values`, `cor:binomial-beta`), at positive integer
arguments. Since `B(m + 1, n + 1) = m! n! / (m + n + 1)!` is the reciprocal of an integer, the
statements are about the reciprocal

  `R(m, n) = 1 / B(m + 1, n + 1) = (m + n + 1) C(m + n, m)`.

* `rbeta_fact` (`thm:integer-values`): `R(m, n) m! n! = (m + n + 1)!`;
* `rbeta_symm`: `R(m, n) = R(n, m)`;
* `rbeta_step_left`, `rbeta_step_right` (`cor:coordinate-recurrence`):
  `(m + 1) R(m + 1, n) = (m + n + 2) R(m, n)`, i.e. `B(a + 1, b) = a/(a + b) · B(a, b)`, and the
  same in the second argument;
* `rbeta_balanced` (`lem:balanced-ibp`): `(m + 1) R(m + 1, n) = (n + 1) R(m, n + 1)`, i.e.
  `a B(a, b + 1) = b B(a + 1, b)`;
* `rbeta_pascal` (`thm:pascal`): `R(m + 1, n) R(m, n + 1) = R(m, n) (R(m + 1, n) + R(m, n + 1))`,
  i.e. `B(a, b) = B(a + 1, b) + B(a, b + 1)`;
* `rbeta_poch` (`thm:integer-values`): `R(m, N) N! = (m + 1)_{N+1}`, i.e.
  `B(a, N + 1) = N! / (a (a + 1) ⋯ (a + N))`;
* `rbeta_general` (`cor:coordinate-recurrence`):
  `(a + 1)_i (b + 1)_j R(a + i, b + j) = (a + b + 2)_{i+j} R(a, b)`, i.e.
  `B(a + i, b + j) = (a)_i (b)_j / (a + b)_{i+j} · B(a, b)`.

`cor:binomial-beta`, `C(n, k) = 1 / ((n + 1) B(n − k + 1, k + 1))`, is the definition of `R`
(`rbeta_binom`). The integrals behind the real-argument statements are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BetaIntegers

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_fact)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `R(m, k) = (m + k + 1) C(m + k, m)`, the reciprocal of `B(m + 1, k + 1)`. -/
def rbeta (m k : PTm n) : PTm n := succ (m + k) * binom (m + k) m

/-- `cor:binomial-beta`: `1 / B(m + 1, k + 1) = (m + k + 1) C(m + k, m)`. -/
theorem rbeta_binom (m k : PTm n) : Γ ⊢[PRAAx] rbeta m k ≐ succ (m + k) * binom (m + k) m := .eqRefl _

alias succ_pos := Common.succ_pos

/-- `R(m, k) m! k! = (m + k + 1)!`, i.e. `B(m + 1, k + 1) = m! k! / (m + k + 1)!`. -/
theorem rbeta_fact (m k : PTm n) : Γ ⊢[PRAAx] rbeta m k * (fact m * fact k) ≐ fact (succ (m + k)) := by
  have g : Γ ⊢[PRAAx] fact (monus (m + k) m) ≐ fact k := congrAp2 factF (add_monus' k m) (.eqRefl _)
  unfold rbeta
  ipra_lc -natEq (fact_succ (Γ := Γ) (m + k) zero) -
    (𝔞(m) + 𝔞(k) + 1) * natEq ((binom_eq (Γ := Γ) (le_add_right m k)).eqTrans (congrMul (congrMul (.eqRefl _) g) (.eqRefl _)))

/-- `B(a, b) = B(b, a)`. -/
theorem rbeta_symm (m k : PTm n) : Γ ⊢[PRAAx] rbeta m k ≐ rbeta k m := by
  refine mul_cancel (D := fact m * fact k) (pos_mul (fact_pos m) (fact_pos k)) ?_
  ipra_lc natEq (rbeta_fact (Γ := Γ) m k) - natEq (rbeta_fact (Γ := Γ) k m) +
    natEq (congrAp2 (Γ := Γ) factF (congrSucc (add_comm m k)) (.eqRefl zero))

/-- `(m + 1) R(m + 1, k) = (m + k + 2) R(m, k)`. -/
theorem rbeta_step_left (m k : PTm n) :
    Γ ⊢[PRAAx] succ m * rbeta (succ m) k ≐ succ (succ (m + k)) * rbeta m k := by
  refine mul_cancel (D := fact m * fact k) (pos_mul (fact_pos m) (fact_pos k)) ?_
  ipra_lc natEq (rbeta_fact (Γ := Γ) (succ m) k) +
    natEq ((congrAp2 (Γ := Γ) factF (congrSucc (succ_add m k)) (.eqRefl zero)).eqTrans (fact_succ (succ (m + k)) zero)) -
    (𝔞(m) + 𝔞(k) + 2) * natEq (rbeta_fact (Γ := Γ) m k) -
    𝔞(fact k) * 𝔞(rbeta (succ m) k) * natEq (fact_succ (Γ := Γ) m zero)

/-- `(k + 1) R(m, k + 1) = (m + k + 2) R(m, k)`. -/
theorem rbeta_step_right (m k : PTm n) :
    Γ ⊢[PRAAx] succ k * rbeta m (succ k) ≐ succ (succ (m + k)) * rbeta m k :=
  (congrMul (.eqRefl _) (rbeta_symm m (succ k))).eqTrans
    ((rbeta_step_left k m).eqTrans (congrMul (congrSucc (congrSucc (add_comm k m))) (rbeta_symm k m)))

/-- `lem:balanced-ibp`: `(m + 1) R(m + 1, k) = (k + 1) R(m, k + 1)`. -/
theorem rbeta_balanced (m k : PTm n) : Γ ⊢[PRAAx] succ m * rbeta (succ m) k ≐ succ k * rbeta m (succ k) :=
  (rbeta_step_left m k).eqTrans (rbeta_step_right m k).eqSymm

/-- `thm:pascal`: `R(m + 1, k) R(m, k + 1) = R(m, k) (R(m + 1, k) + R(m, k + 1))`, i.e.
`B(a, b) = B(a + 1, b) + B(a, b + 1)`. -/
theorem rbeta_pascal (m k : PTm n) :
    Γ ⊢[PRAAx] rbeta (succ m) k * rbeta m (succ k) ≐ rbeta m k * (rbeta (succ m) k + rbeta m (succ k)) := by
  refine mul_cancel (D := succ m * succ k) (pos_mul (succ_pos m) (succ_pos k)) ?_
  ipra_lc (𝔞(k) + 1) * (𝔞(rbeta m (succ k)) - 𝔞(rbeta m k)) * natEq (rbeta_step_left (Γ := Γ) m k) +
    𝔞(rbeta m k) * (𝔞(k) + 1) * natEq (rbeta_step_right (Γ := Γ) m k)

/-- `R(m, N) N! = (m + 1)_{N+1}`, i.e. `B(a, N + 1) = N! / (a (a + 1) ⋯ (a + N))`. -/
theorem rbeta_poch (m N : PTm n) : Γ ⊢[PRAAx] rbeta m N * fact N ≐ poch (succ m) (succ N) := by
  refine mul_cancel (D := fact m) (fact_pos m) ?_
  ipra_lc natEq (rbeta_fact (Γ := Γ) m N) - natEq (poch_fact (Γ := Γ) m (succ N)) -
    natEq (congrAp2 (Γ := Γ) factF (add_succ m N) (.eqRefl zero))

/-- `(a + 1)_i (b + 1)_j R(a + i, b + j) = (a + b + 2)_{i+j} R(a, b)`, i.e.
`B(a + i, b + j) = (a)_i (b)_j / (a + b)_{i+j} · B(a, b)`. -/
theorem rbeta_general (a b i j : PTm n) :
    Γ ⊢[PRAAx] (poch (succ a) i * poch (succ b) j) * rbeta (a + i) (b + j) ≐
      poch (succ (succ (a + b))) (i + j) * rbeta a b := by
  refine mul_cancel (D := fact a * fact b) (pos_mul (fact_pos a) (fact_pos b)) ?_
  have pa := natEq (poch_fact (Γ := Γ) a i); have pb := natEq (poch_fact (Γ := Γ) b j)
  have f₁ := natEq (rbeta_fact (Γ := Γ) (a + i) (b + j)); have f₀ := natEq (rbeta_fact (Γ := Γ) a b)
  have hc : Γ ⊢[PRAAx] succ ((a + i) + (b + j)) ≐ succ (a + b) + (i + j) := by
    ipra_ring
  ipra_lc 𝔞(rbeta (a + i) (b + j)) * 𝔞(fact b) * 𝔞(poch (succ b) j) * pa +
    𝔞(rbeta (a + i) (b + j)) * 𝔞(fact (a + i)) * pb + f₁ - 𝔞(poch (succ (succ (a + b))) (i + j)) * f₀ -
    natEq (poch_fact (Γ := Γ) (succ (a + b)) (i + j)) + natEq (congrAp2 (Γ := Γ) factF hc (.eqRefl zero))

end LeanProofs.IPRA.Analysis.BetaIntegers
