import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The Apéry numbers: first values and growth

Packet: `diophantine-number-theory/apery_ipra` (`lem:integrality`, initial values, and
`lem:growth`). The Apéry numbers are

  `a_n = ∑_{k≤n} C(n, k)² C(n + k, k)²`.

* `cb_double`, `cb_ge_pow`: `2 C(2n, n) ≤ C(2n + 2, n + 1)` and `2^n ≤ C(2n, n)`, from the
  recurrence `(n + 1) C(2n + 2, n + 1) = 2 (2n + 1) C(2n, n)`;
* `apery_zero`, `apery_one` (`lem:integrality`): `a_0 = 1`, `a_1 = 5`;
* `apery_ge_cb`: `C(2n, n)² ≤ a_n` (the term `k = n`);
* `apery_lower` (`lem:growth`): `4^n ≤ a_n`;
* `four_pow_ge`: `n + 1 ≤ 4^n`, and `apery_ge_succ`: `n + 1 ≤ a_n`;
* `apery_pos`: `a_n > 0`.

The Apéry recurrence is derived in `DiophantineNumberTheory/AperyRecurrence`. The second sequence
`b_n` and the irrationality argument are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyNumbers

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_zero' binom_self')
open LeanProofs.IPRA.Combinatorics.Catalan (cb cb_zero cb_rec)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The central binomial coefficient grows -/

theorem congrBinom {a a' k : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] binom a k ≐ binom a' k :=
  congrAp2 quoF (congrAp2 factF h (.eqRefl _))
    (congrMul (.eqRefl _) (congrAp2 factF (congrMonus h (.eqRefl _)) (.eqRefl _)))

/-- `2 C(2m, m) ≤ C(2m + 2, m + 1)`. -/
theorem cb_double (m : PTm n) : Γ ⊢[PRAAx] le (two * cb m) (cb (succ m)) := by
  refine mul_le_cancel (d' := m) (le_congr (.eqRefl _) (cb_rec m).eqSymm
    (le_of_eq_add (d := (two * m) * cb m) ?_))
  ipra_ring

theorem cb_pow_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (pw two m) (cb m)) :
    Γ ⊢[PRAAx] le (pw two (succ m)) (cb (succ m)) :=
  le_trans (le_congr ((mul_comm _ _).eqTrans (pw_succ two m).eqSymm) (.eqRefl _) (le_mul_mono (le_refl two) ih))
    (cb_double m)

/-- Variables: `0 = m`. -/
private abbrev cbPowF : Fm PTm 1 := le (pw two (var 0)) (cb (var 0))

private theorem cbPow₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] cbPowF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (pw_zero two).eqSymm cb_zero.eqSymm (le_refl one)
  · exact cb_pow_step Prf.hyp0

/-- `2^m ≤ C(2m, m)`. -/
theorem cb_ge_pow (m : PTm n) : Γ ⊢[PRAAx] le (pw two m) (cb m) := by
  have h := inst (Γ := Γ) cbPow₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-! ## The Apéry numbers -/

/-- `C(m, k)² C(m + k, k)²`, with `m` the parameter. -/
abbrev apB : PTm 2 :=
  (binom (var 1) (var 0) * binom (var 1) (var 0)) * (binom (var 1 + var 0) (var 0) * binom (var 1 + var 0) (var 0))

theorem inst2_ap (k m : PTm n) :
    inst2 apB k m = (binom m k * binom m k) * (binom (m + k) k * binom (m + k) k) := by
  simp [inst2]

/-- `a_m = ∑_{k≤m} C(m, k)² C(m + k, k)²`. -/
abbrev apery (m : PTm n) : PTm n := ap2 (sumF apB) (succ m) m

/-- The last term: `C(m, m)² C(2m, m)² = C(2m, m)²`. -/
theorem last_term (m : PTm n) : Γ ⊢[PRAAx] inst2 apB m m ≐ cb m * cb m := by
  rw [inst2_ap]
  have hN : Γ ⊢[PRAAx] m + m ≐ two * m := by ipra_ring
  exact (congrMul (congrMul (binom_self' m) (binom_self' m)) (congrMul (congrBinom hN) (congrBinom hN))).eqTrans
    ((congrMul (one_mul _) (.eqRefl _)).eqTrans (one_mul _))

/-- `C(2m, m)² ≤ a_m`. -/
theorem apery_ge_cb (m : PTm n) : Γ ⊢[PRAAx] le (cb m * cb m) (apery m) :=
  le_congr (last_term m) (.eqRefl _) (term_le_sum apB (le_refl (succ m)))

/-- `lem:growth`: `4^m ≤ a_m`. -/
theorem apery_lower (m : PTm n) : Γ ⊢[PRAAx] le (pw (two * two) m) (apery m) :=
  le_trans (le_congr (pw_mul_base two two m).eqSymm (.eqRefl _) (le_mul_mono (cb_ge_pow m) (cb_ge_pow m)))
    (apery_ge_cb m)

/-! ## `m + 1 ≤ 4^m` -/

theorem four_step {m : PTm n} (ih : Γ ⊢[PRAAx] le (succ m) (pw (two * two) m)) :
    Γ ⊢[PRAAx] le (succ (succ m)) (pw (two * two) (succ m)) := by
  refine le_trans (le_of_eq_add (d := (two + one) * m + two) ?_)
    (le_congr (.eqRefl _) (pw_succ _ _).eqSymm (le_mul_mono ih (le_refl (two * two))))
  ipra_ring

/-- Variables: `0 = m`. -/
private abbrev fourF : Fm PTm 1 := le (succ (var 0)) (pw (two * two) (var 0))

private theorem four₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] fourF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (.eqRefl _) (pw_zero _).eqSymm (le_refl one)
  · exact four_step Prf.hyp0

/-- `m + 1 ≤ 4^m`. -/
theorem four_pow_ge (m : PTm n) : Γ ⊢[PRAAx] le (succ m) (pw (two * two) m) := by
  have h := inst (Γ := Γ) four₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- `lem:growth`: `m + 1 ≤ a_m`. -/
theorem apery_ge_succ (m : PTm n) : Γ ⊢[PRAAx] le (succ m) (apery m) :=
  le_trans (four_pow_ge m) (apery_lower m)

/-- `a_m > 0`. -/
theorem apery_pos (m : PTm n) : Γ ⊢[PRAAx] apery m ≐ succ (pred (apery m)) :=
  pos_of_eq_succ (c := m + monus (apery m) (succ m))
    ((eq_add_of_le (apery_ge_succ m)).eqTrans (succ_add _ _))

/-! ## The first values -/

/-- `a_0 = 1`. -/
private theorem apery_first_term (N : PTm n) : Γ ⊢[PRAAx] inst2 apB zero N ≐ one := by
  rw [inst2_ap]
  exact (congrMul (congrMul (binom_zero' _) (binom_zero' _)) (congrMul (binom_zero' _) (binom_zero' _))).eqTrans
    ((congrMul (one_mul _) (one_mul _)).eqTrans (one_mul _))

theorem apery_zero : Γ ⊢[PRAAx] apery (zero : PTm n) ≐ one :=
  (sum_singleton apB zero).eqTrans (apery_first_term zero)

theorem cb_one : Γ ⊢[PRAAx] cb (one : PTm n) ≐ two := by
  ipra_lc natEq (cb_rec (Γ := Γ) (zero : PTm n)) + 2 * natEq (cb_zero (Γ := Γ))

/-- `a_1 = 5`. -/
theorem apery_one : Γ ⊢[PRAAx] apery (one : PTm n) ≐ two * two + one := by
  have t₁ : Γ ⊢[PRAAx] inst2 apB (one : PTm n) one ≐ two * two := (last_term one).eqTrans (congrMul cb_one cb_one)
  exact (sum_two_terms apB one).eqTrans
    ((congrAdd (apery_first_term one) t₁).eqTrans (add_comm _ _))

end LeanProofs.IPRA.DiophantineNumberTheory.AperyNumbers
