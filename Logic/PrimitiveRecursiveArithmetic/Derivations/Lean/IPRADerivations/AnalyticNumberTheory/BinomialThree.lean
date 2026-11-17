import IPRADerivations.Combinatorics.BinomialTwo
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Probability.SortingBound
import IPRADerivations.Geometry.HypercubeSplit

/-!
# The binomial bound `(1 + 1/a)^a ≤ 3`

Packet: `prime_reciprocal_ipra_2026-11-15`, Lemma `lem:binomial-three`, cleared of denominators:
`(a + 1)^a ≤ 3 a^a`. The proof is the packet's: expand by the binomial theorem
(`Combinatorics/BinomialTwo`), bound `C(a, k)/a^k ≤ 1/k! ≤ 1/2^{k−1}`, and sum the geometric
series.

* `two_pow_le_fact`: `2^j ≤ (j + 1)!`;
* `fact_le_falling`: `(m + k)! ≤ m! (m + k)^k`;
* `binom_fact_le`: `k! C(a, k) ≤ a^k` for `k ≤ a`;
* `term_bound`: `2^j · C(a, j + 1) a^{a−j−1} ≤ a^a` (also when `j + 1 > a`, where the term is `0`);
* `geom_dom`: `2^K ∑_{j<K} t_{j+1} + 2 a^a ≤ 2 a^a 2^K` for the binomial terms `t_k`;
* `binomial_three` (`lem:binomial-three`): `(a + 1)^a ≤ 3 a^a`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb gb_above)
open LeanProofs.IPRA.Combinatorics.Stirling (gle_of_le)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (bt bt_at S binomial_two)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (lt_pw)
open LeanProofs.IPRA.Probability.SortingBound (fct fact_pos le_one_succ)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem pos_of_one_le {x : PTm n} (h : Γ ⊢[PRAAx] le one x) : Γ ⊢[PRAAx] x ≐ succ (pred x) := by
  have e := natEq (eq_add_of_le h)
  exact pos_of_eq_succ (c := monus x one) (by apply deriveNat; ipra_simps; linear_combination e)

/-! ## Factorial bounds -/

/-- Variable: `0 = j`. -/
private abbrev tfF : Fm PTm 1 := le (pw two (var 0)) (ap2 factF (succ (var 0)) zero)

private theorem tf₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] tfF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine le_congr (pw_zero _).eqSymm ?_ (le_refl one)
    exact ((fact_succ _ _).eqTrans ((congrMul (fact_zero _) (.eqRefl _)).eqTrans (by ipra_ring))).eqSymm
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    refine le_congr (pw_succ _ _).eqSymm (fact_succ _ _).eqSymm (le_mul_mono Prf.hyp0 ?_)
    exact le_of_eq_add (d := var 0) (by ipra_ring)

/-- `2^j ≤ (j + 1)!`. -/
theorem two_pow_le_fact (j : PTm n) : Γ ⊢[PRAAx] le (pw two j) (fct (succ j)) := by
  have h := inst (Γ := Γ) tf₀ (![j] : Fin 1 → PTm n)
  simpa using h

theorem fl_step {m k : PTm n} (ih : Γ ⊢[PRAAx] le (ap2 factF (m + k) zero) (ap2 factF m zero * pw (m + k) k)) :
    Γ ⊢[PRAAx] le (ap2 factF (m + succ k) zero) (ap2 factF m zero * pw (m + succ k) (succ k)) := by
  have hle : Γ ⊢[PRAAx] le (pw (m + k) k) (pw (m + succ k) k) :=
    pw_le_pw _ (le_of_eq_add (d := one) (by apply deriveNat; ipra_simps; ring))
  refine le_congr ((congrAp2 factF (add_succ _ _) (.eqRefl _)).eqTrans (fact_succ _ _)).eqSymm ?_
    (le_mul_mono (le_trans ih (le_mul_mono (le_refl _) hle)) (le_refl (succ (m + k))))
  have p := natEq (pw_succ (Γ := Γ) (m + succ k) k)
  apply deriveNat; ipra_simps; linear_combination -𝔞 (ap2 factF m zero) * p

/-- Variables: `0 = k`, `1 = m`. -/
private abbrev flF : Fm PTm 2 :=
  le (ap2 factF (var 1 + var 0) zero) (ap2 factF (var 1) zero * pw (var 1 + var 0) (var 0))

private theorem fl₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] flF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_congr (congrAp2 factF (add_zero _).eqSymm (.eqRefl _))
      ((congrMul (.eqRefl _) (pw_zero _)).eqTrans ((mul_comm _ _).eqTrans (one_mul _))).eqSymm (le_refl _)
  · simp only [subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact fl_step Prf.hyp0

/-- `(m + k)! ≤ m! (m + k)^k`. -/
theorem fact_le_falling (m k : PTm n) : Γ ⊢[PRAAx] le (fct (m + k)) (fct m * pw (m + k) k) := by
  have h := inst (Γ := Γ) fl₀ (![k, m] : Fin 2 → PTm n)
  simpa using h

/-- `k! C(a, k) ≤ a^k` for `k ≤ a`. -/
theorem binom_fact_le {k a : PTm n} (h : Γ ⊢[PRAAx] le k a) : Γ ⊢[PRAAx] le (fct k * binom a k) (pw a k) := by
  have be := binom_eq h
  have ea := eq_add_of_le h
  have fl := fact_le_falling (Γ := Γ) (monus a k) k
  have ex : Γ ⊢[PRAAx] monus a k + k ≐ a := (add_comm _ _).eqTrans ea.eqSymm
  have hc := pos_of_one_le (fact_pos (Γ := Γ) (monus a k))
  refine le_cancel_pos hc (le_congr ?_ ?_ fl)
  · refine (congrAp2 factF ex (.eqRefl _)).eqTrans (be.eqTrans ?_)
    apply deriveNat; ipra_simps; ring
  · exact congrMul (.eqRefl _) (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw ex (.eqRefl _))

/-! ## The terms -/

theorem term_in {j a : PTm n} (h : Γ ⊢[PRAAx] le (succ j) a) :
    Γ ⊢[PRAAx] le (pw two j * inst2 bt (succ j) (pairT a (pairT one a))) (pw a a) := by
  have ev := (bt_at (Γ := Γ) (succ j) a one a).eqTrans
    (congrMul (congrMul (gle_of_le h |> fun g => (congrMul g (.eqRefl _)).eqTrans (one_mul _)) (pw_one_base _))
      (.eqRefl _))
  have ea := eq_add_of_le h
  have pa := pw_add (Γ := Γ) a (succ j) (monus a (succ j))
  have c₁ := le_mul_mono (two_pow_le_fact (Γ := Γ) j) (le_refl (binom a (succ j) * pw a (monus a (succ j))))
  have c₂ := le_mul_mono (binom_fact_le h) (le_refl (pw a (monus a (succ j))))
  refine le_congr ?_ ?_ (le_trans c₁ (le_congr (by apply deriveNat; ipra_simps; ring) (.eqRefl _) c₂))
  · have e := natEq ev
    apply deriveNat; ipra_simps; linear_combination -𝔞 (pw two j) * e
  · exact pa.eqSymm.eqTrans (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (.eqRefl _) ea.eqSymm)

theorem term_out {j a : PTm n} (h : Γ ⊢[PRAAx] lt a (succ j)) :
    Γ ⊢[PRAAx] le (pw two j * inst2 bt (succ j) (pairT a (pairT one a))) (pw a a) := by
  have z : Γ ⊢[PRAAx] inst2 bt (succ j) (pairT a (pairT one a)) ≐ zero :=
    (bt_at _ _ _ _).eqTrans ((congrMul (congrMul (gb_above h) (.eqRefl _)) (.eqRefl _)).eqTrans
      (by apply deriveNat; ipra_simps; ring))
  exact le_congr ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)

/-- `2^j · C(a, j + 1) a^{a−j−1} ≤ a^a`. -/
theorem term_bound (j a : PTm n) :
    Γ ⊢[PRAAx] le (pw two j * inst2 bt (succ j) (pairT a (pairT one a))) (pw a a) :=
  .orE (lt_or_le a (succ j)) (term_out Prf.hyp0) (term_in Prf.hyp0)

/-! ## Geometric domination -/

theorem geom_step {K a : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw two K * ap2 (sumF (shiftBody bt)) K (pairT a (pairT one a)) + two * pw a a)
      (two * pw a a * pw two K)) :
    Γ ⊢[PRAAx] le (pw two (succ K) * ap2 (sumF (shiftBody bt)) (succ K) (pairT a (pairT one a)) + two * pw a a)
      (two * pw a a * pw two (succ K)) := by
  have s := sum_succ' (Γ := Γ) (shiftBody bt) K (pairT a (pairT one a))
  rw [inst2_shiftBody] at s
  have s' := natEq s
  have p := natEq (pw_succ (Γ := Γ) two K)
  have t := natEq (eq_add_of_le (term_bound (Γ := Γ) K a))
  have i := natEq (eq_add_of_le ih)
  refine le_of_eq_add (d := two * monus (two * pw a a * pw two K)
      (pw two K * ap2 (sumF (shiftBody bt)) K (pairT a (pairT one a)) + two * pw a a) +
    two * monus (pw a a) (pw two K * inst2 bt (succ K) (pairT a (pairT one a)))) ?_
  apply deriveNat; ipra_simps
  linear_combination (2 * 𝔞 (pw a a) - 𝔞 (ap2 (sumF (shiftBody bt)) (succ K) (pairT a (pairT one a)))) * p -
    2 * 𝔞 (pw two K) * s' + 2 * i + 2 * t

/-- Variables: `0 = K`, `1 = a`. -/
private abbrev geomF : Fm PTm 2 :=
  le (pw two (var 0) * ap2 (sumF (shiftBody bt)) (var 0) (pairT (var 1) (pairT one (var 1))) +
      two * pw (var 1) (var 1))
    (two * pw (var 1) (var 1) * pw two (var 0))

private theorem geom₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] geomF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have z := natEq (sum_zero (Γ := ([] : List (Fm PTm 1))) (shiftBody bt) (pairT (var 0) (pairT one (var 0))))
    have p := natEq (pw_zero (Γ := ([] : List (Fm PTm 1))) two)
    refine le_of_eq_add (d := zero) ?_
    apply deriveNat; ipra_simps
    linear_combination 2 * 𝔞 (pw (var 0) (var 0) : PTm 1) * p - 𝔞 (pw two zero : PTm 1) * z
  · simp only [subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact geom_step Prf.hyp0

/-- `2^K ∑_{j<K} t_{j+1} + 2 a^a ≤ 2 a^a 2^K`. -/
theorem geom_dom (K a : PTm n) :
    Γ ⊢[PRAAx] le (pw two K * ap2 (sumF (shiftBody bt)) K (pairT a (pairT one a)) + two * pw a a)
      (two * pw a a * pw two K) := by
  have h := inst (Γ := Γ) geom₀ (![K, a] : Fin 2 → PTm n)
  simpa using h

/-- `lem:binomial-three`: `(a + 1)^a ≤ 3 a^a`, i.e. `(1 + 1/a)^a ≤ 3`. -/
theorem binomial_three (a : PTm n) : Γ ⊢[PRAAx] le (pw (succ a) a) (num 3 * pw a a) := by
  have bin := binomial_two (Γ := Γ) a one a
  have sh := sum_shift (Γ := Γ) bt a (pairT a (pairT one a))
  have t0 := (bt_at (Γ := Γ) zero a one a).eqTrans
    (congrMul (congrMul (LeanProofs.IPRA.Combinatorics.Vandermonde.gb_zero a) (pw_zero _))
      (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (.eqRefl a) (monus_zero a)))
  have g := geom_dom (Γ := Γ) a a
  have hp := pos_of_one_le (le_trans (le_one_succ a) (lt_pw (Γ := Γ) (le_refl two) a))
  have sb : Γ ⊢[PRAAx] le (ap2 (sumF (shiftBody bt)) a (pairT a (pairT one a))) (two * pw a a) := by
    refine le_cancel_pos hp (le_trans (le_of_eq_add (d := two * pw a a) (.eqRefl _)) (le_congr (.eqRefl _) ?_ g))
    apply deriveNat; ipra_simps; ring
  have e₁ := natEq bin; have e₂ := natEq sh; have e₃ := natEq t0
  have e₄ := natEq (eq_add_of_le sb)
  refine le_of_eq_add (d := monus (two * pw a a) (ap2 (sumF (shiftBody bt)) a (pairT a (pairT one a)))) ?_
  have ec := natEq (LeanProofs.IPRA.Combinatorics.BinomialTheorem.congrPw (Γ := Γ)
    (show Γ ⊢[PRAAx] one + a ≐ succ a by ipra_ring) (.eqRefl a))
  apply deriveNat; ipra_simps
  linear_combination ec + e₁ - e₂ - e₃ + e₄

end LeanProofs.IPRA.AnalyticNumberTheory.BinomialThree
