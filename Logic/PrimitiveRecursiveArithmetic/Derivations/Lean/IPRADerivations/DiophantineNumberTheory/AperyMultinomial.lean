import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.DiophantineNumberTheory.SuperellipticFamily
import IPRADerivations.Combinatorics.BinomialTheorem
import IPRADerivations.Core.SumLemmas

/-!
# The multinomial-term bound of the Apéry lcm estimate

Packet: `diophantine-number-theory/apery_ipra`, Lemma `lem:multibound`: "In the expansion of
`(21 + 14 + 6 + 1)^{42m} = 42^{42m}`, the term with respective exponents `21m, 14m, 6m, m` is
`M_m 21^{21m} 14^{14m} 6^{6m}`. All terms are nonnegative, so it is at most the whole sum."

The multinomial coefficient is the product of three binomial coefficients,
`M_m = C(42m, 21m) C(21m, 14m) C(7m, 6m)`, and the term bound follows from three binomial term bounds
(`binom_term`: `C(n, k) x^k ≤ (x + 1)^n`, one term of `BinomialTheorem.binomial_at`):

* `C(42m, 21m) ≤ 2^{42m}` (`x = 1`), `C(21m, 14m) 2^{14m} ≤ 3^{21m}` (`x = 2`), `C(7m, 6m) 6^{6m} ≤ 7^{7m}` (`x = 6`);
* `multinomial_term`: `M_m · 21^{21m} 14^{14m} 6^{6m} ≤ 42^{42m}`, after `21 = 3·7`, `14 = 2·7`,
  `42 = 2·3·7` (`AperyMultibound.mul_pw`) and the exponent splits (`pw_add`);
* `multibound` (`lem:multibound`, first part): `M_m ≤ A^m`, by `AperyMultibound.multibound_of_term`.

Here `M_m` is taken in its binomial-product form; its agreement with `(42m)!/((21m)!(14m)!(6m)!m!)` is the
standard factorial identity and is not restated.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (Aval mul_pw multibound_of_term)
open LeanProofs.IPRA.DiophantineNumberTheory.SuperellipticFamily (one_pw)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (tBody inst2_t binomial_at congrBinom congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- One binomial term: `C(n, j) x^j ≤ (x + 1)^n` for `j ≤ n`. -/
theorem binom_term {n j x : PTm k} (hj : Γ ⊢[PRAAx] le j n) :
    Γ ⊢[PRAAx] le (binom n j * pw x j) (pw (succ x) n) := by
  have t := term_le_sum (Γ := Γ) tBody (i := j) (M := succ n) (x := pairT n x)
    (by show Γ ⊢[PRAAx] le (succ j) (succ n); ipra_le sl hj)
  rw [inst2_t] at t
  exact le_congr (congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (.eqRefl _)))
    (binomial_at n x) t

/-- `M_m = C(42m, 21m) C(21m, 14m) C(7m, 6m)`. -/
abbrev Mm (m : PTm k) : PTm k :=
  binom (num 42 * m) (num 21 * m) * binom (num 21 * m) (num 14 * m) * binom (num 7 * m) (num 6 * m)

theorem base_split {a b c : ℕ} (h : a = b * c) (e : PTm k) :
    Γ ⊢[PRAAx] pw (num a) e ≐ pw (num b) e * pw (num c) e :=
  (congrPw (by apply deriveNat; ipra_simps; subst h; push_cast; ring) (.eqRefl e)).eqTrans (mul_pw _ _ e)

theorem exp_split (a b c : ℕ) (h : a = b + c) (x m : PTm k) :
    Γ ⊢[PRAAx] pw x (num a * m) ≐ pw x (num b * m) * pw x (num c * m) :=
  (congrPw (.eqRefl x) (by apply deriveNat; ipra_simps; subst h; push_cast; ring)).eqTrans (pw_add _ _ _)

/-- The multinomial term bound `M_m 21^{21m} 14^{14m} 6^{6m} ≤ 42^{42m}`. -/
theorem multinomial_term (m : PTm k) :
    Γ ⊢[PRAAx] le (Mm m * (pw (num 21) (num 21 * m) * pw (num 14) (num 14 * m) * pw (num 6) (num 6 * m)))
      (pw (num 42) (num 42 * m)) := by
  have b1 := binom_term (Γ := Γ) (n := num 42 * m) (j := num 21 * m) (x := one) (by ipra_le 21 * 𝔞 m)
  have b2 := binom_term (Γ := Γ) (n := num 21 * m) (j := num 14 * m) (x := two) (by ipra_le 7 * 𝔞 m)
  have b3 := binom_term (Γ := Γ) (n := num 7 * m) (j := num 6 * m) (x := num 6) (by ipra_le 𝔞 m)
  have o1 := natEq (one_pw (Γ := Γ) (num 21 * m))
  have e21 := natEq (base_split (Γ := Γ) (a := 21) (b := 3) (c := 7) rfl (num 21 * m))
  have e14 := natEq (base_split (Γ := Γ) (a := 14) (b := 2) (c := 7) rfl (num 14 * m))
  have e42a := natEq (base_split (Γ := Γ) (a := 42) (b := 6) (c := 7) rfl (num 42 * m))
  have e42b := natEq (base_split (Γ := Γ) (a := 6) (b := 2) (c := 3) rfl (num 42 * m))
  have x3 := natEq (exp_split (Γ := Γ) 42 21 21 rfl (num 3) m)
  have x7a := natEq (exp_split (Γ := Γ) 42 21 21 rfl (num 7) m)
  have x7b := natEq (exp_split (Γ := Γ) 21 14 7 rfl (num 7) m)
  have h2 : Γ ⊢[PRAAx] (succ one : PTm k) ≐ num 2 := by apply deriveNat; ipra_simps; ring
  have h3 : Γ ⊢[PRAAx] (succ two : PTm k) ≐ num 3 := by apply deriveNat; ipra_simps; ring
  have h7 : Γ ⊢[PRAAx] (succ (num 6) : PTm k) ≐ num 7 := by apply deriveNat; ipra_simps; ring
  have b1' := le_congr (.eqRefl _) (congrPw h2 (.eqRefl _)) b1
  have b2' := le_congr (congrMul (.eqRefl _) (congrPw ((by apply deriveNat; ipra_simps; ring :
    Γ ⊢[PRAAx] (two : PTm k) ≐ num 2)) (.eqRefl _))) (congrPw h3 (.eqRefl _)) b2
  have b3' := le_congr (.eqRefl _) (congrPw h7 (.eqRefl _)) b3
  ipra_le 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 21 * m)) * 𝔞 (pw (num 7) (num 14 * m)) * (sl b1' * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 7 * m)) + 𝔞 (binom (num 42 * m) (num 21 * m)) * sl b2' * 𝔞 (pw (num 7) (num 7 * m)) + 𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (binom (num 21 * m) (num 14 * m)) * 𝔞 (pw (num 2) (num 14 * m)) * sl b3') using
    linear_combination (-(𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (binom (num 21 * m) (num 14 * m)) * 𝔞 (binom (num 7 * m) (num 6 * m)) * 𝔞 (pw (num 6) (num 6 * m)) * 𝔞 (pw (num 14) (num 14 * m)))) * e21 + (-(𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (binom (num 21 * m) (num 14 * m)) * 𝔞 (binom (num 7 * m) (num 6 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 6) (num 6 * m)) * 𝔞 (pw (num 7) (num 21 * m)))) * e14 +
      e42a + 𝔞 (pw (num 7) (num 42 * m)) * e42b + (𝔞 (pw (num 2) (num 42 * m)) * 𝔞 (pw (num 7) (num 42 * m))) * x3 + (𝔞 (pw (num 2) (num 42 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m))) * x7a +
      (𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (pw one (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 14 * m)) * 𝔞 (pw (num 7) (num 7 * m)) - 𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 14 * m)) * 𝔞 (pw (num 7) (num 7 * m)) + 𝔞 (pw (num 2) (num 42 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 21 * m))) * x7b +
      (𝔞 (binom (num 42 * m) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 3) (num 21 * m)) * 𝔞 (pw (num 7) (num 14 * m)) * 𝔞 (pw (num 7) (num 14 * m)) * 𝔞 (pw (num 7) (num 7 * m)) * 𝔞 (pw (num 7) (num 7 * m))) * o1

/-- `lem:multibound`, first part: `M_m ≤ A^m` for `A = 2^22 3^15 7^7`. -/
theorem multibound (m : PTm k) : Γ ⊢[PRAAx] le (Mm m) (pw (num Aval) m) :=
  multibound_of_term (multinomial_term m)

end LeanProofs.IPRA.DiophantineNumberTheory.AperyMultinomial
