import IPRADerivations.AnalyticNumberTheory.ValuationMul
import IPRADerivations.Foundations.BoundedDecision
import IPRADerivations.Core.OrderCertificates

/-!
# Primality of numerals by trial division

A reusable piece of the embedding framework: a primality certificate checked in the metatheory becomes a
derivation of `prime (num p)` in iPRA.

The certificate for `p ≥ 2` is a bound `r` with `p < (r + 1)²` and the remainders `p mod j ≠ 0` for
`2 ≤ j ≤ r` (a decidable statement about natural numbers; `decide` closes it). The derivation follows the
usual argument: a divisor `e` of `p` with `2 ≤ e < p` has a cofactor `c = p / e ≥ 2`, and the smaller of `e`,
`c` is a divisor `d ≥ 2` with `d² ≤ p`, hence `d ≤ r`; the bounded case split `cases_num` then names `d` as a
numeral `j`, and `p = j ⌊p/j⌋ + (p mod j)` with `0 < p mod j < j` excludes `j ∣ p`.

* `subst_num`, `shift_num`: numerals are closed terms;
* `num_le`, `num_lt`, `num_mul`, `num_pos`: order and products of numerals;
* `not_dvd_num`: `p mod j ≠ 0` gives `¬ (d ∣ p)` for `d = j`;
* `no_small`: no `d` with `2 ≤ d`, `d² ≤ p` divides `p`;
* `no_divisor`: no `e` with `2 ≤ e < p` divides `p`;
* `prime_num`: `prime (num p)`.

The size of the derivation is linear in `r`. First use: the ten primes of the finite certificate of
Bertrand's postulate (`AnalyticNumberTheory/BertrandCertificate`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.NumeralPrimes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm dmu)
open LeanProofs.IPRA.Foundations.BoundedDecision (cases_num)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Numerals -/

theorem subst_num {m : ℕ} (σ : Fin n → PTm m) : ∀ k : ℕ, Syn.subst σ (num k : PTm n) = num k
  | 0 => by simp only [num, ConciseIPRA.PTm.subst_zero]
  | k + 1 => by simp only [num, ConciseIPRA.PTm.subst_succ, subst_num σ k]

theorem shift_num (k : ℕ) : Syn.shift (num k : PTm n) = num k := by simp [Syn.shift, subst_num]

theorem num_le {a b : ℕ} (h : a ≤ b) : Γ ⊢[PRAAx] le (num a : PTm n) (num b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  ipra_le (c : Groth (Q Γ)) using push_cast; ring

theorem num_lt {a b : ℕ} (h : a < b) : Γ ⊢[PRAAx] lt (num a : PTm n) (num b) := num_le (a := a + 1) h

theorem num_mul (a b : ℕ) : Γ ⊢[PRAAx] (num a : PTm n) * num b ≐ num (a * b) := by
  apply deriveNat; ipra_simps
  exact (Nat.cast_mul a b).symm

theorem num_pos {a : ℕ} (h : 1 ≤ a) : Γ ⊢[PRAAx] (num a : PTm n) ≐ succ (pred (num a)) := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  exact congrSucc (pred_succ _).eqSymm

theorem one_le_of_pos {c : PTm n} (h : Γ ⊢[PRAAx] c ≐ succ (pred c)) : Γ ⊢[PRAAx] le one c := by
  have e := natEq h
  exact le_of_eq_add (d := pred c) (by apply deriveNat; ipra_simps; linear_combination e)

/-! ## Remainders of numerals -/

/-- `p mod j ≠ 0` excludes `d ∣ p` for `d = j`. -/
theorem not_dvd_num {d : PTm n} (p j : ℕ) (hj : 1 ≤ j) (hr : p % j ≠ 0) (hd : Γ ⊢[PRAAx] d ≐ num j)
    (h : Γ ⊢[PRAAx] dvd d (num p)) : Γ ⊢[PRAAx] Fm.bot := by
  obtain ⟨c, hc⟩ : ∃ c, p % j = c + 1 := ⟨p % j - 1, by omega⟩
  have key : p = j * (p / j) + (c + 1) := by rw [← hc]; exact (Nat.div_add_mod p j).symm
  have hz : Γ ⊢[PRAAx] (num p : PTm n) ≐ num j * num (p / j) + succ (num c) := by
    apply deriveNat; ipra_simps
    have k2 := congrArg (fun t : ℕ => (t : Groth (Q Γ))) key
    push_cast at k2
    linear_combination k2
  have hlt : Γ ⊢[PRAAx] lt (succ (num c) : PTm n) (num j) :=
    num_lt (a := c + 1) (by have := Nat.mod_lt p hj; omega)
  have r := Prf.andE₂ (dmu (num_pos hj) hz hlt)
  have r' : Γ ⊢[PRAAx] rem (num p) d ≐ succ (num c) := (congrAp2 remF (.eqRefl _) hd).eqTrans r
  exact succ_ne_zero' _ (r'.eqSymm.eqTrans h)

/-- No `d` with `2 ≤ d` and `d² ≤ p` divides the numeral `p`. -/
theorem no_small {d : PTm n} (p r : ℕ) (hr : p < (r + 1) * (r + 1))
    (hnd : ∀ j, j < r + 1 → 2 ≤ j → p % j ≠ 0)
    (h2 : Γ ⊢[PRAAx] le two d) (hsq : Γ ⊢[PRAAx] le (d * d) (num p)) (hd : Γ ⊢[PRAAx] dvd d (num p)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have hle : Γ ⊢[PRAAx] le d (num r) := by
    refine .orE (lt_or_le (num r) d) ?_ Prf.hyp0
    have hl : (lt (num r) d :: Γ) ⊢[PRAAx] le (num (r + 1)) d := Prf.hyp0
    have m : (lt (num r) d :: Γ) ⊢[PRAAx] le (num (r + 1) * num (r + 1)) (d * d) := by
      ipra_le sl hl * sl hl + 2 * ((r + 1 : ℕ) : Groth (Q _)) * sl hl using push_cast; ring
    have m' := le_congr (num_mul (r + 1) (r + 1)) (.eqRefl _) (le_trans m hsq.wk)
    exact le_lt_absurd _ m' (num_lt hr)
  refine cases_num r hle (fun j hj => .impI ?_)
  by_cases hj2 : 2 ≤ j
  · exact not_dvd_num p j (by omega) (hnd j (by omega) hj2) Prf.hyp0 hd.wk
  · have a : ((d ≐ num j) :: Γ) ⊢[PRAAx] le two (num j) := le_congr (.eqRefl _) Prf.hyp0 h2.wk
    have b : ((d ≐ num j) :: Γ) ⊢[PRAAx] lt (num j) two := num_lt (a := j) (b := 2) (by omega)
    exact le_lt_absurd _ a b

/-- No `e` with `2 ≤ e < p` divides the numeral `p`. -/
theorem no_divisor {e : PTm n} (p r : ℕ) (hr : p < (r + 1) * (r + 1))
    (hnd : ∀ j, j < r + 1 → 2 ≤ j → p % j ≠ 0)
    (h2 : Γ ⊢[PRAAx] le two e) (hlt : Γ ⊢[PRAAx] lt e (num p)) (hd : Γ ⊢[PRAAx] dvd e (num p)) :
    Γ ⊢[PRAAx] Fm.bot := by
  have epos := p_pos h2
  have de : Γ ⊢[PRAAx] num p ≐ e * quo (num p) e + zero :=
    (Prf.andE₁ (dm epos (num p))).eqTrans (congrAdd (.eqRefl _) hd)
  refine .orE (lt_or_le (quo (num p) e) e) ?_ ?_
  · -- the cofactor `c = p / e` is the smaller one
    have hce : (lt (quo (num p) e) e :: Γ) ⊢[PRAAx] le (quo (num p) e) e := le_of_lt Prf.hyp0
    have den := natEq (de.wk (ψ := lt (quo (num p) e) e))
    have hc2 : (lt (quo (num p) e) e :: Γ) ⊢[PRAAx] le two (quo (num p) e) := by
      refine .orE (lt_or_le (quo (num p) e) two) ?_ Prf.hyp0
      have hc1 : (lt (quo (num p) e) two :: lt (quo (num p) e) e :: Γ) ⊢[PRAAx] lt (quo (num p) e) two :=
        Prf.hyp0
      have hlt' : (lt (quo (num p) e) two :: lt (quo (num p) e) e :: Γ) ⊢[PRAAx] lt e (num p) := hlt.wk.wk
      have den' := natEq ((de.wk (ψ := lt (quo (num p) e) e)).wk (ψ := lt (quo (num p) e) two))
      have bad : (lt (quo (num p) e) two :: lt (quo (num p) e) e :: Γ) ⊢[PRAAx] le one zero := by
        ipra_le sl hlt' + 𝔞 e * sl hc1 with den'
      exact lt_zero_absurd _ bad
    have cpos := p_pos hc2
    have hz : (lt (quo (num p) e) e :: Γ) ⊢[PRAAx] num p ≐ quo (num p) e * e + zero := by
      apply deriveNat; ipra_simps; linear_combination den
    have dc : (lt (quo (num p) e) e :: Γ) ⊢[PRAAx] dvd (quo (num p) e) (num p) :=
      Prf.andE₂ (dmu cpos hz (one_le_of_pos cpos))
    have csq : (lt (quo (num p) e) e :: Γ) ⊢[PRAAx] le (quo (num p) e * quo (num p) e) (num p) := by
      ipra_le 𝔞 (quo (num p) e) * sl hce with den
    exact no_small p r hr hnd hc2 csq dc
  · -- `e` is the smaller one
    have hh : (le e (quo (num p) e) :: Γ) ⊢[PRAAx] le e (quo (num p) e) := Prf.hyp0
    have den := natEq (de.wk (ψ := le e (quo (num p) e)))
    have hsq : (le e (quo (num p) e) :: Γ) ⊢[PRAAx] le (e * e) (num p) := by
      ipra_le 𝔞 e * sl hh with den
    exact no_small p r hr hnd h2.wk hsq hd.wk

/-- `prime (num p)` from a trial-division certificate: `p ≥ 2`, `p < (r + 1)²`, and `p mod j ≠ 0` for
`2 ≤ j ≤ r`. -/
theorem prime_num (p r : ℕ) (hp2 : 2 ≤ p) (hr : p < (r + 1) * (r + 1))
    (hnd : ∀ j, j < r + 1 → 2 ≤ j → p % j ≠ 0) : Γ ⊢[PRAAx] prime (num p : PTm n) := by
  unfold prime
  refine .andI (num_le (a := 2) hp2) (.allI (.impI (.impI (.impI ?_))))
  rw [shift_num]
  exact no_divisor p r hr hnd (.hyp (by simp)) (.hyp (by simp)) Prf.hyp0

end LeanProofs.IPRA.Foundations.NumeralPrimes
