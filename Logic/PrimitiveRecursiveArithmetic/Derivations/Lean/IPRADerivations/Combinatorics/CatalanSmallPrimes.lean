import IPRADerivations.Combinatorics.CatalanPrimes
import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Core.LinearCombination

/-!
# The prime Catalan numbers: the small cases (`catalan_numbers_ipra_2026-11-16`, Section 5)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, theorem "Catalan primes": "The only
prime Catalan numbers are `Cat_2 = 2` and `Cat_3 = 5`. ... The small values are direct."

`Combinatorics/CatalanPrimes` shows that `Cat_n` is not prime for `n ≥ 4`. The remaining
indices:

* `cat_two`, `cat_three`: `Cat_2 = 2`, `Cat_3 = 5`, from the ratio recurrence;
* `cat_zero_not_prime`, `cat_one_not_prime`: `Cat_0 = Cat_1 = 1` are not prime;
* `prime_two`, `prime_five`: `2` and `5` are prime (`small_cases`: a number `e` with
  `2 ≤ e < 5` is `2`, `3` or `4`; `not_dvd_of`: a nonzero remainder excludes divisibility).

Together with `cat_not_prime` this is the theorem: among the Catalan numbers exactly `Cat_2`
and `Cat_3` are prime. The statements `prime (cat 2)` and `prime (cat 3)` themselves are the
two equations followed by `prime_two`, `prime_five`; the transport of `prime` along an equation
is not written out.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanSmallPrimes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Catalan
open LeanProofs.IPRA.Combinatorics.CatalanGrowth (cat_one)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.Foundations.FiniteSetExponential (pair_snd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `3`. -/
abbrev three : PTm n := succ two
/-- `4`. -/
abbrev four : PTm n := succ three
/-- `5`. -/
abbrev five : PTm n := succ four

/-! ## The values -/

/-- `Cat_2 = 2`. -/
theorem cat_two : Γ ⊢[PRAAx] cat (succ (succ (zero : PTm n))) ≐ two := by
  refine mul_cancel (D := three) (succ_pos two) ?_
  ipra_lc natEq (cat_rec (Γ := Γ) (succ zero)) + 6 * natEq (cat_one (Γ := Γ))

/-- `Cat_3 = 5`. -/
theorem cat_three : Γ ⊢[PRAAx] cat (succ (succ (succ (zero : PTm n)))) ≐ five := by
  refine mul_cancel (D := four) (succ_pos three) ?_
  ipra_lc natEq (cat_rec (Γ := Γ) (succ (succ zero))) + 10 * natEq (cat_two (Γ := Γ))

/-- `Cat_0 = 1` is not prime. -/
theorem cat_zero_not_prime : Γ ⊢[PRAAx] neg (prime (cat (zero : PTm n))) := by
  refine .impI ?_
  have hp : (prime (cat (zero : PTm n)) :: Γ) ⊢[PRAAx] prime (cat (zero : PTm n)) := Prf.hyp0
  exact not_succ_le_self one _ (le_congr (.eqRefl _) cat_zero (Prf.andE₁ hp))

/-- `Cat_1 = 1` is not prime. -/
theorem cat_one_not_prime : Γ ⊢[PRAAx] neg (prime (cat (succ (zero : PTm n)))) := by
  refine .impI ?_
  have hp : (prime (cat (succ (zero : PTm n))) :: Γ) ⊢[PRAAx]
      prime (cat (succ (zero : PTm n))) := Prf.hyp0
  exact not_succ_le_self one _ (le_congr (.eqRefl _) cat_one (Prf.andE₁ hp))

/-! ## The primes `2` and `5` -/

/-- `2` is prime. -/
theorem prime_two : Γ ⊢[PRAAx] prime (two : PTm n) := by
  unfold prime
  refine .andI (le_refl two) (.allI ?_)
  simp only [Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  exact .impI (.impI (le_lt_absurd _ Prf.hyp1 Prf.hyp0))

/-- A nonzero remainder excludes divisibility: if `e = m`, `F = i m + (c + 1)` and
`c + 1 < m`, then `e ∤ F`. -/
theorem not_dvd_of {e m F i c : PTm n} (he : Γ ⊢[PRAAx] e ≐ m)
    (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hF : Γ ⊢[PRAAx] F ≐ i * m + succ c)
    (hc : Γ ⊢[PRAAx] lt (succ c) m) : Γ ⊢[PRAAx] neg (dvd e F) := by
  refine .impI ?_
  have r : ((dvd e F) :: Γ) ⊢[PRAAx] rem F e ≐ succ c :=
    (congrAp2 remF hF.wk he.wk).eqTrans (pair_snd hm.wk hc.wk)
  exact succ_ne_zero' _ (r.eqSymm.eqTrans Prf.hyp0)

/-- A number `e` with `2 ≤ e < 5` is `2`, `3` or `4`. -/
theorem small_cases {e : PTm n} (h2 : Γ ⊢[PRAAx] le two e) (h5 : Γ ⊢[PRAAx] lt e five) :
    Γ ⊢[PRAAx] (e ≐ two) ⋎ ((e ≐ three) ⋎ (e ≐ four)) := by
  have e₀ := eq_add_of_le h2
  refine .orE (zero_or_succ (monus e two)) ?_ ?_
  · refine .orI₁ ?_
    have z := natEq (Prf.hyp0 (Γ := Γ) (φ := monus e two ≐ zero))
    have a := natEq (e₀.wk (ψ := monus e two ≐ zero))
    apply deriveNat; ipra_simps
    linear_combination a + z
  · refine .orE (zero_or_succ (pred (monus e two))) ?_ ?_
    · refine .orI₂ (.orI₁ ?_)
      have z := natEq (Prf.hyp0 (Γ := (monus e two ≐ succ (pred (monus e two))) :: Γ)
        (φ := pred (monus e two) ≐ zero))
      have s := natEq (Prf.hyp1 (Γ := Γ) (φ := monus e two ≐ succ (pred (monus e two)))
        (ψ := pred (monus e two) ≐ zero))
      have a := natEq ((e₀.wk (ψ := monus e two ≐ succ (pred (monus e two)))).wk
        (ψ := pred (monus e two) ≐ zero))
      apply deriveNat; ipra_simps
      linear_combination a + s + z
    · refine .orE (zero_or_succ (pred (pred (monus e two)))) ?_ ?_
      · refine .orI₂ (.orI₂ ?_)
        have z := natEq (Prf.hyp0
          (Γ := (pred (monus e two) ≐ succ (pred (pred (monus e two)))) ::
            (monus e two ≐ succ (pred (monus e two))) :: Γ)
          (φ := pred (pred (monus e two)) ≐ zero))
        have s₂ := natEq (Prf.hyp1
          (Γ := (monus e two ≐ succ (pred (monus e two))) :: Γ)
          (φ := pred (monus e two) ≐ succ (pred (pred (monus e two))))
          (ψ := pred (pred (monus e two)) ≐ zero))
        have s₁ := natEq (hyp2 (Γ := Γ) (φ := monus e two ≐ succ (pred (monus e two)))
          (ψ := pred (monus e two) ≐ succ (pred (pred (monus e two))))
          (χ := pred (pred (monus e two)) ≐ zero))
        have a := natEq (((e₀.wk (ψ := monus e two ≐ succ (pred (monus e two)))).wk
          (ψ := pred (monus e two) ≐ succ (pred (pred (monus e two))))).wk
          (ψ := pred (pred (monus e two)) ≐ zero))
        apply deriveNat; ipra_simps
        linear_combination a + s₁ + s₂ + z
      · -- `e ≥ 5`, against `e < 5`
        have s₃ := natEq (Prf.hyp0
          (Γ := (pred (monus e two) ≐ succ (pred (pred (monus e two)))) ::
            (monus e two ≐ succ (pred (monus e two))) :: Γ)
          (φ := pred (pred (monus e two)) ≐ succ (pred (pred (pred (monus e two))))))
        have s₂ := natEq (Prf.hyp1
          (Γ := (monus e two ≐ succ (pred (monus e two))) :: Γ)
          (φ := pred (monus e two) ≐ succ (pred (pred (monus e two))))
          (ψ := pred (pred (monus e two)) ≐ succ (pred (pred (pred (monus e two))))))
        have s₁ := natEq (hyp2 (Γ := Γ) (φ := monus e two ≐ succ (pred (monus e two)))
          (ψ := pred (monus e two) ≐ succ (pred (pred (monus e two))))
          (χ := pred (pred (monus e two)) ≐ succ (pred (pred (pred (monus e two))))))
        have a := natEq (((e₀.wk (ψ := monus e two ≐ succ (pred (monus e two)))).wk
          (ψ := pred (monus e two) ≐ succ (pred (pred (monus e two))))).wk
          (ψ := pred (pred (monus e two)) ≐ succ (pred (pred (pred (monus e two))))))
        refine le_lt_absurd _ (le_of_eq_add (d := pred (pred (pred (monus e two)))) ?_)
          h5.wk.wk.wk
        ipra_lc a + s₁ + s₂ + s₃

/-- `5` is prime. -/
theorem prime_five : Γ ⊢[PRAAx] prime (five : PTm n) := by
  unfold prime
  refine .andI (le_of_eq_add (d := three) (by ipra_ring)) (.allI ?_)
  simp only [Syn.shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  refine .impI (.impI ?_)
  refine .orE (small_cases Prf.hyp1 Prf.hyp0) ?_ (.orE Prf.hyp0 ?_ ?_)
  · exact not_dvd_of (m := two) (i := two) (c := zero) Prf.hyp0 (succ_pos one)
      (by ipra_ring) (le_refl two)
  · exact not_dvd_of (m := three) (i := one) (c := one) Prf.hyp0 (succ_pos two)
      (by ipra_ring) (le_refl three)
  · exact not_dvd_of (m := four) (i := one) (c := zero) Prf.hyp0 (succ_pos three)
      (by ipra_ring)
      (le_of_eq_add (d := two) (by ipra_ring))

end LeanProofs.IPRA.Combinatorics.CatalanSmallPrimes
