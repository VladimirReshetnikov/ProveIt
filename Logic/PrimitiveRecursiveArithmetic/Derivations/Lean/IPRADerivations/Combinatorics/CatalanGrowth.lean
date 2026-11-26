import IPRADerivations.Combinatorics.Catalan

/-!
# Growth of the Catalan numbers (`catalan_numbers_ipra_2026-11-16`, Section 5)

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Subsection "The only prime Catalan
numbers", the lemma "For every `n ≥ 4`, `Cat_n > 2n - 1`": "The base case is `Cat_4 = 14 > 7`.
From Equation (ratio-cleared), for `n ≥ 1`, `Cat_{n+1} ≥ 2 Cat_n`, because
`2(2n + 1) ≥ 2(n + 2)`."

With `cat n = Cat_n` of `Combinatorics/Catalan` and its ratio recurrence `cat_rec`
(`(n + 2) Cat_{n+1} = 2 (2n + 1) Cat_n`):

* `cat_one`: `Cat_1 = 1`;
* `cat_double`: `2 Cat_{j+1} ≤ Cat_{j+2}`, that is `Cat_{n+1} ≥ 2 Cat_n` for `n ≥ 1`;
* `cat_four`: `8 ≤ Cat_4`;
* `cat_ge`: `2 (m + 4) ≤ Cat_{m+4}`, that is `Cat_n ≥ 2n` (equivalently `Cat_n > 2n - 1`) for
  `n ≥ 4`; closed form `cat_ge_closed`.

The lemma "every prime divisor of `Cat_n` is less than `2n`" and the theorem on Catalan primes,
which combines it with `cat_ge`, are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanGrowth

open_ipra
open LeanProofs.IPRA.Combinatorics.Catalan
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `Cat_1 = 1`. -/
theorem cat_one : Γ ⊢[PRAAx] cat (succ (zero : PTm n)) ≐ one := by
  refine mul_cancel (D := two) (succ_pos one) ?_
  ipra_lc natEq (cat_rec (Γ := Γ) zero) + 2 * natEq (cat_zero (Γ := Γ))

/-- `Cat_{n+1} ≥ 2 Cat_n` for `n = j + 1 ≥ 1`. -/
theorem cat_double (j : PTm n) :
    Γ ⊢[PRAAx] le (two * cat (succ j)) (cat (succ (succ j))) := by
  refine mul_le_cancel (d' := succ (succ j))
    (le_of_eq_add (d := two * j * cat (succ j)) ?_)
  ipra_lc natEq (cat_rec (Γ := Γ) (succ j))

/-- `8 ≤ Cat_4`. -/
theorem cat_four :
    Γ ⊢[PRAAx] le (two * (two * two)) (cat (succ (succ (succ (succ (zero : PTm n)))))) := by
  refine le_of_eq_add (d :=
    two * two * monus (cat (succ (succ zero))) (two * cat (succ zero)) +
      two * monus (cat (succ (succ (succ zero)))) (two * cat (succ (succ zero))) +
      monus (cat (succ (succ (succ (succ zero))))) (two * cat (succ (succ (succ zero))))) ?_
  ipra_lc natEq (eq_add_of_le (cat_double (Γ := Γ) (succ (succ zero)))) +
    2 * natEq (eq_add_of_le (cat_double (Γ := Γ) (succ zero))) + 4 * natEq (eq_add_of_le (cat_double (Γ := Γ) zero)) +
    8 * natEq (cat_one (Γ := Γ))

theorem ge_step {m : PTm n}
    (ih : Γ ⊢[PRAAx] le (two * succ (succ (succ (succ m)))) (cat (succ (succ (succ (succ m)))))) :
    Γ ⊢[PRAAx] le (two * succ (succ (succ (succ (succ m)))))
      (cat (succ (succ (succ (succ (succ m)))))) := by
  refine le_of_eq_add (d := two * m + two * (two + one) +
    two * monus (cat (succ (succ (succ (succ m))))) (two * succ (succ (succ (succ m)))) +
    monus (cat (succ (succ (succ (succ (succ m))))))
      (two * cat (succ (succ (succ (succ m)))))) ?_
  ipra_lc natEq (eq_add_of_le (cat_double (Γ := Γ) (succ (succ (succ m))))) + 2 * natEq (eq_add_of_le ih)

/-- Variable: `0 = m`. -/
private abbrev geF : Fm PTm 1 :=
  le (two * succ (succ (succ (succ (var 0))))) (cat (succ (succ (succ (succ (var 0))))))

private theorem ge₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] geF := by
  ipra_ind [subst_le, subst_ap2]
  · exact le_congr (by ipra_ring) (.eqRefl _) cat_four
  · exact ge_step Prf.hyp0

/-- `Cat_n ≥ 2n` for `n = m + 4 ≥ 4`. -/
theorem cat_ge (m : PTm n) :
    Γ ⊢[PRAAx] le (two * succ (succ (succ (succ m)))) (cat (succ (succ (succ (succ m))))) := by
  have h := inst (Γ := Γ) ge₀ (![m] : Fin 1 → PTm n)
  simpa using h

/-- `Cat_{m+4} ≥ 2 (m + 4)` as a closed sentence. -/
theorem cat_ge_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le (two * succ (succ (succ (succ (var 0))))) (cat (succ (succ (succ (succ (var 0))))))) :=
  closeUniv 1 (cat_ge _)

end LeanProofs.IPRA.Combinatorics.CatalanGrowth
