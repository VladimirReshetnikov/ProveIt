import IPRADerivations.Combinatorics.CatalanHalving

/-!
# The ballot factor in the square sum

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Square sum", (2.20)): for
`k ≤ n/2`, `d_k = C(n, k) − C(n, k − 1) = (n − 2k + 1)/(n − k + 1) · C(n, n − k)`. Cleared of the
denominator, with `d_k` the absolute difference of `Combinatorics/CatalanHalving`:

* `binom_ratio`: `(n − j) C(n, j) = (j + 1) C(n, j + 1)` for `j < n`;
* `ballot_le`: `C(n, k − 1) ≤ C(n, k)` for `2k ≤ n`, so `d_k = C(n, k) ∸ C(n, k − 1)`;
* `ballot_factor`: `(n + 1 − k) d_k = (n + 1 − 2k) C(n, k)` for `2k ≤ n`;
* `ballot_factor'`: the same with `C(n, n − k)`, the form displayed in (2.20).

With `square_sum_half`, `Cat_n = ∑_{k ≤ ⌊n/2⌋} d_k²` and these values of `d_k` give (2.20).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanBallot

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (gb_symm)
open LeanProofs.IPRA.Combinatorics.CatalanHalving (pv pv_zero pv_succ congrAd)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(n − j) C(n, j) = (j + 1) C(n, j + 1)` for `j < n`. -/
theorem binom_ratio {j N : PTm n} (h : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] monus N j * binom N j ≐ succ j * binom N (succ j) := by
  have eN := eq_add_of_le h   -- `N = (j + 1) + (N ∸ (j + 1))`
  have r : Γ ⊢[PRAAx] monus N j ≐ succ (monus N (succ j)) := by
    have a := natEq eN
    have e : Γ ⊢[PRAAx] N ≐ succ (monus N (succ j)) + j := by apply deriveNat; ipra_simps; linear_combination a
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  refine mul_cancel (D := fact j * fact (monus N (succ j))) (pos_mul' (fact_pos _) (fact_pos _)) ?_
  ipra_lc -natEq (binom_eq (le_of_lt h)) + natEq (binom_eq h) -
    𝔞(fact j) * 𝔞(binom N j) * natEq ((congrAp2 factF r (.eqRefl zero)).eqTrans (fact_succ (Γ := Γ) (monus N (succ j)) zero)) +
    𝔞(fact (monus N (succ j))) * 𝔞(binom N (succ j)) * natEq (fact_succ (Γ := Γ) j zero) +
    𝔞(fact j) * 𝔞(fact (monus N (succ j))) * 𝔞(binom N j) * natEq r

/-! ## The ballot numbers -/

section Ballot

variable {j N : PTm n}

/-- With `2(j + 1) ≤ n`: `n + 1 = (E + 1) + (j + 1) + (j + 1)`, `E = n ∸ 2(j + 1)`. -/
theorem split_N (h : Γ ⊢[PRAAx] le (succ j + succ j) N) :
    Γ ⊢[PRAAx] succ N ≐ succ (monus N (succ j + succ j)) + succ j + succ j := by
  ipra_lc natEq (eq_add_of_le h)

theorem A_eq (h : Γ ⊢[PRAAx] le (succ j + succ j) N) :
    Γ ⊢[PRAAx] monus (succ N) (succ j) ≐ succ (monus N (succ j + succ j)) + succ j :=
  (congrMonus (split_N h) (.eqRefl _)).eqTrans (add_monus _ _)

theorem B_eq (h : Γ ⊢[PRAAx] le (succ j + succ j) N) :
    Γ ⊢[PRAAx] monus (succ N) (succ j + succ j) ≐ succ (monus N (succ j + succ j)) :=
  (congrMonus ((split_N h).eqTrans (add_assoc _ _ _)) (.eqRefl _)).eqTrans (add_monus _ _)

theorem lt_jN (h : Γ ⊢[PRAAx] le (succ j + succ j) N) : Γ ⊢[PRAAx] lt j N :=
  le_trans (le_add_right (succ j) (succ j)) h

/-- `(n − j) C(n, j) = (j + 1) C(n, j + 1)` for the guarded coefficients, `2(j + 1) ≤ n`. -/
theorem gb_ratio (h : Γ ⊢[PRAAx] le (succ j + succ j) N) :
    Γ ⊢[PRAAx] monus N j * gb N j ≐ succ j * gb N (succ j) := by
  have hl := lt_jN h
  ipra_lc 𝔞(monus N j) * 𝔞(binom N j) * natEq (gle_of_le (le_of_lt hl)) -
    (𝔞(j) + 1) * 𝔞(binom N (succ j)) * natEq (gle_of_le hl) + natEq (binom_ratio hl)

/-- `C(n, j) ≤ C(n, j + 1)` for `2(j + 1) ≤ n`. -/
theorem ballot_le (h : Γ ⊢[PRAAx] le (succ j + succ j) N) : Γ ⊢[PRAAx] le (gb N j) (gb N (succ j)) := by
  have hA : Γ ⊢[PRAAx] monus N j ≐ succ (monus N (succ j + succ j)) + succ j := by
    have e : Γ ⊢[PRAAx] N ≐ (succ (monus N (succ j + succ j)) + succ j) + j := by
      ipra_lc natEq (eq_add_of_le h)
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  refine mul_le_cancel (d' := j) ?_
  refine le_congr (.eqRefl _) (gb_ratio h) (le_of_eq_add (d := succ (monus N (succ j + succ j)) * gb N j) ?_)
  exact (congrMul hA (.eqRefl _)).eqTrans ((add_mul _ _ _).eqTrans (add_comm _ _))

/-- `a = b + D`, `A b = J a` and `A = B + J` give `A D = B a`. -/
theorem aux {a b D A B J : PTm n} (e : Γ ⊢[PRAAx] a ≐ b + D) (r : Γ ⊢[PRAAx] A * b ≐ J * a)
    (hA : Γ ⊢[PRAAx] A ≐ B + J) : Γ ⊢[PRAAx] A * D ≐ B * a := by
  have e' := natEq e; have r' := natEq r; have h' := natEq hA
  apply deriveNat; ipra_simps
  linear_combination -𝔞(A) * e' - r' + 𝔞(a) * h'

/-- `(n + 1 − k) d_k = (n + 1 − 2k) C(n, k)` for `k = j + 1`, `2k ≤ n`. -/
theorem ballot_factor_succ (h : Γ ⊢[PRAAx] le (succ j + succ j) N) :
    Γ ⊢[PRAAx] monus (succ N) (succ j) * ad (gb N (succ j)) (pv N (succ j)) ≐
      monus (succ N) (succ j + succ j) * gb N (succ j) := by
  have le' := ballot_le h
  have ad' : Γ ⊢[PRAAx] ad (gb N (succ j)) (pv N (succ j)) ≐ monus (gb N (succ j)) (gb N j) :=
    (congrAd (.eqRefl _) (pv_succ _ _)).eqTrans ((congrAdd (.eqRefl _) le').eqTrans (add_zero _))
  have r : Γ ⊢[PRAAx] monus (succ N) (succ j) * gb N j ≐ succ j * gb N (succ j) :=
    (congrMul (succ_monus_succ _ _) (.eqRefl _)).eqTrans (gb_ratio h)
  have hA : Γ ⊢[PRAAx] monus (succ N) (succ j) ≐ monus (succ N) (succ j + succ j) + succ j :=
    (A_eq h).eqTrans (congrAdd (B_eq h).eqSymm (.eqRefl _))
  exact (congrMul (.eqRefl _) ad').eqTrans (aux (eq_add_of_le le') r hA)

end Ballot

/-- `(n + 1 − k) d_k = (n + 1 − 2k) C(n, k)` for `2k ≤ n`. -/
theorem ballot_factor {k N : PTm n} (h : Γ ⊢[PRAAx] le (k + k) N) :
    Γ ⊢[PRAAx] monus (succ N) k * ad (gb N k) (pv N k) ≐ monus (succ N) (k + k) * gb N k := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have e : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    have kk : ((k ≐ zero) :: Γ) ⊢[PRAAx] k + k ≐ zero := (congrAdd e e).eqTrans (add_zero _)
    have d : ((k ≐ zero) :: Γ) ⊢[PRAAx] ad (gb N k) (pv N k) ≐ gb N k := by
      have g := (congrGb (.eqRefl N) e).eqTrans (gb_zero N)
      have p := (CatalanHalving.congrPv e).eqTrans (pv_zero N)
      exact (congrAd g p).eqTrans ((congrAdd (monus_zero _) (zero_monus _)).eqTrans
        ((add_zero _).eqTrans g.eqSymm))
    refine (congrMul (congrMonus (.eqRefl _) e) d).eqTrans (congrMul ?_ (.eqRefl _))
    exact (monus_zero _).eqTrans ((monus_zero _).eqSymm.eqTrans (congrMonus (.eqRefl _) kk.eqSymm))
  · have e : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have h' : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] le (succ (pred k) + succ (pred k)) N :=
      le_congr (congrAdd e e) (.eqRefl _) h.wk
    refine (congrMul (congrMonus (.eqRefl _) e) (congrAd (congrGb (.eqRefl _) e) (CatalanHalving.congrPv e))).eqTrans
      ((ballot_factor_succ h').eqTrans ?_)
    exact congrMul (congrMonus (.eqRefl _) (congrAdd e e).eqSymm) (congrGb (.eqRefl _) e.eqSymm)

/-- The displayed form: `(n + 1 − k) d_k = (n + 1 − 2k) C(n, n − k)` for `2k ≤ n`. -/
theorem ballot_factor' {k N : PTm n} (h : Γ ⊢[PRAAx] le (k + k) N) :
    Γ ⊢[PRAAx] monus (succ N) k * ad (gb N k) (pv N k) ≐ monus (succ N) (k + k) * gb N (monus N k) :=
  (ballot_factor h).eqTrans (congrMul (.eqRefl _) (gb_symm (le_trans (le_add_right k k) h)).eqSymm)

end LeanProofs.IPRA.Combinatorics.CatalanBallot
