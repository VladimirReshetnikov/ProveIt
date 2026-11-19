import IPRADerivations.Probability.NormalMoments
import IPRADerivations.Probability.BinomialLaw
import IPRADerivations.Foundations.HurwitzProduct
import IPRADerivations.Core.OrderCertificates

/-!
# The coefficient array of the Hermite polynomials and of the raw normal moments

Packet: `probability/normal_distribution_ipra_2026-11-16`, `paper/sections/05_moments_hermite.tex`:

* Corollary `cor:raw-moments`: `E Xⁿ = ∑_{j ≤ n/2} C(n, 2j) (2j − 1)!! σ^{2j} μ^{n−2j}
  = ∑_j n!/(2^j j! (n − 2j)!) σ^{2j} μ^{n−2j}`, and (`eq:raw-rec`) `M_{n+1} = μ M_n + n σ² M_{n−1}`,
  where "the direct coefficient proof is a finite ring identity";
* `eq:hermite-def`: `He_{n+1}(x) = x He_n(x) − n He_{n−1}(x)`, "a primitive-recursive coefficient array";
* `eq:hermite-derivative` of Theorem `thm:hermite-derivatives`: `He_n′(x) = n He_{n−1}(x)`.

The three statements concern one array: `c(n, j) = C(n, 2j) (2j − 1)!!`, the coefficient of
`σ^{2j} μ^{n−2j}` in `E Xⁿ` and, with the sign `(−1)^j`, the coefficient of `x^{n−2j}` in `He_n`.

* `hc`: the array, `hc m j = C(m, 2j) · df j` with `df j = (2j − 1)!!` of `Probability/NormalMoments`;
* `hc_zero`: `c(n, 0) = 1` (the leading coefficient);
* `hc_rec`: for `2j + 1 ≤ m`, `c(m + 2, j + 1) = c(m + 1, j + 1) + (m + 1) c(m, j)`; this is the
  coefficient of `σ^{2j+2} μ^{m−2j}` in `eq:raw-rec` and, multiplied by `(−1)^{j+1}`, the coefficient of
  `x^{m−2j}` in `eq:hermite-def`;
* `hc_top`: `c(2j + 2, j + 1) = (2j + 1) c(2j, j)`, the same recurrence for the constant coefficient of an
  even index, where the middle term is absent;
* `binom_lower`: `(m − k + 1) C(m + 1, k) = (m + 1) C(m, k)` for `k ≤ m`;
* `hc_deriv`: for `2j ≤ m`, `(m + 1 − 2j) c(m + 1, j) = (m + 1) c(m, j)`, the coefficient of `x^{m−2j}`
  in `He_{m+1}′ = (m + 1) He_m`;
* `hc_closed`: for `2j ≤ m`, `c(m, j) · 2^j j! (m − 2j)! = m!`, the second form in `cor:raw-moments`.

The binomial coefficient of the library is the quotient `n!/(k! (n ∸ k)!)`, which is meaningful for
`k ≤ n` only; the guards are the ranges in which the coefficients occur. The identification of the
array with moments (the integrals) and the analytic statements of `thm:hermite-derivatives` are not
derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.HermiteCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel pascal_at binom_zero' binom_self')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Probability.BinomialLaw (absorption)
open LeanProofs.IPRA.Probability.NormalMoments (df df_zero df_succ df_fact)
open LeanProofs.IPRA.Foundations.HurwitzProduct (succ_monus_of_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `c(m, j) = C(m, 2j) (2j − 1)!!`. -/
abbrev hc (m j : PTm n) : PTm n := binom m (two * j) * df j

/-- The leading coefficient: `c(m, 0) = 1`. -/
theorem hc_zero (m : PTm n) : Γ ⊢[PRAAx] hc m zero ≐ one := by
  have b := natEq ((congrBinom (.eqRefl m) (mul_zero (Γ := Γ) (two : PTm n))).eqTrans (binom_zero' m))
  have d := natEq (df_zero (Γ := Γ))
  apply deriveNat; ipra_simps
  linear_combination 𝔟(df (zero : PTm n)) * b + d

theorem two_succ (j : PTm n) : Γ ⊢[PRAAx] two * succ j ≐ succ (succ (two * j)) := by
  apply deriveNat; ipra_simps; ring

/-- `eq:raw-rec` and `eq:hermite-def`, coefficientwise:
`c(m + 2, j + 1) = c(m + 1, j + 1) + (m + 1) c(m, j)` for `2j + 1 ≤ m`. -/
theorem hc_rec {m j : PTm n} (h : Γ ⊢[PRAAx] le (succ (two * j)) m) :
    Γ ⊢[PRAAx] hc (succ (succ m)) (succ j) ≐ hc (succ m) (succ j) + succ m * hc m j := by
  have hlt : Γ ⊢[PRAAx] lt (succ (two * j)) (succ m) := (succ_monus_succ _ _).eqTrans h
  have c₂ := natEq (congrBinom (.eqRefl (succ (succ m))) (two_succ (Γ := Γ) j))
  have c₁ := natEq (congrBinom (.eqRefl (succ m)) (two_succ (Γ := Γ) j))
  have pa := natEq (pascal_at hlt)
  have ab := natEq (absorption (le_trans (le_succ_self (two * j)) h))
  have ds := natEq (df_succ (Γ := Γ) j)
  apply deriveNat; ipra_simps
  linear_combination 𝔟(df (succ j)) * c₂ + 𝔟(df (succ j)) * pa - 𝔟(df (succ j)) * c₁ +
    𝔟(binom (succ m) (succ (two * j))) * ds + 𝔟(df j) * ab

/-- The recurrence for the constant coefficient of an even index:
`c(2j + 2, j + 1) = (2j + 1) c(2j, j)`. -/
theorem hc_top (j : PTm n) :
    Γ ⊢[PRAAx] hc (two * succ j) (succ j) ≐ succ (two * j) * hc (two * j) j := by
  have bt := natEq (binom_self' (Γ := Γ) (two * succ j))
  have bl := natEq (binom_self' (Γ := Γ) (two * j))
  have ds := natEq (df_succ (Γ := Γ) j)
  apply deriveNat; ipra_simps
  linear_combination 𝔟(df (succ j)) * bt + ds - (2 * 𝔟 j + 1) * 𝔟(df j) * bl

/-- `(m − k + 1) C(m + 1, k) = (m + 1) C(m, k)` for `k ≤ m`. -/
theorem binom_lower {k m : PTm n} (h : Γ ⊢[PRAAx] le k m) :
    Γ ⊢[PRAAx] succ (monus m k) * binom (succ m) k ≐ succ m * binom m k := by
  have h' : Γ ⊢[PRAAx] le k (succ m) := le_trans h (le_succ_self m)
  have e₀ := natEq (binom_eq h); have e₁ := natEq (binom_eq h')
  have f₁ := natEq (fact_succ (Γ := Γ) m zero)
  have f₃ := natEq ((congrAp2 factF (succ_monus_of_le h) (.eqRefl zero)).eqTrans
    (fact_succ (Γ := Γ) (monus m k) zero))
  refine mul_cancel (bden_pos m k) ?_
  apply deriveNat; ipra_simps
  linear_combination -𝔟(fact k) * 𝔟(binom (succ m) k) * f₃ - e₁ + f₁ + (𝔟 m + 1) * e₀

/-- `eq:hermite-derivative`, coefficientwise: `(m + 1 − 2j) c(m + 1, j) = (m + 1) c(m, j)` for
`2j ≤ m`. -/
theorem hc_deriv {m j : PTm n} (h : Γ ⊢[PRAAx] le (two * j) m) :
    Γ ⊢[PRAAx] succ (monus m (two * j)) * hc (succ m) j ≐ succ m * hc m j := by
  have b := natEq (binom_lower h)
  apply deriveNat; ipra_simps
  linear_combination 𝔟(df j) * b

/-- `cor:raw-moments`, the second form of the coefficient: `c(m, j) · 2^j j! (m − 2j)! = m!` for
`2j ≤ m`. -/
theorem hc_closed {m j : PTm n} (h : Γ ⊢[PRAAx] le (two * j) m) :
    Γ ⊢[PRAAx] hc m j * (pw two j * fact j * fact (monus m (two * j))) ≐ fact m := by
  have e := natEq (binom_eq h)
  have d := natEq (df_fact (Γ := Γ) j)
  apply deriveNat; ipra_simps
  linear_combination 𝔟(binom m (two * j)) * 𝔟(fact (monus m (two * j))) * d - e

end LeanProofs.IPRA.Probability.HermiteCoefficients
