import IPRADerivations.Analysis.Pochhammer
import IPRADerivations.Core.LinearCombination

/-!
# The contiguous relations of the Gauss series, coefficientwise

Packet: `analysis/hypergeometric_ipra_2026-11-16`, `sections/09_contiguous.tex`, Theorem
`thm:contiguous-master` ("Seven expressions for `θF`"): "Every equality is a formal power-series
identity", proved by comparing coefficients: `(a + 1)_n / (a)_n = (a + n)/a`,
`(c)_n / (c − 1)_n = (c + n − 1)/(c − 1)`, and for the lowering relations "clearing `n (n + c − 1)`
reduces the assertion to a polynomial identity in `n, a, b, c`".

The coefficient of `z^n` in `₂F₁(a, b; c; z)` is `A_n = T_n(a, b) / ((c)_n n!)` with the numerator
`T_n(a, b) = (a)_n (b)_n`. Natural parameters; every relation is multiplied by the common denominator
and the subtracted terms are moved across.

* `Tn a b k = (a)_k (b)_k`; `Tn_succ`: `T_{k+1} = T_k (a + k)(b + k)`;
* `contig_a_plus` (`eq:contig-a+`): `a T_k(a + 1, b) = (a + k) T_k(a, b)`, i.e.
  `a (A_k(a+) − A_k) = k A_k`; `contig_b_plus` (`eq:contig-b+`) symmetric;
* `contig_c_minus` (`eq:contig-c-`): `c (c + 1)_k = (c + k) (c)_k`, i.e.
  `(c′ − 1)(A_k(c′ − 1) − A_k(c′)) = k A_k(c′)` at `c′ = c + 1`;
* `contig_a_minus` (`eq:contig-a-`), the coefficient of `z^{k+1}` in
  `(1 − z) θF = (c − a) F(a−) + (a − c + bz) F` at `a = α + 1`, multiplied by `(c)_{k+1} (k + 1)!`:
  `(k + 1 + c) T_{k+1}(α + 1, b) + (α + 1) T_{k+1}(α, b) =
   (k + b)(c + k)(k + 1) T_k(α + 1, b) + c T_{k+1}(α, b) + (α + 1) T_{k+1}(α + 1, b)`;
  `contig_b_minus` (`eq:contig-b-`) symmetric;
* `contig_c_plus` (`eq:contig-c+`), the coefficient of `z^{k+1}` in
  `z ((c − a)(c − b) F(c+) + c (a + b − c) F) = c (1 − z) θF`, multiplied by `(c)_{k+1} (k + 1)!` and
  divided by `c (k + 1)`:
  `(c² + ab) T_k + (a + b)(c + k) T_k + k (c + k) T_k = T_{k+1} + (a + b) c T_k + c (c + k) T_k`.

Lemma `lem:gauss-chain` ("Gauss difference chain", `f_{j-1} - f_j = α_j z f_{j+1}`), whose two parity cases
are the relation `F(a, b; c) - F(a + 1, b; c + 1) = ((a - c) b / (c (c + 1))) z F(a + 1, b + 1; c + 2)` at
shifted parameters (with `a` and `b` exchanged for even `j`):

* `gauss_chain`, the coefficient of `z^{k+1}` at `c = a + e`, multiplied by `c (c + 1)_{k+1} (k + 1)!`:
  `(c + 1 + k) T_{k+1}(a, b) + e b (k + 1) T_k(a + 1, b + 1) = c T_{k+1}(a + 1, b)`.

The first line `eq:contig-der` is `gauss_derivative` of `Analysis/Pochhammer`. The fifteen Gauss
relations follow by equating pairs of the seven expressions. The analytic reading (named functions on a
disk) is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.ContiguousRelations

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_succ poch_shift poch_shift')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The numerator `T_k(a, b) = (a)_k (b)_k` of the Gauss coefficient. -/
abbrev Tn (a b k : PTm n) : PTm n := poch a k * poch b k

/-- `T_{k+1} = T_k (a + k)(b + k)`. -/
theorem Tn_succ (a b k : PTm n) : Γ ⊢[PRAAx] Tn a b (succ k) ≐ Tn a b k * ((a + k) * (b + k)) := by
  ipra_lc 𝔟(poch b (succ k)) * natEq (poch_succ (Γ := Γ) a k) +
    𝔟(poch a k) * (𝔟 a + 𝔟 k) * natEq (poch_succ (Γ := Γ) b k)

/-- `eq:contig-a+`: `a T_k(a + 1, b) = (a + k) T_k(a, b)`. -/
theorem contig_a_plus (a b k : PTm n) : Γ ⊢[PRAAx] a * Tn (succ a) b k ≐ (a + k) * Tn a b k := by
  ipra_lc 𝔟(poch b k) * natEq (poch_shift (Γ := Γ) a k)

/-- `eq:contig-b+`: `b T_k(a, b + 1) = (b + k) T_k(a, b)`. -/
theorem contig_b_plus (a b k : PTm n) : Γ ⊢[PRAAx] b * Tn a (succ b) k ≐ (b + k) * Tn a b k := by
  ipra_lc 𝔟(poch a k) * natEq (poch_shift (Γ := Γ) b k)

/-- `eq:contig-c-`, the denominators: `c (c + 1)_k = (c + k) (c)_k`. -/
theorem contig_c_minus (c k : PTm n) : Γ ⊢[PRAAx] c * poch (succ c) k ≐ (c + k) * poch c k :=
  poch_shift c k

/-- `eq:contig-a-` at `a = α + 1`, the coefficient of `z^{k+1}` multiplied by `(c)_{k+1} (k + 1)!`. -/
theorem contig_a_minus (α b c k : PTm n) :
    Γ ⊢[PRAAx] (succ k + c) * Tn (succ α) b (succ k) + succ α * Tn α b (succ k) ≐
      (k + b) * (c + k) * succ k * Tn (succ α) b k + c * Tn α b (succ k) +
        succ α * Tn (succ α) b (succ k) := by
  ipra_lc (𝔟 k + 𝔟 c - 𝔟 α) * (𝔟(poch b (succ k)) * natEq (poch_succ (Γ := Γ) (succ α) k) + 𝔟(poch (succ α) k) * (𝔟 α + 1 + 𝔟 k) * natEq (poch_succ (Γ := Γ) b k)) +
    (𝔟 α + 1 - 𝔟 c) * (𝔟(poch b (succ k)) * natEq (poch_shift' (Γ := Γ) α k) + 𝔟 α * 𝔟(poch (succ α) k) * natEq (poch_succ (Γ := Γ) b k))

/-- `eq:contig-b-` at `b = β + 1`. -/
theorem contig_b_minus (a β c k : PTm n) :
    Γ ⊢[PRAAx] (succ k + c) * Tn a (succ β) (succ k) + succ β * Tn a β (succ k) ≐
      (k + a) * (c + k) * succ k * Tn a (succ β) k + c * Tn a β (succ k) +
        succ β * Tn a (succ β) (succ k) := by
  ipra_lc natEq (contig_a_minus (Γ := Γ) β a c k)

/-- `eq:contig-c+`, the coefficient of `z^{k+1}` multiplied by `(c)_{k+1} (k + 1)!` and divided by
`c (k + 1)`. -/
theorem contig_c_plus (a b c k : PTm n) :
    Γ ⊢[PRAAx] (c * c + a * b) * Tn a b k + (a + b) * (c + k) * Tn a b k + k * (c + k) * Tn a b k ≐
      Tn a b (succ k) + (a + b) * c * Tn a b k + c * (c + k) * Tn a b k := by
  ipra_lc -natEq (Tn_succ (Γ := Γ) a b k)

/-- `lem:gauss-chain`, coefficientwise: with `c = a + e`,
`(c + 1 + k) T_{k+1}(a, b) + e b (k + 1) T_k(a + 1, b + 1) = c T_{k+1}(a + 1, b)`. -/
theorem gauss_chain (a b e k : PTm n) :
    Γ ⊢[PRAAx] (a + e + succ k) * Tn a b (succ k) + e * b * succ k * Tn (succ a) (succ b) k ≐
      (a + e) * Tn (succ a) b (succ k) := by
  ipra_lc (𝔟 a + 𝔟 e + 1 + 𝔟 k) * (𝔟(poch b (succ k)) * natEq (poch_shift' (Γ := Γ) a k) + 𝔟 a * 𝔟(poch (succ a) k) * natEq (poch_shift' (Γ := Γ) b k)) -
    (𝔟 a + 𝔟 e) * (𝔟(poch b (succ k)) * natEq (poch_succ (Γ := Γ) (succ a) k) + 𝔟(poch (succ a) k) * (𝔟 a + 1 + 𝔟 k) * natEq (poch_shift' (Γ := Γ) b k))

end LeanProofs.IPRA.Analysis.ContiguousRelations
