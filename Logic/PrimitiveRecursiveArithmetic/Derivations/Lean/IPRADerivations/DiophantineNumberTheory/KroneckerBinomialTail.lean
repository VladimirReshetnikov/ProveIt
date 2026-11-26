import IPRADerivations.DiophantineNumberTheory.KroneckerKernel
import IPRADerivations.Combinatorics.BinomialTwo
import IPRADerivations.Core.Header

/-!
# The binomial tail of the Kronecker kernel

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`, Theorem `thm:kronecker`, the "complete rational estimate"
before `eq:kernel-tail`: with `δ = t^{−2}`,
"`(1 − δ)^r ≤ (1 + δ)^{−r} ≤ (C(r, k) δ^k)^{−1}`". Cleared of denominators with `T = t² = T' + 1`:

* `binom_term`: one term of the binomial theorem is at most the whole sum,
  `C(M, k) X^k Y^{M−k} ≤ (X + Y)^M` for `k ≤ M` (`BinomialTwo.binomial_two`, `term_le_sum`);
* `binom_tail`: `(T − 1)^r C(r, k) ≤ T^k T^r` for `k ≤ r`, i.e. `(1 − δ)^r ≤ 1/(C(r, k) δ^k)`. The proof is the
  packet's: `(T − 1)^r (T + 1)^r = (T² − 1)^r ≤ T^{2r}` and `C(r, k) T^{r−k} ≤ (1 + T)^r`, then the factor
  `T^{r−k} ≥ 1` cancels.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerBinomialTail

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound (mul_pw)
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (one_le_pw_of cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (bt S bt_at binomial_two)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- One term of the binomial theorem: `C(M, k) X^k Y^{M−k} ≤ (X + Y)^M` for `k ≤ M`. -/
theorem binom_term {k M : PTm n} (X Y : PTm n) (hk : Γ ⊢[PRAAx] le k M) :
    Γ ⊢[PRAAx] le (gb M k * pw X k * pw Y (monus M k)) (pw (X + Y) M) := by
  have hl : Γ ⊢[PRAAx] lt k (succ M) := (by ipra_le sl hk : Γ ⊢[PRAAx] le (succ k) (succ M))
  exact le_congr (bt_at k M X Y) (binomial_two M X Y) (term_le_sum bt (x := pairT M (pairT X Y)) hl)

/-- `(T − 1)^r C(r, k) ≤ T^k T^r` for `T = T' + 1` and `k ≤ r`: `(1 − δ)^r ≤ 1/(C(r, k) δ^k)`. -/
theorem binom_tail {T' r k : PTm n} (hk : Γ ⊢[PRAAx] le k r) :
    Γ ⊢[PRAAx] le (pw T' r * gb r k) (pw (succ T') k * pw (succ T') r) := by
  have t := binom_term one (succ T') hk
  have hq : Γ ⊢[PRAAx] le (T' * (one + succ T')) (succ T' * succ T') := by ipra_le 1
  have m := pw_le_pw r hq
  have p1 := natEq (pw_one_base (Γ := Γ) k)
  have e1 := natEq (mul_pw (Γ := Γ) T' (one + succ T') r)
  have e2 := natEq (mul_pw (Γ := Γ) (succ T') (succ T') r)
  have e3 := natEq ((congrPw (.eqRefl (succ T')) (eq_add_of_le hk)).eqTrans (pw_add (succ T') k (monus r k)) :
    Γ ⊢[PRAAx] pw (succ T') r ≐ pw (succ T') k * pw (succ T') (monus r k))
  have hE := one_le_pw_of (Γ := Γ) (monus r k) (show Γ ⊢[PRAAx] le one (succ T') by ipra_le 𝔟 T')
  refine cancel_pos hE ?_
  ipra_le sl m + 𝔟 (pw T' r) * sl t using
    simp only [e1, e2, p1, e3]
    ring

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerBinomialTail
