import IPRADerivations.AnalyticNumberTheory.MobiusFloor
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# The recursion of the Mertens function

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`, `thm:floor-recurrence`, second identity:
`M(N) = 1 − ∑_{a=2}^{N} M(⌊N/a⌋)` for `N ≥ 1`.

With `M = M⁺ − M⁻` (`MobiusFloor.MP`, `MN`) and the sums over `2 ≤ a ≤ N` written as offset sums
(`Core/SumSplit.offB`, index `a = 2 + j`, `j < N − 1`), the identity is

    M⁺(N) + ∑_{2 ≤ a ≤ N} M⁺(⌊N/a⌋) = 1 + M⁻(N) + ∑_{2 ≤ a ≤ N} M⁻(⌊N/a⌋).

* `head2`: `∑_{a<2} G(a) = G(0) + G(1)`;
* `gP_zero`, `gP_one`, `gN_zero`, `gN_one`: the terms `a = 0` (zero) and `a = 1` (`M^±(N)`) of the floor sums;
* `peel`: `∑_{a ≤ N} G(a) = (G(0) + G(1)) + ∑_{2 ≤ a ≤ N} G(a)` for `N ≥ 1`;
* **`mertens_recursion`**: the identity above, from `MobiusFloor.mertens_floor`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MertensRecursion

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (MP MN GPB GNB inst2_GPB inst2_GNB mertens_floor)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `∑_{a<2} G(a) = G(0) + G(1)`. -/
theorem head2 (G : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF G) two x ≐ inst2 G zero x + inst2 G one x :=
  sum_two_terms G x

theorem gP_zero (x : PTm n) : Γ ⊢[PRAAx] inst2 GPB zero x ≐ zero := by
  rw [inst2_GPB]; exact zero_mul_l sg_zero _

theorem gN_zero (x : PTm n) : Γ ⊢[PRAAx] inst2 GNB zero x ≐ zero := by
  rw [inst2_GNB]; exact zero_mul_l sg_zero _

theorem gP_one (x : PTm n) : Γ ⊢[PRAAx] inst2 GPB one x ≐ MP x := by
  rw [inst2_GPB]
  have s1 : Γ ⊢[PRAAx] sg (one : PTm n) ≐ one := sg_succ _
  exact (congrMul s1 (congrAp2 _ (RSA.quo_one x) (.eqRefl _))).eqTrans (one_mul _)

theorem gN_one (x : PTm n) : Γ ⊢[PRAAx] inst2 GNB one x ≐ MN x := by
  rw [inst2_GNB]
  have s1 : Γ ⊢[PRAAx] sg (one : PTm n) ≐ one := sg_succ _
  exact (congrMul s1 (congrAp2 _ (RSA.quo_one x) (.eqRefl _))).eqTrans (one_mul _)

theorem succ_split {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) : Γ ⊢[PRAAx] succ x ≐ two + pred x := by
  ipra_lc natEq hx

/-- `∑_{a ≤ x} G(a) = (G(0) + G(1)) + ∑_{2 ≤ a ≤ x} G(a)` for `x ≥ 1`. -/
theorem peel (G : PTm 2) {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ ⊢[PRAAx] ap2 (sumF G) (succ x) x ≐
      (inst2 G zero x + inst2 G one x) + ap2 (sumF (offB G)) (pred x) (pairT two x) :=
  (congrAp2 _ (succ_split hx) (.eqRefl _)).eqTrans
    ((sum_split G two (pred x) x).eqTrans (congrAdd (head2 G x) (.eqRefl _)))

/-- **`thm:floor-recurrence`, second identity**: for `x ≥ 1`,
`M⁺(x) + ∑_{2 ≤ a ≤ x} M⁺(⌊x/a⌋) = 1 + (M⁻(x) + ∑_{2 ≤ a ≤ x} M⁻(⌊x/a⌋))`. -/
theorem mertens_recursion {x : PTm n} (hx : Γ ⊢[PRAAx] x ≐ succ (pred x)) :
    Γ ⊢[PRAAx] MP x + ap2 (sumF (offB GPB)) (pred x) (pairT two x) ≐
      one + (MN x + ap2 (sumF (offB GNB)) (pred x) (pairT two x)) := by
  have eP : Γ ⊢[PRAAx] ap2 (sumF GPB) (succ x) x ≐ MP x + ap2 (sumF (offB GPB)) (pred x) (pairT two x) :=
    (peel GPB hx).eqTrans (congrAdd ((congrAdd (gP_zero x) (gP_one x)).eqTrans (zero_add _)) (.eqRefl _))
  have eN : Γ ⊢[PRAAx] ap2 (sumF GNB) (succ x) x ≐ MN x + ap2 (sumF (offB GNB)) (pred x) (pairT two x) :=
    (peel GNB hx).eqTrans (congrAdd ((congrAdd (gN_zero x) (gN_one x)).eqTrans (zero_add _)) (.eqRefl _))
  exact eP.eqSymm.eqTrans ((mertens_floor x).eqTrans (congrAdd (sg_pos hx) eN))

end LeanProofs.IPRA.AnalyticNumberTheory.MertensRecursion
