import IPRADerivations.AnalyticNumberTheory.BlockInstance
import IPRADerivations.Core.LinearCombination

/-!
# The one-step contraction, raw form (`pnt_ipra_constructive_2026-11-14`, Lemma `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"By Lemma con:deficit, `∫_0^t (t − u)|r(u)| du ≤ at²/2 + 4st − b (t/2) (1/(64q²))` … Substitution in
(con:weighted) gives `|r(t)| ≤ a − 4δ + (8s + S)/t`."

Discretely (`u_m` the harmonic logarithm, `F = L!`, `R(m) = ψ(m) − Fm`, stage bound `D|R(m)| ≤ AFm` for
`Y ≤ m ≤ x`, divisors `d ≤ N = M + 1` with `NY ≤ x`):

* `deficit_growth`: the weighted sum `Σ_d 2F u_d |R(⌊x/d⌋)|` together with the weighted deficit on any sub-block
  `E₀ < d ≤ E₁` of `(0, N]` is bounded by the head and tail baselines (`HeadDeficit.head_deficit`,
  `ContractionSplit.tail_bound`; the other deficit pieces are dropped, being nonnegative);
* `one_step_raw`: with the chain bound `BlockInstance.chain_deficit` on `E_k = E₀ 2^{2hk}` and the weighted
  Selberg sum `WeightedAbel.weighted_sum`,

  `24D² |ψ(x) − Fx| u_x² + 3A²F² x B u_{E₀} + 96 D² F x u_N²
     ≤ 24 D A F x (u_N² + 2F²) + 96 D² F x (u_x² + 2F²) + 100 A D F² B u_{N'} (N' + ⌊x/E₀⌋)
       + 24 D² (19222 F² x u_x + 11070 F³ x)`.

The left term `3A²F²xB u_{E₀}` is the deficit gain of the `B` blocks; the rest of the contraction is arithmetic on
harmonic logarithms.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.OneStepRaw

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (OnBlock stg)
open LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit (hgB head_deficit)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockFamily (Lay hg_split)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockInstance (chain_deficit)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (wbB Stage tail_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedAbel (weighted_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB qB)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Head and tail baselines, keeping the weighted deficit of one sub-block `E₀ < d ≤ E₁` of `(0, M + 1]`. -/
theorem deficit_growth {M x K L Ds A Y E0 E1 : PTm n} (hK : Γ ⊢[PRAAx] le one K)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hst : Γ ⊢[PRAAx] Stage x Y Ds A K L)
    (hE : Γ ⊢[PRAAx] le E0 E1) (hE1 : Γ ⊢[PRAAx] le E1 (succ M)) :
    Γ ⊢[PRAAx] le (Ds * ap2 (sumF wbB) (succ x) (pairT x (pairT K (fact L))) +
        two * fact L * ap2 (sumF hgB) (succ x) (Lay x E0 E1 A Ds K L) +
        num 4 * Ds * (fact L * x) * (U (succ M) K (fact L) * U (succ M) K (fact L)))
      (A * (fact L * (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L)))) +
        num 4 * Ds * (fact L * x) * (U x K (fact L) * U x K (fact L) + two * (fact L * fact L))) := by
  have hL : Γ ⊢[PRAAx] le (K * succ M) L := le_trans (le_scale K hMx) hKx
  have hd := head_deficit hK hL hY hMx hst
  have t := le_scale Ds (tail_bound hK hP hKx hMx)
  have ex : Γ ⊢[PRAAx] succ x ≐ succ (succ M) + monus x (succ M) := by
    ipra_lc natEq (eq_add_of_le hMx)
  have sp := natEq ((congrAp2 (sumF wbB) ex (.eqRefl _)).eqTrans
    (sum_split (Γ := Γ) wbB (succ (succ M)) (monus x (succ M)) (pairT x (pairT K (fact L)))))
  have e1 := natEq (hg_split (Γ := Γ) (x := x) (A := A) (Ds := Ds) (K := K) (L := L) (zero_le E0) (le_trans hE hE1))
  have e2 := natEq (hg_split (Γ := Γ) (x := x) (A := A) (Ds := Ds) (K := K) (L := L) hE hE1)
  ipra_le sl hd + sl t + 2 * 𝔞 (fact L) * (𝔞 (ap2 (sumF hgB) (succ x) (Lay x zero E0 A Ds K L)) +
      𝔞 (ap2 (sumF hgB) (succ x) (Lay x E1 (succ M) A Ds K L))) with
    𝔞 Ds * sp - 2 * 𝔞 (fact L) * (e1 + e2)

/-- The one-step contraction before the arithmetic on harmonic logarithms. -/
theorem one_step_raw {M x K L Ds A Y E0 h B N H0 : PTm n} (hx : Γ ⊢[PRAAx] le one x)
    (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) (hL4 : Γ ⊢[PRAAx] le (K * Q4 x) L)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hst : Γ ⊢[PRAAx] Stage x Y Ds A K L)
    (hE0 : Γ ⊢[PRAAx] le one E0) (hBN : Γ ⊢[PRAAx] le (E0 * pw (pw two (h + h)) B) N)
    (hNM : Γ ⊢[PRAAx] le N (succ M)) (hxL : Γ ⊢[PRAAx] le x L) (hxK : Γ ⊢[PRAAx] le x K)
    (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hh : Γ ⊢[PRAAx] le (two * H0 + one) h) (hF : Γ ⊢[PRAAx] le (two * x) (fact L))
    (hon : Γ ⊢[PRAAx] OnBlock x E0 N (stg x A Ds K L)) :
    Γ ⊢[PRAAx] le (num 24 * (Ds * Ds) * absd (inst2 psiB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L))
          (inst2 qB x (pairT K (fact L)) * U x K (fact L) * U x K (fact L)) +
        num 3 * (A * A) * (fact L * fact L) * x * (B * U E0 K (fact L)) +
        num 96 * (Ds * Ds) * (fact L * x) * (U (succ M) K (fact L) * U (succ M) K (fact L)))
      (num 24 * Ds * (A * (fact L * (x * (U (succ M) K (fact L) * U (succ M) K (fact L) + two * (fact L * fact L))))) +
        num 96 * (Ds * Ds) * (fact L * x) * (U x K (fact L) * U x K (fact L) + two * (fact L * fact L)) +
        num 100 * (A * Ds) * (fact L * fact L) * (B * U N K (fact L)) * (N + quo x E0) +
        num 24 * (Ds * Ds) * (num 19222 * (fact L * fact L * (x * U x K (fact L))) +
          num 11070 * (fact L * fact L * fact L * x))) := by
  have hBM := le_trans hBN hNM
  have hNx := le_trans hNM hMx
  have g := deficit_growth (E0 := E0) (E1 := E0 * pw (pw two (h + h)) B) hK hP hKx hMx hY hst
    (BlockChain.e0_le (BlockChain.one_le_pw' (le_succ_self one) _) B) hBM
  have c := chain_deficit hE0 hBN hNx hxL hK hxK hNN hKx hP hA1 hA4 hH0 hh hF hon
  have w := weighted_sum hx hK hx4 hL4 hP
  ipra_le 24 * 𝔞 Ds * sl g + 𝔞 (fact L) * sl c + 24 * 𝔞 Ds * 𝔞 Ds * sl w

end LeanProofs.IPRA.AnalyticNumberTheory.OneStepRaw
