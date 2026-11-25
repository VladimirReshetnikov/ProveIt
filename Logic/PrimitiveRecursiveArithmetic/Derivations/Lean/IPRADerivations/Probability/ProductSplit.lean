import IPRADerivations.Probability.ProductPower
import IPRADerivations.Foundations.MixedRadix
import IPRADerivations.Core.LinearCombination

/-!
# Splitting the iterated product law into a past and a future block

Packet: `probability/expected_value_ipra_2026-11-16`. In the `n`-fold product law of
`Probability/ProductPower` an `n`-tuple is the code `t = ∑_l i_l M^l < M^n` with digits
`dg_l(t) = ⌊t / M^l⌋ mod M`. Writing `t = i M^k + j` with `j < M^k`, the low block `j` carries the first `k`
coordinates and the high block `i` the remaining ones (the "past" and the "future" of the proof of
`thm:kolmogorov`):

* `dg_high`: `dg_{k+l}(i M^k + j) = dg_l(i)` for `j < M^k`;
* `high_congr`: the offset digits of the code are the digits of the high block;
* `pr_split`: `P_{k+m}(i M^k + j) = P_k(j) · P_m(i)`, the product weight factorizes;
* `sr_split`: `S_{k+m}(i M^k + j) = S_k(j) + S_m(i)`, the sample sum is the past sum plus the increment.

With `Core/BlockSum.block_sum` (`∑_{t < M^m M^k} g(t) = ∑_{i<M^m} ∑_{j<M^k} g(i M^k + j)`) this presents the
`(k + m)`-fold law as the product of the `k`-fold and the `m`-fold law.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductSplit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.BlockSum (qr_block)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Probability.ProductPower (dg div_eq' rem_lt'' dB_at low_congr Pr Sr wdB xdB)
open LeanProofs.IPRA.Foundations.MixedRadix (prod_split)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `dg_{k+l}(i M^k + j) = dg_l(i)` for `j < M^k`. -/
theorem dg_high {M i j k l : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] dg M (k + l) (i * pw M k + j) ≐ dg M l i := by
  have hl := pw_pos' hM l
  have hs : Γ ⊢[PRAAx] le (succ (rem i (pw M l))) (pw M l) := rem_lt'' hl i
  have hj' : Γ ⊢[PRAAx] le (succ j) (pw M k) := hj
  have pa := natEq (pw_add (Γ := Γ) M k l)
  have hb : Γ ⊢[PRAAx] lt (rem i (pw M l) * pw M k + j) (pw M (k + l)) := by
    show Γ ⊢[PRAAx] le (succ (rem i (pw M l) * pw M k + j)) (pw M (k + l))
    ipra_le sl hs * 𝔟 (pw M k) + sl hj' using rw [pa]; ring
  have q1 := Prf.andE₁ (qr_block (i := quo i (pw M l)) (j := rem i (pw M l) * pw M k + j) (pw_pos' hM (k + l)) hb)
  have eq : Γ ⊢[PRAAx] i * pw M k + j ≐ quo i (pw M l) * pw M (k + l) + (rem i (pw M l) * pw M k + j) := by
    ipra_lc 𝔟 (pw M k) * natEq (div_eq' (t := i) hl) - 𝔟 (quo i (pw M l)) * pa
  exact congrAp2 remF ((congrAp2 quoF eq (.eqRefl _)).eqTrans q1) (.eqRefl _)

/-- The offset digits of `i M^k + j` are the digits of `i`. -/
theorem high_congr (f : PTm 2) {M i j k m x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      (inst2 (offB (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f)) (var 0)
        (Syn.shift (pairT k (pairT (i * pw M k + j) (pairT M x)))) ≐
      inst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f) (var 0)
        (Syn.shift (pairT i (pairT M x))))) := by
  have hM' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have hj'' : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (pw (Syn.shift M) (Syn.shift k)) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  simp only [shift_pairT]
  rw [show Syn.shift (i * pw M k + j) = Syn.shift i * pw (Syn.shift M) (Syn.shift k) + Syn.shift j by
    simp [Syn.shift], inst2_offB]
  have c := congrInst2 (Syn.subst ![dg (fstT (sndT (var 1))) (var 0) (fstT (var 1)), sndT (sndT (var 1))] f)
    (congrAdd (fst_pair (Γ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) (Syn.shift k)
      (pairT (Syn.shift i * pw (Syn.shift M) (Syn.shift k) + Syn.shift j) (pairT (Syn.shift M) (Syn.shift x))))
      (.eqRefl (var 0)))
    (snd_pair (Syn.shift k)
      (pairT (Syn.shift i * pw (Syn.shift M) (Syn.shift k) + Syn.shift j) (pairT (Syn.shift M) (Syn.shift x))))
  refine c.eqTrans ((dB_at f _ _ _ _).eqTrans (.eqTrans ?_ (dB_at f _ _ _ _).eqSymm))
  exact congrInst2 f (dg_high hM'.wk hj''.wk) (.eqRefl _)

/-- `P_{k+m}(i M^k + j) = P_k(j) · P_m(i)` for `j < M^k`. -/
theorem pr_split (w : PTm 2) {M i j k m x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] Pr w (k + m) (i * pw M k + j) M x ≐ Pr w k j M x * Pr w m i M x := by
  refine (prod_split (wdB w) k m _).eqTrans (congrMul ?_ ?_)
  · exact prod_congr_bounded _ _ _ _ _ (low_congr w (a := i) hM)
  · exact prod_congr_bounded _ _ _ _ _ (high_congr w hM hj)

/-- `S_{k+m}(i M^k + j) = S_k(j) + S_m(i)` for `j < M^k`. -/
theorem sr_split (X : PTm 2) {M i j k m x : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hj : Γ ⊢[PRAAx] lt j (pw M k)) :
    Γ ⊢[PRAAx] Sr X (k + m) (i * pw M k + j) M x ≐ Sr X k j M x + Sr X m i M x := by
  refine (sum_split (xdB X) k m _).eqTrans (congrAdd ?_ ?_)
  · exact sum_congr_bounded _ _ _ _ _ (low_congr X (a := i) hM)
  · exact sum_congr_bounded _ _ _ _ _ (high_congr X hM hj)

end LeanProofs.IPRA.Probability.ProductSplit
