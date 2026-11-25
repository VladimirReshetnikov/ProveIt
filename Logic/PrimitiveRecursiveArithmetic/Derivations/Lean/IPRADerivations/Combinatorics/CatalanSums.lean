import IPRADerivations.Combinatorics.CatalanConvolution
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.LinearCombination

/-!
# The weighted Catalan convolution

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Weighted convolution", (2.16)):
`n Cat_n = ∑_{k<n} Cat_{n−k−1} C(2k + 1, k + 1)` for `n ≥ 1`, stated with `n = m + 1`. The packet's
proof is followed: `C(2k + 1, k + 1) = (2k + 1) Cat_k`, and with `S = ∑ k Cat_k Cat_{m−k}`,
`2S = m Cat_{m+1}` by reflecting the sum and Segner's recurrence.

* `binom_odd_symm`: `C(2k + 1, k + 1) = C(2k + 1, k)`;
* `odd_sum`: `∑_{k ≤ m} (2k + 1) Cat_k Cat_{m−k} = (m + 1) Cat_{m+1}`;
* `weighted_convolution`: `∑_{k ≤ m} Cat_{m−k} C(2k + 1, k + 1) = (m + 1) Cat_{m+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanSums

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.Catalan (cat cat_odd_binom)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution
  (congrCat convB wB inst2_conv inst2_w conv_symm segner)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## A binomial symmetry -/

/-- `C(2k + 1, k + 1) = C(2k + 1, k)`. -/
theorem binom_odd_symm (k : PTm n) :
    Γ ⊢[PRAAx] binom (succ (two * k)) (succ k) ≐ binom (succ (two * k)) k := by
  have hN : Γ ⊢[PRAAx] succ (two * k) ≐ k + succ k := by ipra_ring
  have hN' : Γ ⊢[PRAAx] succ (two * k) ≐ succ k + k := by ipra_ring
  have l₁ : Γ ⊢[PRAAx] le (succ k) (succ (two * k)) := le_of_eq_add hN'
  have l₀ : Γ ⊢[PRAAx] le k (succ (two * k)) := le_of_eq_add hN
  have g₁ : Γ ⊢[PRAAx] fact (monus (succ (two * k)) (succ k)) ≐ fact k :=
    congrAp2 factF ((congrMonus hN' (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  have g₀ : Γ ⊢[PRAAx] fact (monus (succ (two * k)) k) ≐ fact (succ k) :=
    congrAp2 factF ((congrMonus hN (.eqRefl _)).eqTrans (add_monus' _ _)) (.eqRefl _)
  refine mul_cancel (D := fact k * fact (succ k)) (pos_mul' (fact_pos _) (fact_pos _)) ?_
  ipra_lc -natEq (binom_eq l₁) + natEq (binom_eq l₀) -
    𝔞(fact (succ k)) * 𝔞(binom (succ (two * k)) (succ k)) * natEq g₁ +
    𝔞(fact k) * 𝔞(binom (succ (two * k)) k) * natEq g₀

/-! ## The odd-weighted convolution; variables `0 = i`, `1 = m` -/

/-- `(2i + 1) Cat_i Cat_{m−i}`. -/
abbrev oddB : PTm 2 := succ (two * var 0) * convB
/-- `2 i Cat_i Cat_{m−i}`. -/
abbrev twoW : PTm 2 := two * wB
/-- `Cat_{m−i} C(2i + 1, i + 1)`. -/
abbrev bwB : PTm 2 := cat (monus (var 1) (var 0)) * binom (succ (two * var 0)) (succ (var 0))

theorem inst2_odd (i m : PTm n) : inst2 oddB i m = succ (two * i) * (cat i * cat (monus m i)) := by
  simp [inst2]
theorem inst2_twoW (i m : PTm n) : inst2 twoW i m = two * inst2 wB i m := by simp [inst2]
theorem inst2_bw (i m : PTm n) :
    inst2 bwB i m = cat (monus m i) * binom (succ (two * i)) (succ i) := by simp [inst2]

theorem odd_pt (i m : PTm n) : Γ ⊢[PRAAx] inst2 oddB i m ≐ inst2 (addBody twoW convB) i m := by
  rw [inst2_addBody, inst2_twoW, inst2_odd, inst2_w, inst2_conv]
  ipra_ring

/-- `∑_{k ≤ m} (2k + 1) Cat_k Cat_{m−k} = (m + 1) Cat_{m+1}`. -/
theorem odd_sum (m : PTm n) : Γ ⊢[PRAAx] ap2 (sumF oddB) (succ m) m ≐ succ m * cat (succ m) := by
  have c := natEq (sum_congr_bounded (Γ := Γ) oddB (addBody twoW convB) m m (succ m)
    (.allI (.impI (odd_pt _ _))))
  have a := natEq (sum_add (Γ := Γ) twoW convB (succ m) m)
  have s' : Γ ⊢[PRAAx] ap2 (sumF twoW) (succ m) m ≐ two * ap2 (sumF wB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    rw [inst2_twoW]
    exact .eqRefl _
  have s := natEq s'
  have y := natEq (conv_symm (Γ := Γ) m); have g := natEq (segner (Γ := Γ) m)
  apply deriveNat; ipra_simps
  linear_combination c + a + s + y + (𝔞(m) + 1) * g

theorem bw_pt (i m : PTm n) : Γ ⊢[PRAAx] inst2 bwB i m ≐ inst2 oddB i m := by
  rw [inst2_bw, inst2_odd]
  ipra_lc 𝔞(cat (monus m i)) * natEq (binom_odd_symm (Γ := Γ) i) -
    𝔞(cat (monus m i)) * natEq (cat_odd_binom (Γ := Γ) i)

/-- (2.16): `∑_{k ≤ m} Cat_{m−k} C(2k + 1, k + 1) = (m + 1) Cat_{m+1}`. -/
theorem weighted_convolution (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF bwB) (succ m) m ≐ succ m * cat (succ m) :=
  (sum_congr_bounded bwB oddB m m (succ m) (.allI (.impI (bw_pt _ _)))).eqTrans (odd_sum m)

end LeanProofs.IPRA.Combinatorics.CatalanSums
