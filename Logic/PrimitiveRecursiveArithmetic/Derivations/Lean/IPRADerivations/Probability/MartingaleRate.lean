import IPRADerivations.Probability.ConditionalAveraging
import IPRADerivations.Probability.ClipLaws

/-!
# The martingale rate of conditional averaging

Packet: `probability/ipra_probability_2026-11-20`, `paper/sections/foundation.tex`, Theorem "Conditional averaging
and a quantified martingale limit": "If `n ≥ ℓ(k)`, then `C_n x_k = x_k`. Hence
`‖C_n X − X‖₁ ≤ ‖C_n(X − x_k)‖₁ + ‖x_k − X‖₁ ≤ 2‖X − x_k‖₁ ≤ 2ε_k`."

In the block-cleared form of `ConditionalAveraging` (fine cells `j < m` with weights `W_j`, the parent map `p`, the
coarse masses `C_i = Σ_{p j = i} W_j`, and `blk p W f i = C_i (C f)_i`), the conditional average of `X` at a fine cell
`j` is `blk X (p j) / C_{p j}`. Multiplying the cell `j` by its block mass `C_{p j}`:

* `rate_pt`: `|blk X i − C_i X_j| ≤ |blk X i − blk x i| + C_i |x'_i − X_j|` for an `F`-measurable `x = x' ∘ p`
  (`C x = x`, `ConditionalAveraging.cond_measurable`), by the triangle inequality;
* `martingale_rate`: `Σ_j W_j |blk X (p j) − C_{p j} X_j| ≤ 2 Σ_j C_{p j} W_j |X_j − x'(p j)|`, i.e.
  `‖C X − X‖₁ ≤ 2 ‖X − x‖₁` with each block weighted by its mass: the first term is the `d₁` contraction
  `blk_contract` regrouped over the blocks, the second is `‖x − X‖₁` directly.

For the dyadic filtration (`p` the first-`n`-bit prefix) and a regular name `x_k` depending on `ℓ(k) ≤ n` bits,
this is the stated rate `‖C_n X − X‖₁ ≤ 2ε_k`.
-/

namespace LeanProofs.IPRA.Probability.MartingaleRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul)
open LeanProofs.IPRA.Probability.ClipLaws (ad_triangle)
open LeanProofs.IPRA.Probability.ConditionalAveraging
  (blk cond_measurable blk_contract nsum_mono toG_ite regroup_defining)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {n k m : ℕ} {Γ : List (Fm PTm n)}

theorem congr_ad {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' :=
  congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁)

theorem ad_symm (a b : PTm n) : Γ ⊢[PRAAx] ad a b ≐ ad b a := add_comm _ _

section Rate

variable (p : Fin m → Fin k) (W X : Fin m → PTm n) (C x : Fin k → PTm n)

/-- `|blk X i − C_i X_j| ≤ |blk X i − blk x i| + C_i |x_i − X_j|` for a measurable `x`. -/
theorem rate_pt (hm : ∀ i, Γ ⊢[PRAAx] (nsum fun j => if p j = i then W j else zero) ≐ C i) (i : Fin k) (Xj : PTm n) :
    Γ ⊢[PRAAx] le (ad (blk p W X i) (C i * Xj))
      (ad (blk p W X i) (blk p W (fun j => x (p j)) i) + C i * ad (x i) Xj) := by
  have t := ad_triangle (Γ := Γ) (blk p W X i) (blk p W (fun j => x (p j)) i) (C i * Xj)
  have e : Γ ⊢[PRAAx] ad (blk p W (fun j => x (p j)) i) (C i * Xj) ≐ C i * ad (x i) Xj :=
    (congr_ad (cond_measurable p W C x hm i) (.eqRefl _)).eqTrans (ad_mul _ _ _)
  exact le_congr (.eqRefl _) (congrAdd (.eqRefl _) e) t

/-- The martingale rate `‖C X − X‖₁ ≤ 2 ‖X − x‖₁` (block-cleared) for a measurable `x = x' ∘ p`. -/
theorem martingale_rate (hm : ∀ i, Γ ⊢[PRAAx] (nsum fun j => if p j = i then W j else zero) ≐ C i) :
    Γ ⊢[PRAAx] le (nsum fun j => W j * ad (blk p W X (p j)) (C (p j) * X j))
      (two * nsum fun j => C (p j) * (W j * ad (X j) (x (p j)))) := by
  -- the block distance `A_i = |blk X i − blk x i|`
  let A : Fin k → PTm n := fun i => ad (blk p W X i) (blk p W (fun j => x (p j)) i)
  -- pointwise, weighted by `W_j`
  have h1 : Γ ⊢[PRAAx] le (nsum fun j => W j * ad (blk p W X (p j)) (C (p j) * X j))
      (nsum fun j => W j * (A (p j) + C (p j) * ad (x (p j)) (X j))) :=
    nsum_mono fun j => le_mul_mono (le_refl (W j)) (rate_pt p W X C x hm (p j) (X j))
  -- `Σ_j W_j A_{p j} = Σ_i A_i C_i ≤ Σ_i C_i Σ_{p j = i} W_j |X_j − x_j| = Σ_j C_{p j} W_j |X_j − x_j|`
  have hC : ∀ i, Γ ⊢[PRAAx] le (C i * A i)
      (C i * nsum fun j => if p j = i then W j * ad (X j) (x (p j)) else zero) :=
    fun i => le_mul_mono (le_refl _) (blk_contract p W X (fun j => x (p j)) i)
  have h2 := nsum_mono (Γ := Γ) hC
  have r1 : Γ ⊢[PRAAx] (nsum fun j => A (p j) * W j) ≐ nsum fun i => C i * A i := by
    have hm' : ∀ i, (∑ j, if p j = i then Groth.ι (Q.mk Γ (W j)) else 0) = Groth.ι (Q.mk Γ (C i)) := by
      intro i
      have e := natEq (hm i)
      rw [toG_nsum] at e
      rw [← e]
      exact Finset.sum_congr rfl fun j _ => by rw [toG_ite]
    apply deriveNat
    simp only [toG_nsum, Q.mk_mul, map_mul]
    rw [regroup_defining p (fun i => Groth.ι (Q.mk Γ (A i))) (fun j => Groth.ι (Q.mk Γ (W j)))]
    exact Finset.sum_congr rfl fun i _ => by rw [hm' i, _root_.mul_comm]
  have r2 : Γ ⊢[PRAAx] (nsum fun i => C i * nsum fun j => if p j = i then W j * ad (X j) (x (p j)) else zero) ≐
      nsum fun j => C (p j) * (W j * ad (X j) (x (p j))) := by
    apply deriveNat
    simp only [toG_nsum, toG_ite, Q.mk_mul, map_mul]
    exact (regroup_defining p (fun i => Groth.ι (Q.mk Γ (C i)))
      (fun j => Groth.ι (Q.mk Γ (W j)) * Groth.ι (Q.mk Γ (ad (X j) (x (p j)))))).symm
  -- the second term, `|x_{p j} − X_j| = |X_j − x_{p j}|`
  have r3 : Γ ⊢[PRAAx] (nsum fun j => W j * (A (p j) + C (p j) * ad (x (p j)) (X j))) ≐
      (nsum fun j => A (p j) * W j) + nsum fun j => C (p j) * (W j * ad (X j) (x (p j))) := by
    have e : ∀ j, Γ ⊢[PRAAx] W j * (A (p j) + C (p j) * ad (x (p j)) (X j)) ≐
        A (p j) * W j + C (p j) * (W j * ad (X j) (x (p j))) := fun j =>
      (congrMul (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (ad_symm _ _)))).eqTrans
        (by apply deriveNat; ipra_simps; ring)
    have ee : ∀ j, Groth.ι (Q.mk Γ (W j * (A (p j) + C (p j) * ad (x (p j)) (X j)))) =
        Groth.ι (Q.mk Γ (A (p j) * W j)) + Groth.ι (Q.mk Γ (C (p j) * (W j * ad (X j) (x (p j))))) := fun j => by
      rw [natEq (e j), Q.mk_add, map_add]
    apply deriveNat
    rw [Q.mk_add, map_add, toG_nsum, toG_nsum, toG_nsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => ee j
  have h12 := le_congr (.eqRefl _) r3 h1
  have h3 : Γ ⊢[PRAAx] le ((nsum fun j => A (p j) * W j) + nsum fun j => C (p j) * (W j * ad (X j) (x (p j))))
      (two * nsum fun j => C (p j) * (W j * ad (X j) (x (p j)))) := by
    have b := le_congr r1.eqSymm r2 h2
    refine le_congr (.eqRefl _) ?_ (LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz.add_le_add b (le_refl _))
    apply deriveNat; ipra_simps; ring
  exact le_trans h12 h3

end Rate

end LeanProofs.IPRA.Probability.MartingaleRate
