import IPRADerivations.AnalyticNumberTheory.SummatoryCompose
import IPRADerivations.Core.LinearCombination

/-!
# Reordering the double sum of the weighted identity (`pnt_ipra_constructive_2026-11-14`, `sb:weighted-sum`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:weighted-sum`:
"use the same equation at `x/n`", which produces `Σ_n Λ(n) Σ_{b≤x/n} Λ(b) R(x/(nb)) = Σ_{ab≤x} Λ(a)Λ(b) R(x/(ab))`.
For any monotone body `f` with `f(0) = 0` and any two coefficient bodies `a`, `b`:

  `Σ_{1≤k≤x} a(k) Σ_{1≤j≤⌊x/k⌋} b(j) f(⌊⌊x/k⌋/j⌋) = Σ_{1≤n≤x} (a * b)(n) f(⌊x/n⌋)`.

* `S1B`, `S1_eq`: the inner sum `H(m) = Σ_{j≤m} b(j) f(⌊m/j⌋)` is the summatory function of `b * Δf`
  (`SummatoryCompose.compose`);
* `S1_mono`, `S1_zero`, `dS1`: so `H` is monotone, `H(0) = 0` and `ΔH = b * Δf` pointwise;
* `conv_congr2`: convolution respects a pointwise equation of its second body;
* `reorder`: the displayed identity, by `compose` for `H`, `ΔH = b * Δf`, `ConvolutionAssoc.conv_assoc` and `compose`
  for `f` with the coefficient `a * b`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.WeightedReorder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (dH inst2_dH Mono hRB inst2_hRB compose)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (conv_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF conv_assoc)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Convolution respects a schematic pointwise equation of the second body. -/
theorem conv_congr2 (a b b' : PTm 2)
    (h : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (i y : PTm m), Δ ⊢[PRAAx] inst2 b i y ≐ inst2 b' i y) (N y : PTm n) :
    Γ ⊢[PRAAx] conv a b N y ≐ conv a b' N y := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cvB, inst2_cvB]
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (h _ _))

section Reorder

variable (f b : PTm 2) (hm : Mono f) (h0 : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m), Δ ⊢[PRAAx] inst2 f zero y ≐ zero)
include hm h0

/-- `H(m) = Σ_{1≤j≤m} b(j) f(⌊m/j⌋)`. -/
abbrev S1B : PTm 2 := ap2 (sumF (hRB f b)) (succ (var 0)) (pairT (var 0) (var 1))

omit hm h0 in
theorem inst2_S1 (m y : PTm n) : inst2 (S1B f b) m y = ap2 (sumF (hRB f b)) (succ m) (pairT m y) := by
  simp [inst2]

/-- `H(m) = Σ_{i≤m} (b * Δf)(i)`. -/
theorem S1_eq (m y : PTm n) :
    Γ ⊢[PRAAx] inst2 (S1B f b) m y ≐ ap2 (sumF (cvF b (dH f))) (succ m) y := by
  rw [inst2_S1]; exact compose f b hm h0 m y

theorem S1_mono : Mono (S1B f b) := by
  unfold Mono; intro m Δ k y
  have a := natEq (S1_eq (Γ := Δ) f b hm h0 k y)
  have c := natEq (S1_eq (Γ := Δ) f b hm h0 (succ k) y)
  have s := natEq (sum_succ' (Γ := Δ) (cvF b (dH f)) (succ k) y)
  ipra_le 𝔞 (inst2 (cvF b (dH f)) (succ k) y) with c + s - a

theorem S1_zero {m : ℕ} {Δ : List (Fm PTm m)} (y : PTm m) : Δ ⊢[PRAAx] inst2 (S1B f b) zero y ≐ zero := by
  refine (S1_eq f b hm h0 zero y).eqTrans ((sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (.eqRefl _)).eqTrans
    ((zero_add _).eqTrans ?_)))
  rw [inst2_cvF]; exact conv_zero _ _ _

/-- `ΔH = b * Δf` at every argument. -/
theorem dS1 {m : ℕ} {Δ : List (Fm PTm m)} (i y : PTm m) :
    Δ ⊢[PRAAx] inst2 (dH (S1B f b)) i y ≐ inst2 (cvF b (dH f)) i y := by
  rw [inst2_dH]
  refine .orE (zero_or_succ i) ?_ ?_
  · let C := (i ≐ zero) :: Δ
    have hi : C ⊢[PRAAx] i ≐ zero := Prf.hyp0
    have z0 : C ⊢[PRAAx] inst2 (S1B f b) i y ≐ zero := (congrInst2 _ hi (.eqRefl _)).eqTrans (S1_zero f b hm h0 y)
    have g0 : C ⊢[PRAAx] inst2 (cvF b (dH f)) i y ≐ zero := by
      rw [inst2_cvF]
      exact (congrAp2 _ (congrSucc hi) (congrPairT hi (.eqRefl _))).eqTrans (conv_zero _ _ _)
    exact ((congrMonus z0 (.eqRefl _)).eqTrans (zero_monus _)).eqTrans g0.eqSymm
  · let C := (i ≐ succ (pred i)) :: Δ
    have hi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp0
    have mi : C ⊢[PRAAx] monus (inst2 (S1B f b) i y) (inst2 (S1B f b) (pred i) y) ≐
        monus (inst2 (S1B f b) (succ (pred i)) y) (inst2 (S1B f b) (pred i) y) :=
      congrMonus (congrInst2 _ hi (.eqRefl _)) (.eqRefl _)
    refine mi.eqTrans ?_
    ipra_lc -natEq (eq_add_of_le (S1_mono f b hm h0 (Δ := C) (pred i) y)) +
      natEq (S1_eq (Γ := C) f b hm h0 (succ (pred i)) y) - natEq (S1_eq (Γ := C) f b hm h0 (pred i) y) +
      natEq (sum_succ' (Γ := C) (cvF b (dH f)) (succ (pred i)) y) -
      natEq (congrInst2 (Γ := C) (cvF b (dH f)) hi (.eqRefl y))

/-- `Σ_k a(k) Σ_j b(j) f(⌊⌊x/k⌋/j⌋) = Σ_n (a * b)(n) f(⌊x/n⌋)`. -/
theorem reorder (a : PTm 2) (x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (hRB (S1B f b) a)) (succ x) (pairT x y) ≐
      ap2 (sumF (hRB f (cvF a b))) (succ x) (pairT x y) := by
  refine (compose (S1B f b) a (S1_mono f b hm h0) (S1_zero f b hm h0) x y).eqTrans
    (.eqTrans ?_ (compose f (cvF a b) hm h0 x y).eqSymm)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_cvF, inst2_cvF]
  exact (conv_congr2 a _ _ (dS1 f b hm h0) _ _).eqTrans (conv_assoc a b (dH f) _ _)

end Reorder

end LeanProofs.IPRA.AnalyticNumberTheory.WeightedReorder
