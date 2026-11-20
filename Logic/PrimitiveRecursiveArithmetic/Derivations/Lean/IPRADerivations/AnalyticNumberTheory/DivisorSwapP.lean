import IPRADerivations.AnalyticNumberTheory.DivisorSwap
import IPRADerivations.AnalyticNumberTheory.SelbergLeibniz
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc

/-!
# The divisor involution with a parameter, and commutativity of convolution (`pnt_ipra_constructive_2026-11-14`)

`DivisorSwap.div_swap` proves `Σ_{d∣N} G(d, N/d, N) = Σ_{d∣N} G(N/d, d, N)` for a body whose third variable is the
modulus `N` itself. This module proves the same involution for a packed parameter `Z = (N, y)` (the arithmetic reads
`N = fst Z`, the body receives `Z`), reusing `DivisorSwap.zt_half`/`zt_symm`, and derives

* `conv_comm`: `(f * g)(m, y) = (g * f)(m, y)` for every pair of bodies with a parameter;
* `tau_lw`: `τ(m) L_w(m, y) = 2 (L_w * 𝟏)(m, y)` (`SelbergLeibniz.tau_leibniz` with `conv_comm`), the identity behind
  `μ * (τ log) = 2 log` in `selberg.tex`, Lemma `sb:symmetry` ("`𝒟τ = 2L * 𝟏`").
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap (zt zt_symm quo_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv DwB inst2_cvB)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (tau_leibniz)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lw)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Swap

variable (G : PTm 3)

/-- `[d ∣ N][N/d = e] G(d, e, Z)`, `N = fst Z`. -/
def swB : PTm 3 := ((sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) * eqb (quo (fstT (var 2)) (var 0)) (var 1)) * G
/-- `[d ∣ N] G(d, N/d, Z)`. -/
def SB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) *
  Syn.subst ![var 0, quo (fstT (var 1)) (var 0), var 1] G
/-- `[d ∣ N] G(N/d, d, Z)`. -/
def TB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) *
  Syn.subst ![quo (fstT (var 1)) (var 0), var 0, var 1] G

theorem inst3_swB (d e Z : PTm n) : inst3 (swB G) d e Z = zt d e (fstT Z) * inst3 G d e Z := by
  simp [inst3, swB]

theorem inst2_SB (d Z : PTm n) :
    inst2 (SB G) d Z = (sg d * eqb (rem (fstT Z) d) zero) * inst3 G d (quo (fstT Z) d) Z := by
  have hf : Syn.subst ![d, Z] (Syn.subst ![var 0, quo (fstT (var 1)) (var 0), var 1] G) =
      inst3 G d (quo (fstT Z) d) Z := by
    simp only [inst3, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, SB, PTm.subst_mul, hf]
  simp

theorem inst2_TB (d Z : PTm n) :
    inst2 (TB G) d Z = (sg d * eqb (rem (fstT Z) d) zero) * inst3 G (quo (fstT Z) d) d Z := by
  have hf : Syn.subst ![d, Z] (Syn.subst ![quo (fstT (var 1)) (var 0), var 0, var 1] G) =
      inst3 G (quo (fstT Z) d) d Z := by
    simp only [inst3, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, TB, PTm.subst_mul, hf]
  simp

theorem row_sw (d Z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (swB G))) (succ (fstT Z)) (pairT d Z) ≐
      (sg d * eqb (rem (fstT Z) d) zero) * inst3 G d (quo (fstT Z) d) Z := by
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (swB G))) (succ (fstT Z)) (pairT d Z) ≐
      (sg d * eqb (rem (fstT Z) d) zero) * ap2 (sumF (dB (rowB G))) (succ (fstT Z)) (pairT (quo (fstT Z) d) (pairT d Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB (swB G), inst2_dB]
    simp only [shift_pairT]
    have hc : Syn.shift (sg d * eqb (rem (fstT Z) d) zero) =
        sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero := by simp [Syn.shift]
    have hq : Syn.shift (quo (fstT Z) d) = quo (fstT (Syn.shift Z)) (Syn.shift d) := by simp [Syn.shift]
    rw [hc, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_swB]
    have r1 : (lt (var 0) (Syn.shift (succ (fstT Z))) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 (rowB G) (var 0) (sndT (pairT (quo (fstT (Syn.shift Z)) (Syn.shift d)) (pairT (Syn.shift d) (Syn.shift Z)))) ≐
          inst3 G (Syn.shift d) (var 0) (Syn.shift Z) := by
      refine (congrInst2 (rowB G) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
      rw [inst2_rowB]
      exact congrInst3 G (fst_pair _ _) (.eqRefl _) (snd_pair _ _)
    refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul (congrEqb' (fst_pair _ _) (.eqRefl _)) r1)).eqSymm
    apply deriveNat; ipra_simps; ring
  refine sc.eqTrans ?_
  refine .orE (zero_or_succ d) ?_ ?_
  · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l (zero_mul_l s0 _) _).eqSymm
  · have hd : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    refine congrMul (.eqRefl _) ((sum_delta (rowB G) (quo_lt' hd)).eqTrans ?_)
    rw [inst2_rowB]
    exact congrInst3 G (fst_pair _ _) (.eqRefl _) (snd_pair _ _)

theorem col_sw {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) (e : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (swB G))) (succ (fstT Z)) (pairT e Z) ≐
      (sg e * eqb (rem (fstT Z) e) zero) * inst3 G (quo (fstT Z) e) e Z := by
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB (swB G))) (succ (fstT Z)) (pairT e Z) ≐
      (sg e * eqb (rem (fstT Z) e) zero) * ap2 (sumF (dB (colB G))) (succ (fstT Z)) (pairT (quo (fstT Z) e) (pairT e Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_colB (swB G), inst2_dB]
    simp only [shift_pairT]
    have hc : Syn.shift (sg e * eqb (rem (fstT Z) e) zero) =
        sg (Syn.shift e) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift e)) zero := by simp [Syn.shift]
    have hq : Syn.shift (quo (fstT Z) e) = quo (fstT (Syn.shift Z)) (Syn.shift e) := by simp [Syn.shift]
    rw [hc, hq]
    refine (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_swB]
    refine (congrMul (zt_symm hN'.wk) (.eqRefl _)).eqTrans ?_
    have r1 : (lt (var 0) (Syn.shift (succ (fstT Z))) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 (colB G) (var 0) (sndT (pairT (quo (fstT (Syn.shift Z)) (Syn.shift e)) (pairT (Syn.shift e) (Syn.shift Z)))) ≐
          inst3 G (var 0) (Syn.shift e) (Syn.shift Z) := by
      refine (congrInst2 (colB G) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
      rw [inst2_colB]
      exact congrInst3 G (.eqRefl _) (fst_pair _ _) (snd_pair _ _)
    refine .eqTrans ?_ (congrMul (.eqRefl _) (congrMul (congrEqb' (fst_pair _ _) (.eqRefl _)) r1)).eqSymm
    apply deriveNat; ipra_simps; ring
  refine sc.eqTrans ?_
  refine .orE (zero_or_succ e) ?_ ?_
  · have s0 : ((e ≐ zero) :: Γ) ⊢[PRAAx] sg e ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l (zero_mul_l s0 _) _).eqTrans (zero_mul_l (zero_mul_l s0 _) _).eqSymm
  · have he : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp0
    refine congrMul (.eqRefl _) ((sum_delta (colB G) (quo_lt' he)).eqTrans ?_)
    rw [inst2_colB]
    exact congrInst3 G (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

/-- The divisor involution with a parameter: `Σ_{d∣N} G(d, N/d, Z) = Σ_{d∣N} G(N/d, d, Z)` for `N = fst Z ≥ 1`. -/
theorem div_swap_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ (fstT Z)) Z ≐ ap2 (sumF (TB G)) (succ (fstT Z)) Z := by
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cS : Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ (fstT Z)) Z ≐
      ap2 (sumF (oB (swB G))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_SB, inst2_oB, shift_pairT, hs]
    refine .eqTrans ?_ (congrAp2 (sumF (rowB (swB G))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    exact (row_sw G _ _).eqSymm
  have cT : Γ ⊢[PRAAx] ap2 (sumF (TB G)) (succ (fstT Z)) Z ≐
      ap2 (sumF (pB (swB G))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_TB, inst2_pB, shift_pairT, hs]
    refine .eqTrans ?_ (congrAp2 (sumF (colB (swB G))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    exact (col_sw G hN'.wk _).eqSymm
  exact cS.eqTrans ((fubini (swB G) (succ (fstT Z)) (succ (fstT Z)) Z).eqTrans cT.eqSymm)

end Swap

/-! ## Commutativity of the convolution -/

/-- `f(a, snd Z) g(b, snd Z)`. -/
def fgB (f g : PTm 2) : PTm 3 := Syn.subst ![var 0, sndT (var 2)] f * Syn.subst ![var 1, sndT (var 2)] g

theorem inst3_fgB (f g : PTm 2) (a b Z : PTm n) : inst3 (fgB f g) a b Z = inst2 f a (sndT Z) * inst2 g b (sndT Z) := by
  have hf : Syn.subst ![a, b, Z] (Syn.subst ![var 0, sndT (var 2)] f) = inst2 f a (sndT Z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  have hg : Syn.subst ![a, b, Z] (Syn.subst ![var 1, sndT (var 2)] g) = inst2 g b (sndT Z) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, fgB, PTm.subst_mul, hf, hg]

/-- `(f * g)(m, y) = (g * f)(m, y)` for `m ≥ 1`. -/
theorem conv_comm (f g : PTm 2) {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] conv f g m y ≐ conv g f m y := by
  have rg : Γ ⊢[PRAAx] succ (fstT (pairT m y)) ≐ succ m := congrSucc (fst_pair _ _)
  have hN : Γ ⊢[PRAAx] fstT (pairT m y) ≐ succ (pred (fstT (pairT m y))) :=
    ConvolutionAssoc.pos_of_eq ((fst_pair _ _).eqTrans hm)
  have cS : Γ ⊢[PRAAx] ap2 (sumF (SB (fgB f g))) (succ (fstT (pairT m y))) (pairT m y) ≐ conv f g m y := by
    refine (congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
    rw [inst2_SB, inst3_fgB, inst2_cvB]
    exact .eqRefl _
  have cT : Γ ⊢[PRAAx] ap2 (sumF (TB (fgB f g))) (succ (fstT (pairT m y))) (pairT m y) ≐ conv g f m y := by
    refine (congrAp2 _ rg (.eqRefl _)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
    rw [inst2_TB, inst3_fgB, inst2_cvB]
    apply deriveNat; ipra_simps; ring
  exact cS.eqSymm.eqTrans ((div_swap_p (fgB f g) hN).eqTrans cT)

/-- `τ(m) L_w(m, y) = 2 (L_w * 𝟏)(m, y)` for `m ≥ 1`. -/
theorem tau_lw (w : PTm 2) {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * conv one one m y ≐ two * conv (DwB w one) one m y := by
  have t := natEq (tau_leibniz (Γ := Γ) w (y := y) hm)
  have c := natEq (conv_comm (Γ := Γ) one (DwB w one) (y := y) hm)
  apply deriveNat; ipra_simps; linear_combination t + c

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP
