import IPRADerivations.AnalyticNumberTheory.DivisorSwap
import IPRADerivations.AnalyticNumberTheory.SelbergLeibniz
import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.Core.LinearCombination

/-!
# The divisor involution with a parameter, and commutativity of convolution (`pnt_ipra_constructive_2026-11-14`)

`DivisorSwap.div_swap` proves `Σ_{d∣N} G(d, N/d, N) = Σ_{d∣N} G(N/d, d, N)` for a body whose third variable is the
modulus `N` itself. The involution for a packed parameter `Z = (N, y)` (`div_swap_p`) is in the module `DivisorSwap`; this module
derives from it

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
    ipra_ring
  exact cS.eqSymm.eqTrans ((div_swap_p (fgB f g) hN).eqTrans cT)

/-- `τ(m) L_w(m, y) = 2 (L_w * 𝟏)(m, y)` for `m ≥ 1`. -/
theorem tau_lw (w : PTm 2) {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * conv one one m y ≐ two * conv (DwB w one) one m y := by
  ipra_lc natEq (tau_leibniz (Γ := Γ) w (y := y) hm) + natEq (conv_comm (Γ := Γ) one (DwB w one) (y := y) hm)

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP
