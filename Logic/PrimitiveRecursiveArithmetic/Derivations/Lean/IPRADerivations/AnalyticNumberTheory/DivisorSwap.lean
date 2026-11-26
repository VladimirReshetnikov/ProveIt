import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.Core.LinearCombination
import IPRADerivations.AnalyticNumberTheory.DivisorCases
import IPRADerivations.Core.Reindex

/-!
# The divisor involution `d ↦ N/d`

For a body `G(a, b, N)` and `N ≥ 1`,

  `∑_{d ∣ N} G(d, N/d, N) = ∑_{d ∣ N} G(N/d, d, N)`   (`div_swap`).

This is the substitution `d ↔ N/d` used throughout the `von_mangoldt_totient_ipra_2026-11-15`
packet (the middle form of `thm:lambda-mobius`, the convolution `thm:mu-lambda`, and commutativity
of Dirichlet convolution). It is proved once for a body with a packed parameter `Z = (N, y)`, where the arithmetic
reads `N = fst Z` and the body receives `Z` (`DivisorSwapP.div_swap_p`, used by `pnt_ipra_constructive_2026-11-14`):
a Fubini swap of `∑_d ∑_e [d ∣ N][N/d = e] G(d, e, Z)`, whose indicator is symmetric,
`[d ∣ N][N/d = e] = [e ∣ N][N/e = d] = [N = d e]` (`zt_half`, `zt_symm`), so each row and each column collapses to
a single term by `sum_delta` (`row_sw`, `col_sw`). `div_swap` is the instance `Z = ⟨N, 0⟩`.
-/

set_option linter.unusedSimpArgs false

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap

alias quo_lt' := DivisorCases.quo_lt'

/-- `[d ≥ 1][d ∣ N][N/d = e]`. -/
abbrev zt (d e N : PTm n) : PTm n := (sg d * eqb (rem N d) zero) * eqb (quo N d) e

/-- `[d ≥ 1][d ∣ N][N/d = e] = [d ≥ 1][e ≥ 1][N = d e]` for `N ≥ 1`. -/
theorem zt_half {d e N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] zt d e N ≐ (sg d * sg e) * eqb N (d * e) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · ipra_lc (𝔞 (eqb (rem N d) zero) * 𝔞 (eqb (quo N d) e) - 𝔞 (sg e) * 𝔞 (eqb N (d * e))) * natEq ((congrSg Prf.hyp0).eqTrans sg_zero : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero)
  · refine .orE (eq_or_ne (rem N d) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N)
      have hk := pos_of_eq_mul hN.wk.wk eN
      refine .orE (eq_or_ne (quo N d) e) ?_ ?_
      · let C' : List (Fm PTm n) := (quo N d ≐ e) :: C
        have hq : C' ⊢[PRAAx] quo N d ≐ e := Prf.hyp0
        have sd := natEq ((congrSg hd.wk).eqTrans (sg_succ _) : C' ⊢[PRAAx] sg d ≐ one)
        have se := natEq ((congrSg hq.eqSymm).eqTrans ((congrSg hk.wk).eqTrans (sg_succ _)) : C' ⊢[PRAAx] sg e ≐ one)
        have hE := natEq (eqb_of_eq (Prf.hyp1 : C' ⊢[PRAAx] rem N d ≐ zero))
        have hQ := natEq (eqb_of_eq hq)
        have hB := natEq (eqb_of_eq (eN.wk.eqTrans (congrMul (.eqRefl _) hq)) : C' ⊢[PRAAx] eqb N (d * e) ≐ one)
        apply deriveNat; ipra_simps
        linear_combination 𝔞 (eqb (rem N d) zero) * 𝔞 (eqb (quo N d) e) * sd + 𝔞 (eqb (quo N d) e) * hE + hQ -
          𝔞 (sg e) * 𝔞 (eqb N (d * e)) * sd - 𝔞 (eqb N (d * e)) * se - hB
      · let C' : List (Fm PTm n) := neg (quo N d ≐ e) :: C
        have hQ : C' ⊢[PRAAx] eqb (quo N d) e ≐ zero := eqb_of_ne Prf.hyp0
        have hB : C' ⊢[PRAAx] eqb N (d * e) ≐ zero := by
          refine eqb_of_ne (.impI ?_)
          have c : ((N ≐ d * e) :: C') ⊢[PRAAx] quo N d ≐ e :=
            mul_cancel hd.wk.wk (eN.wk.wk.eqSymm.eqTrans Prf.hyp0)
          exact Prf.impE Prf.hyp1 c
        exact ((congrMul (.eqRefl _) hQ).eqTrans (mul_zero _)).eqTrans
          ((congrMul (.eqRefl _) hB).eqTrans (mul_zero _)).eqSymm
    · let C : List (Fm PTm n) := neg (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
      have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
      have hE : C ⊢[PRAAx] eqb (rem N d) zero ≐ zero := eqb_of_ne Prf.hyp0
      have hB : C ⊢[PRAAx] eqb N (d * e) ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have r : ((N ≐ d * e) :: C) ⊢[PRAAx] rem N d ≐ zero :=
          dvd_congr_left hd.wk.eqSymm (dvd_of_eq (Prf.hyp0.eqTrans (congrMul hd.wk (.eqRefl _))))
        exact Prf.impE Prf.hyp1 r
      exact (zero_mul_l ((congrMul (.eqRefl _) hE).eqTrans (mul_zero _)) _).eqTrans
        ((congrMul (.eqRefl _) hB).eqTrans (mul_zero _)).eqSymm

/-- The indicator is symmetric: `[d ∣ N][N/d = e] = [e ∣ N][N/e = d]` for `N ≥ 1`. -/
theorem zt_symm {d e N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] zt d e N ≐ zt e d N :=
  (zt_half hN).eqTrans (.eqTrans (congrMul (mul_comm _ _) (congrEqb' (.eqRefl _) (mul_comm _ _)))
    (zt_half hN).eqSymm)

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP

open LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap (zt zt_symm quo_lt')

/-! ## The involution with a packed parameter `Z = (N, y)` -/

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
    ipra_ring
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
    ipra_ring
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

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwapP

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap

/-! ## The plain involution, as the instance `Z = ⟨N, 0⟩` -/

section Swap

variable (G : PTm 3)

/-- `[d ∣ N] G(d, N/d, N)`, over `0 = d`, `1 = N`. -/
def SB : PTm 2 := (sg (var 0) * eqb (rem (var 1) (var 0)) zero) * Syn.subst ![var 0, quo (var 1) (var 0), var 1] G
/-- `[d ∣ N] G(N/d, d, N)`, over `0 = d`, `1 = N`. -/
def TB : PTm 2 := (sg (var 0) * eqb (rem (var 1) (var 0)) zero) * Syn.subst ![quo (var 1) (var 0), var 0, var 1] G

theorem inst2_SB (d N : PTm n) : inst2 (SB G) d N = (sg d * eqb (rem N d) zero) * inst3 G d (quo N d) N := by
  simp only [inst2, SB, PTm.subst_mul, subst_reindex3]
  simp

theorem inst2_TB (d N : PTm n) : inst2 (TB G) d N = (sg d * eqb (rem N d) zero) * inst3 G (quo N d) d N := by
  simp only [inst2, TB, PTm.subst_mul, subst_reindex3]
  simp

/-- `G` read at a packed parameter `Z` through `N = fst Z`. -/
def liftZ : PTm 3 := Syn.subst ![var 0, var 1, fstT (var 2)] G

theorem inst3_liftZ (a b Z : PTm n) : inst3 (liftZ G) a b Z = inst3 G a b (fstT Z) := by
  simp only [inst3, liftZ, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

/-- The divisor involution: `∑_{d ∣ N} G(d, N/d, N) = ∑_{d ∣ N} G(N/d, d, N)` for `N ≥ 1`. -/
theorem div_swap {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ N) N ≐ ap2 (sumF (TB G)) (succ N) N := by
  let Z : PTm n := pairT N zero
  have hZ : Γ ⊢[PRAAx] fstT Z ≐ N := fst_pair _ _
  have h1 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift N ≐ fstT (Syn.shift Z) := by
    simpa [Fm.shift, Syn.shift] using hZ.eqSymm.shift
  have b : Γ ⊢[PRAAx] succ N ≐ succ (fstT Z) := congrSucc hZ.eqSymm
  have p := DivisorSwapP.div_swap_p (Γ := Γ) (liftZ G) (Z := Z)
    (hZ.eqTrans (hN.eqTrans (congrSucc (congrPred hZ.eqSymm))))
  have cS : Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ N) N ≐
      ap2 (sumF (DivisorSwapP.SB (liftZ G))) (succ (fstT Z)) Z := by
    refine (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans (congrAp2 _ b (.eqRefl _))
    rw [inst2_SB, DivisorSwapP.inst2_SB, inst3_liftZ]
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF h1.wk (.eqRefl _)) (.eqRefl _)))
      (congrInst3 G (.eqRefl _) (congrAp2 quoF h1.wk (.eqRefl _)) h1.wk)
  have cT : Γ ⊢[PRAAx] ap2 (sumF (TB G)) (succ N) N ≐
      ap2 (sumF (DivisorSwapP.TB (liftZ G))) (succ (fstT Z)) Z := by
    refine (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans (congrAp2 _ b (.eqRefl _))
    rw [inst2_TB, DivisorSwapP.inst2_TB, inst3_liftZ]
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF h1.wk (.eqRefl _)) (.eqRefl _)))
      (congrInst3 G (congrAp2 quoF h1.wk (.eqRefl _)) (.eqRefl _) h1.wk)
  exact cS.eqTrans (p.eqTrans cT.eqSymm)

end Swap

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap
