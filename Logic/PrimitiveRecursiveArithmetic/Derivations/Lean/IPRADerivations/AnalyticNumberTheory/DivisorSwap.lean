import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.Core.LinearCombination
import IPRADerivations.AnalyticNumberTheory.DivisorCases

/-!
# The divisor involution `d ↦ N/d`

For a body `G(a, b, N)` and `N ≥ 1`,

  `∑_{d ∣ N} G(d, N/d, N) = ∑_{d ∣ N} G(N/d, d, N)`   (`div_swap`).

This is the substitution `d ↔ N/d` used throughout the `von_mangoldt_totient_ipra_2026-11-15`
packet (the middle form of `thm:lambda-mobius`, the convolution `thm:mu-lambda`, and commutativity
of Dirichlet convolution). The proof is a Fubini swap of `∑_d ∑_e [d ∣ N][N/d = e] G(d, e, N)`:
the indicator is symmetric, `[d ∣ N][N/d = e] = [e ∣ N][N/e = d] = [N = d e]` (`zt_half`, `zt_symm`),
so each row and each column collapses to a single term by `sum_delta` (`row_sw`, `col_sw`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (shift_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

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

section Swap

variable (G : PTm 3)

/-- `[d ∣ N][N/d = e] G(d, e, N)`, over `0 = d`, `1 = e`, `2 = N`. -/
def swB : PTm 3 := ((sg (var 0) * eqb (rem (var 2) (var 0)) zero) * eqb (quo (var 2) (var 0)) (var 1)) * G

/-- `[d ∣ N] G(d, N/d, N)`, over `0 = d`, `1 = N`. -/
def SB : PTm 2 := (sg (var 0) * eqb (rem (var 1) (var 0)) zero) * Syn.subst ![var 0, quo (var 1) (var 0), var 1] G
/-- `[d ∣ N] G(N/d, d, N)`, over `0 = d`, `1 = N`. -/
def TB : PTm 2 := (sg (var 0) * eqb (rem (var 1) (var 0)) zero) * Syn.subst ![quo (var 1) (var 0), var 0, var 1] G

theorem inst3_swB (d e N : PTm n) : inst3 (swB G) d e N = zt d e N * inst3 G d e N := by
  simp [inst3, swB]

theorem inst2_SB (d N : PTm n) : inst2 (SB G) d N = (sg d * eqb (rem N d) zero) * inst3 G d (quo N d) N := by
  have hf : Syn.subst ![d, N] (Syn.subst ![var 0, quo (var 1) (var 0), var 1] G) = inst3 G d (quo N d) N := by
    simp only [inst3, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, SB, PTm.subst_mul, hf]
  simp

theorem inst2_TB (d N : PTm n) : inst2 (TB G) d N = (sg d * eqb (rem N d) zero) * inst3 G (quo N d) d N := by
  have hf : Syn.subst ![d, N] (Syn.subst ![quo (var 1) (var 0), var 0, var 1] G) = inst3 G (quo N d) d N := by
    simp only [inst3, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, TB, PTm.subst_mul, hf]
  simp

/-- A row: `∑_{e ≤ N} [d ∣ N][N/d = e] G(d, e) = [d ∣ N] G(d, N/d)`. -/
theorem row_sw (d N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (swB G))) (succ N) (pairT d N) ≐
      (sg d * eqb (rem N d) zero) * inst3 G d (quo N d) N := by
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB (swB G))) (succ N) (pairT d N) ≐
      (sg d * eqb (rem N d) zero) * ap2 (sumF (dB (rowB G))) (succ N) (pairT (quo N d) (pairT d N)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB (swB G), inst2_dB]
    simp only [shift_pairT]
    have hc : Syn.shift (sg d * eqb (rem N d) zero) =
        sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero := by simp [Syn.shift]
    have hq : Syn.shift (quo N d) = quo (Syn.shift N) (Syn.shift d) := by simp [Syn.shift]
    rw [hc, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_swB]
    have r1 : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 (rowB G) (var 0) (sndT (pairT (quo (Syn.shift N) (Syn.shift d)) (pairT (Syn.shift d) (Syn.shift N)))) ≐
          inst3 G (Syn.shift d) (var 0) (Syn.shift N) := by
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

/-- A column: `∑_{d ≤ N} [d ∣ N][N/d = e] G(d, e) = [e ∣ N] G(N/e, e)` for `N ≥ 1`. -/
theorem col_sw {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (e : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (swB G))) (succ N) (pairT e N) ≐
      (sg e * eqb (rem N e) zero) * inst3 G (quo N e) e N := by
  have hN' := shift_pos hN
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB (swB G))) (succ N) (pairT e N) ≐
      (sg e * eqb (rem N e) zero) * ap2 (sumF (dB (colB G))) (succ N) (pairT (quo N e) (pairT e N)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_colB (swB G), inst2_dB]
    simp only [shift_pairT]
    have hc : Syn.shift (sg e * eqb (rem N e) zero) =
        sg (Syn.shift e) * eqb (rem (Syn.shift N) (Syn.shift e)) zero := by simp [Syn.shift]
    have hq : Syn.shift (quo N e) = quo (Syn.shift N) (Syn.shift e) := by simp [Syn.shift]
    rw [hc, hq]
    refine (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_swB]
    refine (congrMul (zt_symm hN'.wk) (.eqRefl _)).eqTrans ?_
    have r1 : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 (colB G) (var 0) (sndT (pairT (quo (Syn.shift N) (Syn.shift e)) (pairT (Syn.shift e) (Syn.shift N)))) ≐
          inst3 G (var 0) (Syn.shift e) (Syn.shift N) := by
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

/-- The divisor involution: `∑_{d ∣ N} G(d, N/d, N) = ∑_{d ∣ N} G(N/d, d, N)` for `N ≥ 1`. -/
theorem div_swap {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ N) N ≐ ap2 (sumF (TB G)) (succ N) N := by
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cS : Γ ⊢[PRAAx] ap2 (sumF (SB G)) (succ N) N ≐ ap2 (sumF (oB (swB G))) (succ N) (pairT (succ N) N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_SB, inst2_oB, shift_pairT, hs]
    refine .eqTrans ?_ (congrAp2 (sumF (rowB (swB G))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    exact (row_sw G _ _).eqSymm
  have cT : Γ ⊢[PRAAx] ap2 (sumF (TB G)) (succ N) N ≐ ap2 (sumF (pB (swB G))) (succ N) (pairT (succ N) N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_TB, inst2_pB, shift_pairT, hs]
    refine .eqTrans ?_ (congrAp2 (sumF (colB (swB G))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
    exact (col_sw G hN'.wk _).eqSymm
  exact cS.eqTrans ((fubini (swB G) (succ N) (succ N) N).eqTrans cT.eqSymm)

end Swap

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSwap
