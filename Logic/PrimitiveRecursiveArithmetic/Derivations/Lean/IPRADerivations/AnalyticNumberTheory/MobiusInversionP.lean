import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.AnalyticNumberTheory.DivisorCases
import IPRADerivations.Core.LinearCombination

/-!
# Möbius inversion with a parameter (`pnt_ipra_constructive_2026-11-14`, towards `sb:symmetry`)

`MobiusInversion.mobius_inversion` inverts `F(k) = Σ_{e ∣ k} f(e, N)` for a body `f` whose second variable is the
modulus `N` itself, so a body cannot carry an independent parameter (for instance the mesh and denominator
`(M, F)` of the packet's harmonic logarithm, which must be the same for every `n ≤ x`). This module proves the
same inversion for a packed parameter `Z = (N, y)`: the arithmetic reads `N = fst Z`, and the body receives `Z`:

  `Σ_{d ∣ N} μ⁺(d) Σ_{e ∣ N/d} f(e, Z) = Σ_{d ∣ N} μ⁻(d) Σ_{e ∣ N/d} f(e, Z) + f(N, Z)`  (`mobius_inversion_p`).

The proof is `MobiusInversion`'s, with its generic arithmetic lemmas (`dv_symm`, `eqb_quo`, `G_at`,
`cancel_gen`) reused at `N = fst Z`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (dv_symm eqb_quo shift_inst2)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Inversion

variable (f : PTm 2)

/-- `[d ∣ N] μ⁺_{N+1}(d) [e ∣ N/d] f(e, Z)` with `N = fst Z`, over `0 = d`, `1 = e`, `2 = Z`. -/
def aP : PTm 3 := ((sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) * muP (succ (fstT (var 2))) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (fstT (var 2)) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)
/-- `[d ∣ N] μ⁻_{N+1}(d) [e ∣ N/d] f(e, Z)`. -/
def aN : PTm 3 := ((sg (var 0) * eqb (rem (fstT (var 2)) (var 0)) zero) * muN (succ (fstT (var 2))) (var 0)) *
  ((sg (var 1) * eqb (rem (quo (fstT (var 2)) (var 0)) (var 1)) zero) * Syn.subst ![var 1, var 2] f)

theorem inst3_aP (d e Z : PTm n) : inst3 (aP f) d e Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) *
      ((sg e * eqb (rem (quo (fstT Z) d) e) zero) * inst2 f e Z) := by
  have hf : Syn.subst ![d, e, Z] (Syn.subst ![var 1, var 2] f) = inst2 f e Z := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, aP, PTm.subst_mul, hf]
  simp
theorem inst3_aN (d e Z : PTm n) : inst3 (aN f) d e Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) *
      ((sg e * eqb (rem (quo (fstT Z) d) e) zero) * inst2 f e Z) := by
  have hf : Syn.subst ![d, e, Z] (Syn.subst ![var 1, var 2] f) = inst2 f e Z := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst3, aN, PTm.subst_mul, hf]
  simp

theorem a_pt (d e Z : PTm n) :
    Γ ⊢[PRAAx] (inst3 (aP f) d e Z ≐ ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
        inst2 GP d (pairT (succ (fstT Z)) (quo (fstT Z) e))) ⋏
      (inst3 (aN f) d e Z ≐ ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
        inst2 GN d (pairT (succ (fstT Z)) (quo (fstT Z) e))) := by
  rw [inst3_aP, inst3_aN]
  have g := G_at (Γ := Γ) d (succ (fstT Z)) (quo (fstT Z) e)
  have g₁ := natEq (Prf.andE₁ g); have g₂ := natEq (Prf.andE₂ g)
  refine .andI ?_ ?_
  · ipra_lc 𝔞 (eqb (sq (succ (fstT Z)) d) zero) * 𝔞 (eqb (rem (om (succ (fstT Z)) d) two) zero) * 𝔞 (inst2 f e Z) * natEq (dv_symm (Γ := Γ) (fstT Z) d e) -
      𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * g₁
  · ipra_lc 𝔞 (eqb (sq (succ (fstT Z)) d) zero) * 𝔞 (eqb (rem (om (succ (fstT Z)) d) two) one) * 𝔞 (inst2 f e Z) * natEq (dv_symm (Γ := Γ) (fstT Z) d e) -
      𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * g₂

theorem col_scale (e Z : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
        ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
          ap2 (sumF GP) (succ (fstT Z)) (pairT (succ (fstT Z)) (quo (fstT Z) e))) ⋏
      (ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) ≐
        ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) *
          ap2 (sumF GN) (succ (fstT Z)) (pairT (succ (fstT Z)) (quo (fstT Z) e))) := by
  have hc : Syn.shift ((sg e * eqb (rem (fstT Z) e) zero) * inst2 f e Z) =
      (sg (Syn.shift e) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift e)) zero) * inst2 f (Syn.shift e) (Syn.shift Z) := by
    rw [Mobius.shift_mul', Mobius.shift_mul', shift_inst2]; simp [Syn.shift]
  have hp : Syn.shift (pairT (succ (fstT Z)) (quo (fstT Z) e)) =
      pairT (succ (fstT (Syn.shift Z))) (quo (fstT (Syn.shift Z)) (Syn.shift e)) := by
    simp [Syn.shift]
  refine .andI (sum_scale _ _ _ _ _ _ (.allI (.impI ?_))) (sum_scale _ _ _ _ _ _ (.allI (.impI ?_)))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₁ (a_pt f _ _ _))
  · rw [inst2_colB, shift_pairT, hc, hp]
    exact (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans (Prf.andE₂ (a_pt f _ _ _))

/-- A column: `C⁺(e) = C⁻(e) + [N = e] f(e, Z)` for `N = fst Z ≥ 1`. -/
theorem col_pt {e Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
      ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) + eqb (fstT Z) e * inst2 f e Z := by
  have cs := col_scale (Γ := Γ) f e Z
  have van : ∀ (Δ : List (Fm PTm n)), Γ ⊆ Δ → (Δ ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero) →
      (Δ ⊢[PRAAx] eqb (fstT Z) e ≐ zero) → (Δ ⊢[PRAAx] ap2 (sumF (colB (aP f))) (succ (fstT Z)) (pairT e Z) ≐
        ap2 (sumF (colB (aN f))) (succ (fstT Z)) (pairT e Z) + eqb (fstT Z) e * inst2 f e Z) := by
    intro Δ hs hc hq
    have z₁ := ((Prf.andE₁ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    have z₂ := ((Prf.andE₂ cs).weaken hs).eqTrans (zero_mul_l (zero_mul_l hc _) _)
    exact z₁.eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd z₂.eqSymm (zero_mul_l hq _).eqSymm))
  refine .orE (zero_or_succ e) ?_ ?_
  · let C : List (Fm PTm n) := (e ≐ zero) :: Γ
    have hc : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero := zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
    have hq : C ⊢[PRAAx] eqb (fstT Z) e ≐ zero :=
      eqb_of_ne (.impI (succ_ne_zero' _ (hN.wk.wk.eqSymm.eqTrans (Prf.hyp0.eqTrans Prf.hyp1))))
    exact van _ (List.subset_cons_of_subset _ (List.Subset.refl _)) hc hq
  · refine .orE (eq_or_ne (rem (fstT Z) e) zero) ?_ ?_
    · let C : List (Fm PTm n) := (rem (fstT Z) e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hd : C ⊢[PRAAx] dvd e (fstT Z) := Prf.hyp0
      have eN := eq_of_dvd' he hd
      have hk := pos_of_eq_mul hN.wk.wk eN
      have w := natEq eN; have wp := natEq he
      have hkN : C ⊢[PRAAx] le (succ (quo (fstT Z) e)) (succ (fstT Z)) := by
        refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred e * quo (fstT Z) e) ?_)
        ipra_lc w + 𝔞 (quo (fstT Z) e) * wp
      have one₁ : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ one :=
        (congrMul ((congrSg he).eqTrans (sg_succ _)) (eqb_of_eq hd)).eqTrans (by ipra_ring)
      ipra_lc natEq ((Prf.andE₁ cs).wk.wk : C ⊢[PRAAx] _) - natEq ((Prf.andE₂ cs).wk.wk : C ⊢[PRAAx] _) +
        𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * natEq (cancel_gen hk hkN hkN) +
        𝔞 (sg e) * 𝔞 (eqb (rem (fstT Z) e) zero) * 𝔞 (inst2 f e Z) * natEq (eqb_quo he eN) +
        𝔞 (inst2 f e Z) * 𝔞 (eqb (fstT Z) e) * natEq one₁
    · let C : List (Fm PTm n) := neg (rem (fstT Z) e ≐ zero) :: (e ≐ succ (pred e)) :: Γ
      have he : C ⊢[PRAAx] e ≐ succ (pred e) := Prf.hyp1
      have hc : C ⊢[PRAAx] sg e * eqb (rem (fstT Z) e) zero ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
      have hq : C ⊢[PRAAx] eqb (fstT Z) e ≐ zero := by
        refine eqb_of_ne (.impI ?_)
        have r : ((fstT Z ≐ e) :: C) ⊢[PRAAx] rem (fstT Z) e ≐ zero :=
          (congrAp2 remF Prf.hyp0 (.eqRefl e)).eqTrans
            (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.dvd_self' he.wk)
        exact Prf.impE Prf.hyp1 r
      exact van _ (fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hc hq

/-- `[fst (snd y) = e] f(e, snd y)`, over `0 = e`, `1 = y`. -/
def dltB : PTm 2 := eqb (fstT (sndT (var 1))) (var 0) * Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_dlt (e y : PTm n) : inst2 (dltB f) e y = eqb (fstT (sndT y)) e * inst2 f e (sndT y) := by
  have hf : Syn.subst ![e, y] (Syn.subst ![var 0, sndT (var 1)] f) = inst2 f e (sndT y) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  simp only [inst2, dltB, PTm.subst_mul, hf]
  simp

/-- Möbius inversion with a parameter: for `N = fst Z ≥ 1`,
`Σ_{d ∣ N} μ⁺(d) Σ_{e ∣ N/d} f(e, Z) = Σ_{d ∣ N} μ⁻(d) Σ_{e ∣ N/d} f(e, Z) + f(N, Z)`. -/
theorem mobius_inversion_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (oB (aN f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) + inst2 f (fstT Z) Z := by
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cs : Γ ⊢[PRAAx] ap2 (sumF (pB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (addBody (pB (aN f)) (dltB f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_addBody, inst2_pB, inst2_pB, inst2_dlt, shift_pairT, hs]
    refine (congrAp2 (sumF (colB (aP f))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((col_pt f (e := var 0) (Z := Syn.shift Z) hN'.wk).eqTrans ?_)
    exact congrAdd (congrAp2 (sumF (colB (aN f))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
      (congrMul (congrEqb' (congrFst (snd_pair _ _)).eqSymm (.eqRefl _)) (congrInst2 f (.eqRefl _) (snd_pair _ _).eqSymm))
  have dl : Γ ⊢[PRAAx] ap2 (sumF (dltB f)) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐ inst2 f (fstT Z) Z := by
    refine (sum_congr_bounded (dltB f) (dB f) _ (pairT (fstT Z) Z) (succ (fstT Z)) (.allI (.impI ?_))).eqTrans
      (sum_delta f (monus_self _))
    rw [inst2_dlt, inst2_dB, shift_pairT, shift_pairT, hs, show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]]
    exact congrMul (congrEqb' ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _).eqSymm) (.eqRefl _))
      (congrInst2 f (.eqRefl _) ((snd_pair _ _).eqTrans (snd_pair _ _).eqSymm))
  ipra_lc natEq (fubini (Γ := Γ) (aP f) (succ (fstT Z)) (succ (fstT Z)) Z) + natEq cs +
    natEq (sum_add (Γ := Γ) (pB (aN f)) (dltB f) (succ (fstT Z)) (pairT (succ (fstT Z)) Z)) + natEq dl -
    natEq (fubini (Γ := Γ) (aN f) (succ (fstT Z)) (succ (fstT Z)) Z)

/-- A row of the double sum in closed form, with a parameter: if `I(e, P)` is the summand
`[e ≥ 1][e ∣ N/d] f(e, Z)` of the inner sum (`hI`) and that sum is `F` whenever `1 ≤ N/d ≤ N` (`hF`), `N = fst Z`,
then the row of `d` is `[d ∣ N] μ^±(d) F`. -/
theorem row_closed_p (I : PTm 2) (d Z P F : PTm n) (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z)))
    (hI : ∀ {Δ : List (Fm PTm (n + 1))}, Δ ⊢[PRAAx]
      (sg (var 0) * eqb (rem (quo (fstT (Syn.shift Z)) (Syn.shift d)) (var 0)) zero) *
          inst2 f (var 0) (Syn.shift Z) ≐ inst2 I (var 0) (Syn.shift P))
    (hF : ∀ {C : List (Fm PTm n)}, (C ⊢[PRAAx] quo (fstT Z) d ≐ succ (pred (quo (fstT Z) d))) →
      (C ⊢[PRAAx] le (succ (quo (fstT Z) d)) (succ (fstT Z))) → (C ⊢[PRAAx] ap2 (sumF I) (succ (fstT Z)) P ≐ F)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP f)) d (pairT (succ (fstT Z)) Z) ≐
        ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) * F) ⋏
      (inst2 (oB (aN f)) d (pairT (succ (fstT Z)) Z) ≐
        ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) * F) := by
  rw [inst2_oB, inst2_oB]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ (fstT Z)) Z) ≐ succ (fstT Z) := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ (fstT Z)) Z) ≐ Z := snd_pair _ _
  have hcP : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muP (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muN (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  refine .andI
    ((congrAp2 (sumF (rowB (aP f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aP f)) I (succ (fstT Z)) ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) P
        (pairT d Z) (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
    ((congrAp2 (sumF (rowB (aN f))) f₁ (congrPairT (.eqRefl d) s₁)).eqTrans
      ((sum_scale (rowB (aN f)) I (succ (fstT Z)) ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) P
        (pairT d Z) (.allI (.impI ?_))).eqTrans (DivisorCases.divisor_quo_congr _ hN hF)))
  · rw [inst2_rowB, shift_pairT, hcP]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) hI
  · rw [inst2_rowB, shift_pairT, hcN]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) hI

/-- Möbius inversion with a parameter and the rows in closed form: if the row of `d` is `Q^±(d, Z)` (`row`), then
`∑_{d ≤ N} Q⁺(d, Z) = f(N, Z) + ∑_{d ≤ N} Q⁻(d, Z)` for `N = fst Z ≥ 1`. -/
theorem inversion_of_rows_p (QP QN : PTm 2) {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z)))
    (row : ∀ {Δ : List (Fm PTm (n + 1))},
      (Δ ⊢[PRAAx] fstT (Syn.shift Z) ≐ succ (pred (fstT (Syn.shift Z)))) →
      (Δ ⊢[PRAAx] (inst2 (oB (aP f)) (var 0) (pairT (succ (fstT (Syn.shift Z))) (Syn.shift Z)) ≐
          inst2 QP (var 0) (Syn.shift Z)) ⋏
        (inst2 (oB (aN f)) (var 0) (pairT (succ (fstT (Syn.shift Z))) (Syn.shift Z)) ≐
          inst2 QN (var 0) (Syn.shift Z)))) :
    Γ ⊢[PRAAx] ap2 (sumF QP) (succ (fstT Z)) Z ≐ inst2 f (fstT Z) Z + ap2 (sumF QN) (succ (fstT Z)) Z := by
  have inv := mobius_inversion_p (Γ := Γ) f hN
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF QP) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN f))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF QN) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row hN'.wk)
  ipra_lc -natEq cP + natEq inv + natEq cN

end Inversion

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP
