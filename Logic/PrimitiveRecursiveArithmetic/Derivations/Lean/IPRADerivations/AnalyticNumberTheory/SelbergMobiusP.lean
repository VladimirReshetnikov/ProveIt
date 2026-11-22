import IPRADerivations.AnalyticNumberTheory.SelbergMobius
import IPRADerivations.AnalyticNumberTheory.MobiusInversionP

/-!
# Selberg's exact symmetry identity with a weight parameter (`pnt_ipra_constructive_2026-11-14`, `sb:exact-symmetry`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma `sb:symmetry`:
"`μ * L² = Λ * Λ + 𝒟Λ`" (sb:exact-symmetry). `SelbergMobius.selberg_mobius` proves it for a prime weight `w`
with its parameter fixed to `0`; the packet's harmonic logarithm needs the weight's parameter (its mesh and
denominator), the same for every `n ≤ x`. With `MobiusInversionP` this module proves, for every prime weight `w`,
every parameter `y` and `N ≥ 1` (packed as `Z = (N, y)`):

  `Σ_{d ∣ N} μ⁺(d) L_w(N/d, y)² = L_w(N, y) Λ_w(N, y) + (Λ_w * Λ_w)(N, y) + Σ_{d ∣ N} μ⁻(d) L_w(N/d, y)²`
                                                                                         (`selberg_mobius_p`).

The divisor-form identity `L_w(k, y)² = Σ_{e ∣ k} G(e, y)` is `ConvolutionAssoc.selberg_divisor`, which already
carries the parameter (`inner_sq_p`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobiusP

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversionP (aP aN inst3_aP inst3_aN mobius_inversion_p)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv DwB inst2_DwB cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (lamF inst2_lamF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF selberg_divisor)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

section Selberg

variable (w : PTm 2)

/-- `G(e, y) = L_w(e, y) Λ_w(e, y) + (Λ_w * Λ_w)(e, y)` with `y = snd Z`, over `0 = e`, `1 = Z`. -/
abbrev GB : PTm 2 :=
  ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1))) *
      ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (sndT (var 1))) +
    ap2 (sumF (cvB (lamF w) (lamF w))) (succ (var 0)) (pairT (var 0) (sndT (var 1)))

/-- The `G`-expression at a parameter. -/
abbrev Gx (e y : PTm n) : PTm n := Lw w e y * Lam w e y + conv (lamF w) (lamF w) e y

theorem inst2_GB (e Z : PTm n) : inst2 (GB w) e Z = Gx w e (sndT Z) := by simp [inst2, subst_ap2]

theorem congrGx {e y y' : PTm n} (h : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx] Gx w e y ≐ Gx w e y' :=
  congrAdd (congrMul (congrAp2 _ (.eqRefl _) (congrPairT (.eqRefl _) h))
    (congrAp2 _ (.eqRefl _) (congrPairT (.eqRefl _) h))) (congrAp2 _ (.eqRefl _) (congrPairT (.eqRefl _) h))

/-- `[e ∣ fst x] G(e, snd x)`. -/
abbrev EB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * GB w

theorem inst2_EB (e x : PTm n) : inst2 (EB w) e x = (sg e * eqb (rem (fstT x) e) zero) * Gx w e (sndT x) := by
  simp [inst2, subst_ap2]

/-- `QSP(d, Z) = [d ∣ N] μ⁺(d) L_w(N/d, y)²`, `N = fst Z`, `y = snd Z`. -/
abbrev QSP : PTm 2 := ((sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * muP (succ (fstT (var 1))) (var 0)) *
  (ap2 (sumF (ellB w)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1))) *
    ap2 (sumF (ellB w)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1))))
/-- `QSN(d, Z) = [d ∣ N] μ⁻(d) L_w(N/d, y)²`. -/
abbrev QSN : PTm 2 := ((sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * muN (succ (fstT (var 1))) (var 0)) *
  (ap2 (sumF (ellB w)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1))) *
    ap2 (sumF (ellB w)) (succ (quo (fstT (var 1)) (var 0))) (pairT (quo (fstT (var 1)) (var 0)) (sndT (var 1))))

theorem inst2_QSP (d Z : PTm n) : inst2 (QSP w) d Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) *
      (Lw w (quo (fstT Z) d) (sndT Z) * Lw w (quo (fstT Z) d) (sndT Z)) := by
  simp [inst2, subst_ap2]
theorem inst2_QSN (d Z : PTm n) : inst2 (QSN w) d Z =
    ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) *
      (Lw w (quo (fstT Z) d) (sndT Z) * Lw w (quo (fstT Z) d) (sndT Z)) := by
  simp [inst2, subst_ap2]

/-- `Σ_{e ≤ N} [e ∣ k] G(e, y) = L_w(k, y)²` for `1 ≤ k ≤ N`. -/
theorem inner_sq_p {k N y : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (EB w)) (succ N) (pairT k y) ≐ Lw w k y * Lw w k y := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF (EB w)) (succ N) (pairT k y) ≐ ap2 (sumF (EB w)) (succ k) (pairT k y) := by
    refine sum_ext (EB w) (fun Δ a hs hl => ?_) hkN
    rw [inst2_EB, shift_pairT]
    refine zero_mul_l ((congrMul (.eqRefl _) ((congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
      (eqb_rem_big (hk'.weaken hs) hl))).eqTrans (mul_zero _)) _
  refine cut.eqTrans (.eqTrans ?_ (selberg_divisor w hk).eqSymm)
  refine (sum_congr_bounded (EB w) (addBody (cvB (DwB w (lamF w)) one) (cvB (cvF (lamF w) (lamF w)) one))
    (pairT k y) (pairT k y) (succ k) (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody, inst2_EB, shift_pairT]
  refine .eqTrans ?_ (congrAdd (cv_at _ _ _ _ _) (cv_at _ _ _ _ _)).eqSymm
  rw [inst2_DwB, inst2_lamF, inst2_cvF, show inst2 (one : PTm 2) (quo (Syn.shift k) (var 0)) (Syn.shift y) = one by
    simp [inst2]]
  refine (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (congrGx w (snd_pair _ _))).eqTrans ?_
  apply deriveNat; ipra_simps; ring

/-- A row of the inversion: `[d ∣ N] μ^±(d) Σ_{e ∣ N/d} G(e, y) = [d ∣ N] μ^±(d) L_w(N/d, y)²`. -/
theorem row_sq_mob_p {d Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (GB w))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QSP w) d Z) ⋏
      (inst2 (oB (aN (GB w))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QSN w) d Z) := by
  rw [inst2_oB, inst2_oB, inst2_QSP, inst2_QSN]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ (fstT Z)) Z) ≐ succ (fstT Z) := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ (fstT Z)) Z) ≐ Z := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP (GB w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN (GB w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muP (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) =
      (sg (Syn.shift d) * eqb (rem (fstT (Syn.shift Z)) (Syn.shift d)) zero) *
        muN (succ (fstT (Syn.shift Z))) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (pairT (quo (fstT Z) d) (sndT Z)) =
      pairT (quo (fstT (Syn.shift Z)) (Syn.shift d)) (sndT (Syn.shift Z)) := by
    simp [Syn.shift]
  have epq : ∀ {Δ : List (Fm PTm (n + 1))} (e Z' d' : PTm (n + 1)),
      Δ ⊢[PRAAx] (sg e * eqb (rem (quo (fstT Z') d') e) zero) * inst2 (GB w) e Z' ≐
        inst2 (EB w) e (pairT (quo (fstT Z') d') (sndT Z')) := fun e Z' d' => by
    rw [inst2_GB, inst2_EB]
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)))
      (congrGx w (snd_pair _ _).eqSymm)
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP (GB w)))) (succ (fstT Z)) (pairT d Z) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * muP (succ (fstT Z)) d) *
        ap2 (sumF (EB w)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcP, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN (GB w)))) (succ (fstT Z)) (pairT d Z) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * muN (succ (fstT Z)) d) *
        ap2 (sumF (EB w)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcN, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have key : ∀ (X : PTm n), Γ ⊢[PRAAx] ((sg d * eqb (rem (fstT Z) d) zero) * X) *
      ap2 (sumF (EB w)) (succ (fstT Z)) (pairT (quo (fstT Z) d) (sndT Z)) ≐
      ((sg d * eqb (rem (fstT Z) d) zero) * X) *
        (Lw w (quo (fstT Z) d) (sndT Z) * Lw w (quo (fstT Z) d) (sndT Z)) := by
    intro X
    refine .orE (zero_or_succ d) ?_ ?_
    · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · refine .orE (eq_or_ne (rem (fstT Z) d) zero) ?_ ?_
      · let C : List (Fm PTm n) := (rem (fstT Z) d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
        have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d (fstT Z))
        have hk := pos_of_eq_mul hN.wk.wk eN
        have ww := natEq eN; have wp := natEq hd
        have hkN : C ⊢[PRAAx] le (succ (quo (fstT Z) d)) (succ (fstT Z)) := by
          refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo (fstT Z) d) ?_)
          apply deriveNat; ipra_simps; linear_combination ww + 𝔞 (quo (fstT Z) d) * wp
        exact congrMul (.eqRefl _) (inner_sq_p w hk hkN)
      · have z : (neg (rem (fstT Z) d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx]
            sg d * eqb (rem (fstT Z) d) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by apply deriveNat; ipra_simps; ring)
        exact (zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm
  exact .andI (cR.eqTrans (scP.eqTrans (key _))) (cR'.eqTrans (scN.eqTrans (key _)))

/-- (sb:exact-symmetry) with a parameter: for `N = fst Z ≥ 1` and `y = snd Z`,
`Σ_{d ∣ N} μ⁺(d) L_w(N/d, y)² = L_w(N, y) Λ_w(N, y) + (Λ_w * Λ_w)(N, y) + Σ_{d ∣ N} μ⁻(d) L_w(N/d, y)²`. -/
theorem selberg_mobius_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (QSP w)) (succ (fstT Z)) Z ≐
      Gx w (fstT Z) (sndT Z) + ap2 (sumF (QSN w)) (succ (fstT Z)) Z := by
  have inv := mobius_inversion_p (Γ := Γ) (GB w) hN
  rw [inst2_GB] at inv
  have hN' := shift_pos hN
  rw [show Syn.shift (fstT Z) = fstT (Syn.shift Z) by simp [Syn.shift]] at hN'
  have hs : Syn.shift (succ (fstT Z)) = succ (fstT (Syn.shift Z)) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP (GB w)))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (QSP w)) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_sq_mob_p w hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN (GB w)))) (succ (fstT Z)) (pairT (succ (fstT Z)) Z) ≐
      ap2 (sumF (QSN w)) (succ (fstT Z)) Z := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_sq_mob_p w hN'.wk)
  have a := natEq inv; have b := natEq cP; have c := natEq cN
  apply deriveNat; ipra_simps
  linear_combination -b + a + c

end Selberg

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobiusP
