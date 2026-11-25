import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.MangoldtMobius
import IPRADerivations.Core.LinearCombination

/-!
# Selberg's exact symmetry identity `μ * L² = Λ * Λ + 𝒟Λ` (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma
`sb:symmetry`: "`L² = L * Λ + 𝟏 * (𝒟Λ) = 𝟏 * (Λ * Λ + 𝒟Λ)`. Convolution with `μ` therefore gives
`μ * L² = Λ * Λ + 𝒟Λ`" (sb:exact-symmetry).

For a prime weight `w` (with its parameter fixed to `0`, as in `MangoldtMobius`) and `N ≥ 1`, with the
signed Möbius function `μ = μ⁺ − μ⁻` of `Mobius`:

  `Σ_{d ∣ N} μ⁺(d) L_w(N/d)² = L_w(N) Λ_w(N) + (Λ_w * Λ_w)(N) + Σ_{d ∣ N} μ⁻(d) L_w(N/d)²`
                                                                                     (`selberg_mobius`).

This is `MobiusInversion.mobius_inversion` for the function `G = 𝒟_w Λ_w + Λ_w * Λ_w`, whose divisor
sums are `Σ_{e ∣ k} G(e) = L_w(k)²` by `ConvolutionAssoc.selberg_divisor` (`inner_sq`); each row of
the inversion is `[d ∣ N] μ^±(d) L_w(N/d)²` (`row_sq_mob`, as `MangoldtMobius.row_lam_mob`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobius

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (aP aN inst3_aP inst3_aN mobius_inversion eqb_rem_big)
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

/-- `G(e) = L_w(e) Λ_w(e) + (Λ_w * Λ_w)(e)` (parameter `0`), over `0 = e`, `1 = N` (unused). -/
abbrev GB : PTm 2 :=
  ap2 (sumF (ellB w)) (succ (var 0)) (pairT (var 0) zero) * ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) zero) +
    ap2 (sumF (cvB (lamF w) (lamF w))) (succ (var 0)) (pairT (var 0) zero)

theorem inst2_GB (e N : PTm n) :
    inst2 (GB w) e N = Lw w e zero * Lam w e zero + conv (lamF w) (lamF w) e zero := by
  simp [inst2, subst_ap2]

/-- `[e ∣ fst x] G(e)`. -/
abbrev EB : PTm 2 := (sg (var 0) * eqb (rem (fstT (var 1)) (var 0)) zero) * GB w

theorem inst2_EB (e x : PTm n) : inst2 (EB w) e x =
    (sg e * eqb (rem (fstT x) e) zero) * (Lw w e zero * Lam w e zero + conv (lamF w) (lamF w) e zero) := by
  simp [inst2, subst_ap2]

/-- `QSP(d, N) = [d ∣ N] μ⁺(d) L_w(N/d)²`. -/
abbrev QSP : PTm 2 := PB * (ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero) *
  ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero))
/-- `QSN(d, N) = [d ∣ N] μ⁻(d) L_w(N/d)²`. -/
abbrev QSN : PTm 2 := NB * (ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero) *
  ap2 (sumF (ellB w)) (succ (quo (var 1) (var 0))) (pairT (quo (var 1) (var 0)) zero))

theorem inst2_QSP (d N : PTm n) : inst2 (QSP w) d N =
    ((sg d * eqb (rem N d) zero) * muP (succ N) d) * (Lw w (quo N d) zero * Lw w (quo N d) zero) := by
  simp [inst2, subst_ap2]
theorem inst2_QSN (d N : PTm n) : inst2 (QSN w) d N =
    ((sg d * eqb (rem N d) zero) * muN (succ N) d) * (Lw w (quo N d) zero * Lw w (quo N d) zero) := by
  simp [inst2, subst_ap2]

/-- `Σ_{e ≤ N} [e ∣ k] G(e) = L_w(k)²` for `1 ≤ k ≤ N`. -/
theorem inner_sq {k N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hkN : Γ ⊢[PRAAx] le (succ k) (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF (EB w)) (succ N) (pairT k zero) ≐ Lw w k zero * Lw w k zero := by
  have hk' := shift_pos hk
  have cut : Γ ⊢[PRAAx] ap2 (sumF (EB w)) (succ N) (pairT k zero) ≐ ap2 (sumF (EB w)) (succ k) (pairT k zero) := by
    refine sum_ext (EB w) (fun Δ a hs hl => ?_) hkN
    rw [inst2_EB, shift_pairT]
    refine zero_mul_l ((congrMul (.eqRefl _) ((congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)).eqTrans
      (eqb_rem_big (hk'.weaken hs) hl))).eqTrans (mul_zero _)) _
  refine cut.eqTrans (.eqTrans ?_ (selberg_divisor w hk).eqSymm)
  refine (sum_congr_bounded (EB w) (addBody (cvB (DwB w (lamF w)) one) (cvB (cvF (lamF w) (lamF w)) one))
    (pairT k zero) (pairT k zero) (succ k) (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  rw [inst2_addBody, inst2_EB, shift_pairT]
  refine .eqTrans ?_ (congrAdd (cv_at _ _ _ _ _) (cv_at _ _ _ _ _)).eqSymm
  rw [inst2_DwB, inst2_lamF, inst2_cvF, show inst2 (one : PTm 2) (quo (Syn.shift k) (var 0)) (Syn.shift (zero : PTm n)) = one by
    simp [inst2]]
  refine (congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _) (.eqRefl _)) (.eqRefl _)))
    (.eqRefl _)).eqTrans ?_
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
  ipra_ring

/-- A row of the inversion for `G`: `[d ∣ N] μ^±(d) Σ_{e ∣ N/d} G(e) = [d ∣ N] μ^±(d) L_w(N/d)²`. -/
theorem row_sq_mob {d N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (GB w))) d (pairT (succ N) N) ≐ inst2 (QSP w) d N) ⋏
      (inst2 (oB (aN (GB w))) d (pairT (succ N) N) ≐ inst2 (QSN w) d N) := by
  rw [inst2_oB, inst2_oB, inst2_QSP, inst2_QSN]
  have f₁ : Γ ⊢[PRAAx] fstT (pairT (succ N) N) ≐ succ N := fst_pair _ _
  have s₁ : Γ ⊢[PRAAx] sndT (pairT (succ N) N) ≐ N := snd_pair _ _
  have cR := congrAp2 (sumF (rowB (aP (GB w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have cR' := congrAp2 (sumF (rowB (aN (GB w)))) f₁ (congrPairT (.eqRefl d) s₁)
  have hcP : Syn.shift ((sg d * eqb (rem N d) zero) * muP (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muP (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hcN : Syn.shift ((sg d * eqb (rem N d) zero) * muN (succ N) d) =
      (sg (Syn.shift d) * eqb (rem (Syn.shift N) (Syn.shift d)) zero) * muN (succ (Syn.shift N)) (Syn.shift d) := by
    simp [Syn.shift]
  have hq : Syn.shift (pairT (quo N d) (zero : PTm n)) = pairT (quo (Syn.shift N) (Syn.shift d)) zero := by
    simp [Syn.shift]
  have epq : ∀ {Δ : List (Fm PTm (n + 1))} (e N' d' : PTm (n + 1)),
      Δ ⊢[PRAAx] (sg e * eqb (rem (quo N' d') e) zero) * inst2 (GB w) e N' ≐
        inst2 (EB w) e (pairT (quo N' d') zero) := fun e N' d' => by
    rw [inst2_GB, inst2_EB]
    exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)))
      (.eqRefl _)
  have scP : Γ ⊢[PRAAx] ap2 (sumF (rowB (aP (GB w)))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muP (succ N) d) * ap2 (sumF (EB w)) (succ N) (pairT (quo N d) zero) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcP, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aP]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have scN : Γ ⊢[PRAAx] ap2 (sumF (rowB (aN (GB w)))) (succ N) (pairT d N) ≐
      ((sg d * eqb (rem N d) zero) * muN (succ N) d) * ap2 (sumF (EB w)) (succ N) (pairT (quo N d) zero) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, shift_pairT, hcN, hq]
    refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
    rw [inst3_aN]
    exact congrMul (.eqRefl _) (epq _ _ _)
  have key : ∀ (X : PTm n), Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * ap2 (sumF (EB w)) (succ N) (pairT (quo N d) zero) ≐
      ((sg d * eqb (rem N d) zero) * X) * (Lw w (quo N d) zero * Lw w (quo N d) zero) := by
    intro X
    refine .orE (zero_or_succ d) ?_ ?_
    · have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqTrans (zero_mul_l (zero_mul_l (zero_mul_l s0 _) _) _).eqSymm
    · refine .orE (eq_or_ne (rem N d) zero) ?_ ?_
      · let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
        have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
        have eN := eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N)
        have hk := pos_of_eq_mul hN.wk.wk eN
        have ww := natEq eN; have wp := natEq hd
        have hkN : C ⊢[PRAAx] le (succ (quo N d)) (succ N) := by
          refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo N d) ?_)
          ipra_lc ww + 𝔞 (quo N d) * wp
        exact congrMul (.eqRefl _) (inner_sq w hk hkN)
      · have z : (neg (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d * eqb (rem N d) zero ≐ zero :=
          (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (by ipra_ring)
        exact (zero_mul_l (zero_mul_l z _) _).eqTrans (zero_mul_l (zero_mul_l z _) _).eqSymm
  exact .andI (cR.eqTrans (scP.eqTrans (key _))) (cR'.eqTrans (scN.eqTrans (key _)))

/-- (sb:exact-symmetry) `μ * L_w² = 𝒟_w Λ_w + Λ_w * Λ_w`:
`Σ_{d ∣ N} μ⁺(d) L_w(N/d)² = L_w(N) Λ_w(N) + (Λ_w * Λ_w)(N) + Σ_{d ∣ N} μ⁻(d) L_w(N/d)²` for `N ≥ 1`. -/
theorem selberg_mobius {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (QSP w)) (succ N) N ≐
      (Lw w N zero * Lam w N zero + conv (lamF w) (lamF w) N zero) + ap2 (sumF (QSN w)) (succ N) N := by
  have inv := mobius_inversion (Γ := Γ) (GB w) hN
  rw [inst2_GB] at inv
  have hN' := shift_pos hN
  have hs : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have cP : Γ ⊢[PRAAx] ap2 (sumF (oB (aP (GB w)))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF (QSP w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₁ (row_sq_mob w hN'.wk)
  have cN : Γ ⊢[PRAAx] ap2 (sumF (oB (aN (GB w)))) (succ N) (pairT (succ N) N) ≐ ap2 (sumF (QSN w)) (succ N) N := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, hs]
    exact Prf.andE₂ (row_sq_mob w hN'.wk)
  ipra_lc -natEq cP + natEq inv + natEq cN

end Selberg

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobius
