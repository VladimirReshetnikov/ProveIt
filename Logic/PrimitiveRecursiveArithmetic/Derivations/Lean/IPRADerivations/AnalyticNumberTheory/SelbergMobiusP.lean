import IPRADerivations.AnalyticNumberTheory.SelbergMobius
import IPRADerivations.AnalyticNumberTheory.MobiusInversion
import IPRADerivations.Core.LinearCombination
import IPRADerivations.AnalyticNumberTheory.DivisorCases
import IPRADerivations.Core.Header

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

open_ipra
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
  ipra_ring

/-- A row of the inversion: `[d ∣ N] μ^±(d) Σ_{e ∣ N/d} G(e, y) = [d ∣ N] μ^±(d) L_w(N/d, y)²`. -/
theorem row_sq_mob_p {d Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] (inst2 (oB (aP (GB w))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QSP w) d Z) ⋏
      (inst2 (oB (aN (GB w))) d (pairT (succ (fstT Z)) Z) ≐ inst2 (QSN w) d Z) := by
  rw [inst2_QSP, inst2_QSN]
  refine MobiusInversionP.row_closed_p (GB w) (EB w) d Z (pairT (quo (fstT Z) d) (sndT Z))
    (Lw w (quo (fstT Z) d) (sndT Z) * Lw w (quo (fstT Z) d) (sndT Z)) hN ?_ fun hk hkN => inner_sq_p w hk hkN
  intro Δ
  rw [show Syn.shift (pairT (quo (fstT Z) d) (sndT Z)) =
    pairT (quo (fstT (Syn.shift Z)) (Syn.shift d)) (sndT (Syn.shift Z)) by simp [Syn.shift], inst2_GB, inst2_EB]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)))
    (congrGx w (snd_pair _ _).eqSymm)

/-- (sb:exact-symmetry) with a parameter: for `N = fst Z ≥ 1` and `y = snd Z`,
`Σ_{d ∣ N} μ⁺(d) L_w(N/d, y)² = L_w(N, y) Λ_w(N, y) + (Λ_w * Λ_w)(N, y) + Σ_{d ∣ N} μ⁻(d) L_w(N/d, y)²`. -/
theorem selberg_mobius_p {Z : PTm n} (hN : Γ ⊢[PRAAx] fstT Z ≐ succ (pred (fstT Z))) :
    Γ ⊢[PRAAx] ap2 (sumF (QSP w)) (succ (fstT Z)) Z ≐
      Gx w (fstT Z) (sndT Z) + ap2 (sumF (QSN w)) (succ (fstT Z)) Z := by
  have h := MobiusInversionP.inversion_of_rows_p (GB w) (QSP w) (QSN w) hN fun h => row_sq_mob_p w h
  rwa [inst2_GB] at h

end Selberg

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobiusP
