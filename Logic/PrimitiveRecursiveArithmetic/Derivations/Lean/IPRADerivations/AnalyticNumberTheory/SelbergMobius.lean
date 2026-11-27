import IPRADerivations.AnalyticNumberTheory.ConvolutionAssoc
import IPRADerivations.AnalyticNumberTheory.MangoldtMobius

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

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds (sum_ext shift_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusInversion (aP aN inst3_aP inst3_aN mobius_inversion eqb_rem_big)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv DwB inst2_DwB cv_at)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (lamF inst2_lamF)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF selberg_divisor)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

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
  rw [inst2_QSP, inst2_QSN]
  refine MobiusInversion.row_closed (GB w) (EB w) d N (pairT (quo N d) zero)
    (Lw w (quo N d) zero * Lw w (quo N d) zero) hN ?_ fun hk hkN => inner_sq w hk hkN
  intro Δ
  rw [show Syn.shift (pairT (quo N d) (zero : PTm n)) = pairT (quo (Syn.shift N) (Syn.shift d)) zero by
    simp [Syn.shift], inst2_GB, inst2_EB]
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF (fst_pair _ _).eqSymm (.eqRefl _)) (.eqRefl _)))
    (.eqRefl _)

/-- (sb:exact-symmetry) `μ * L_w² = 𝒟_w Λ_w + Λ_w * Λ_w`:
`Σ_{d ∣ N} μ⁺(d) L_w(N/d)² = L_w(N) Λ_w(N) + (Λ_w * Λ_w)(N) + Σ_{d ∣ N} μ⁻(d) L_w(N/d)²` for `N ≥ 1`. -/
theorem selberg_mobius {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (QSP w)) (succ N) N ≐
      (Lw w N zero * Lam w N zero + conv (lamF w) (lamF w) N zero) + ap2 (sumF (QSN w)) (succ N) N := by
  have h := MobiusInversion.inversion_of_rows (GB w) (QSP w) (QSN w) hN fun h => row_sq_mob w h
  rwa [inst2_GB] at h

end Selberg

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergMobius
