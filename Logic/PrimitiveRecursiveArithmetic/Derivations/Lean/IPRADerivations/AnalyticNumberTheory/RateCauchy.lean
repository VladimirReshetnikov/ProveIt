import IPRADerivations.AnalyticNumberTheory.RateIff
import IPRADerivations.Core.Header

/-!
# The explicit Cauchy modulus of the weighted series (`riemann_ipra_equivalences_2026-11-20`, `thm:rate` (3))

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `series.tex`, Theorem `thm:rate` (3):
"`P, Q ≥ 2^{4r(t+K)} ⟹ |S_r(P) − S_r(Q)| ≤ 2^{−t}`" and its proof: "For a tail with all shell indices `j ≥ 2L` the sum of
the geometric majorants is bounded by `16(c+1)2^r 2^{−L}`".

For a base point `P` and `Q ≥ P` the scaled difference of the weighted errors `E = W − M`,
`G(Q) = E(Q) u_P − E(P) u_Q`, satisfies `G(Q+1) = ρ_Q G(Q) + (ρ_Q − 1) M(Q) u_P` (`g_step`). The shell series between `P`
and `Q` telescopes against `F(j) = −2^{−⌊j/2⌋}(8 − 2(j mod 2))`; cleared by `2^{h_Q + h_P}` (`h = ⌊j/2⌋`) it is the integer
invariant `GInv`, which gives `2^{h_P}|G(Q)| ≤ 10 A u_P u_Q` with `A = (c+1)2^r`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RateCauchy

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RateAbel
open LeanProofs.IPRA.AnalyticNumberTheory.RateShell
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer (k4)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (aP aN : PTm 2)

/-- `E⁺(N) = W⁺(N) + M⁻(N)` and `E⁻(N) = W⁻(N) + M⁺(N)`, so `E = W − M = E⁺ − E⁻`. -/
abbrev EP (r y N : PTm n) : PTm n := Wv aP r y N + Mv aN y N
abbrev EN (r y N : PTm n) : PTm n := Wv aN r y N + Mv aP y N

/-- `G(Q) = E(Q) u_P − E(P) u_Q` as the pair `G⁺ = E⁺_Q u_P + E⁻_P u_Q`, `G⁻ = E⁻_Q u_P + E⁺_P u_Q`. -/
abbrev GP (r y P Q : PTm n) : PTm n := EP aP aN r y Q * uu r P + EN aP aN r y P * uu r Q
abbrev GN (r y P Q : PTm n) : PTm n := EN aP aN r y Q * uu r P + EP aP aN r y P * uu r Q
abbrev Gab (r y P Q : PTm n) : PTm n := absd (GP aP aN r y P Q) (GN aP aN r y P Q)

/-- `|G(Q+1)| ≤ ρ_Q |G(Q)| + (ρ_Q − 1)|M(Q)| u_P` for `Q ≥ 1`. -/
theorem g_step {r y P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] le (Gab aP aN r y P (succ Q))
      (rho r Q * Gab aP aN r y P Q + pred (rho r Q) * (Mab aP aN y Q * uu r P)) := by
  have hρ : Γ ⊢[PRAAx] rho r Q ≐ succ (pred (rho r Q)) := pos_of_one_le (rho_pos r Q)
  have uS := uu_succ hr hQ
  have qq : ∀ (X : PTm n), Γ ⊢[PRAAx] rho r Q * X ≐ pred (rho r Q) * X + X := fun X =>
    (congrMul hρ (.eqRefl X)).eqTrans (by ipra_ring)
  have qP := natEq (qq (Mv aP y Q * uu r P))
  have qN := natEq (qq (Mv aN y Q * uu r P))
  have uP := natEq ((congrMul (.eqRefl (EP aP aN r y P)) uS).eqTrans (by ipra_ring) :
    Γ ⊢[PRAAx] EP aP aN r y P * uu r (succ Q) ≐ rho r Q * (EP aP aN r y P * uu r Q))
  have uN := natEq ((congrMul (.eqRefl (EN aP aN r y P)) uS).eqTrans (by ipra_ring) :
    Γ ⊢[PRAAx] EN aP aN r y P * uu r (succ Q) ≐ rho r Q * (EN aP aN r y P * uu r Q))
  have l1 := le_mul_mono (le_refl (rho r Q)) (le_absd_l (Γ := Γ) (GP aP aN r y P Q) (GN aP aN r y P Q))
  have l2 := le_mul_mono (le_refl (rho r Q)) (le_absd_r (Γ := Γ) (GP aP aN r y P Q) (GN aP aN r y P Q))
  have l3 := le_mul_mono (le_refl (pred (rho r Q)))
    (le_mul_mono (le_absd_r (Γ := Γ) (Mv aP y Q) (Mv aN y Q)) (le_refl (uu r P)))
  have l4 := le_mul_mono (le_refl (pred (rho r Q)))
    (le_mul_mono (le_absd_l (Γ := Γ) (Mv aP y Q) (Mv aN y Q)) (le_refl (uu r P)))
  have wPu := natEq (congrMul (W_succ (Γ := Γ) aP r y Q) (.eqRefl (uu r P)))
  have wNu := natEq (congrMul (W_succ (Γ := Γ) aN r y Q) (.eqRefl (uu r P)))
  have mPu := natEq (congrMul (M_succ (Γ := Γ) aP y Q) (.eqRefl (uu r P)))
  have mNu := natEq (congrMul (M_succ (Γ := Γ) aN y Q) (.eqRefl (uu r P)))
  refine absd_le ?_ ?_
  · ipra_le sl l1 + sl l4 with wNu + mPu + uP - wPu - mNu - uN + qN - qP
  · ipra_le sl l2 + sl l3 with wPu + mNu + uN - wNu - mPu - uP + qP - qN

/-! ## The two-point invariant -/

/-- `U = u_P u_Q`. -/
abbrev UU (r P Q : PTm n) : PTm n := uu r P * uu r Q

/-- `2^{h_Q}2^{h_P}|G(Q)| + 8AU 2^{h_P} + 2AU 2^{h_Q}(j_P mod 2) ≤ 8AU 2^{h_Q} + 2AU 2^{h_P}(j_Q mod 2)`. -/
abbrev GInv (r c y P Q : PTm n) : Fm PTm n :=
  le (Hh r Q * Hh r P * Gab aP aN r y P Q + Ac r c * UU r P Q * Hh r P * eight +
      Ac r c * UU r P Q * Hh r Q * (two * rem (jj r P) two))
    (Ac r c * UU r P Q * Hh r Q * eight + Ac r c * UU r P Q * Hh r P * (two * rem (jj r Q) two))

theorem jj_congr {r P Q : PTm n} (h : Γ ⊢[PRAAx] P ≐ Q) : Γ ⊢[PRAAx] jj r P ≐ jj r Q :=
  congrAp2 quoF (congrPred (congrAp2 _ (congrSucc (congrSucc h)) (congrSucc h))) (.eqRefl _)

theorem uu_congr {r P Q : PTm n} (h : Γ ⊢[PRAAx] P ≐ Q) : Γ ⊢[PRAAx] uu r P ≐ uu r Q :=
  congrPw (.eqRefl _) (congrMul (.eqRefl _) (jj_congr h))

/-- The base `Q = P`. -/
theorem ginv_eq {r c y P Q : PTm n} (h : Γ ⊢[PRAAx] P ≐ Q) : Γ ⊢[PRAAx] GInv aP aN r c y P Q := by
  have eE1 : Γ ⊢[PRAAx] EP aP aN r y P ≐ EP aP aN r y Q :=
    congrAdd (congrAp2 _ h (.eqRefl _)) (congrAp2 _ h (.eqRefl _))
  have eE2 : Γ ⊢[PRAAx] EN aP aN r y P ≐ EN aP aN r y Q :=
    congrAdd (congrAp2 _ h (.eqRefl _)) (congrAp2 _ h (.eqRefl _))
  have eU := uu_congr (r := r) h
  have eJ := jj_congr (r := r) h
  have eH : Γ ⊢[PRAAx] Hh r P ≐ Hh r Q := congrPw (.eqRefl _) (congrAp2 quoF eJ (.eqRefl _))
  have eR : Γ ⊢[PRAAx] rem (jj r P) two ≐ rem (jj r Q) two := congrAp2 remF eJ (.eqRefl _)
  have e1 := natEq (congrMul (.eqRefl (EN aP aN r y Q)) eU)
  have e2 := natEq (congrMul eE1 (.eqRefl (uu r Q)))
  have e3 := natEq (congrMul (.eqRefl (EP aP aN r y Q)) eU)
  have e4 := natEq (congrMul eE2 (.eqRefl (uu r Q)))
  have z : Γ ⊢[PRAAx] le (Gab aP aN r y P Q) zero := by
    refine absd_le ?_ ?_
    · ipra_le 0 with e1 + e2 - e3 - e4
    · ipra_le 0 with e3 + e4 - e1 - e2
  have zs := le_mul_mono (le_refl (Hh r Q * Hh r P)) z
  have E1 := natEq (congrMul (congrMul (.eqRefl (Ac r c * UU r P Q)) eH) (.eqRefl (eight : PTm n)))
  have E2 := natEq (congrMul (congrMul (.eqRefl (Ac r c * UU r P Q)) eH.eqSymm) (congrMul (.eqRefl two) eR))
  ipra_le sl zs with -E1 - E2

/-- One step of the two-point invariant, for `1 ≤ P ≤ Q`. -/
theorem ginv_step {r c y P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hQ : Γ ⊢[PRAAx] le one Q)
    (ih : Γ ⊢[PRAAx] GInv aP aN r c y P Q)
    (hc : Γ ⊢[PRAAx] le (pw (Mab aP aN y Q) (k4 r)) (c * pw Q (succ (two * r)))) :
    Γ ⊢[PRAAx] GInv aP aN r c y P (succ Q) := by
  have gs := g_step (Γ := Γ) aP aN (y := y) (P := P) hr hQ
  have mb := m_bound' aP aN hr hQ hc
  have jm := jj_mono hr hQ
  have js := jj_step hr hQ
  have hρ : Γ ⊢[PRAAx] rho r Q ≐ succ (pred (rho r Q)) := pos_of_one_le (rho_pos r Q)
  have g4p : Γ ⊢[PRAAx] rho r Q * (Ac r c * UU r P Q * Hh r P) ≐
      pred (rho r Q) * (Ac r c * UU r P Q * Hh r P) + Ac r c * UU r P Q * Hh r P :=
    (congrMul hρ (.eqRefl _)).eqTrans (by ipra_ring)
  -- `ρ'·(2^{h_P} u_P)·(2^{h_Q}|M(Q)|) ≤ ρ'·(2^{h_P} u_P)·(2 A u_Q)`
  have f3 := le_mul_mono (le_refl (pred (rho r Q) * (Hh r P * uu r P))) mb
  refine .orE (lt_or_le (jj r Q) (jj r (succ Q))) ?_ ?_
  · let C : List (Fm PTm n) := lt (jj r Q) (jj r (succ Q)) :: Γ
    have hJ : C ⊢[PRAAx] jj r (succ Q) ≐ succ (jj r Q) := le_antisymm js.wk Prf.hyp0
    have eU : C ⊢[PRAAx] uu r (succ Q) ≐ rho r Q * uu r Q := uu_succ hr.wk hQ.wk
    have eUU : C ⊢[PRAAx] UU r P (succ Q) ≐ rho r Q * UU r P Q :=
      (congrMul (.eqRefl _) eU).eqTrans (by ipra_ring)
    have f1 := le_mul_mono (le_refl (Hh r Q * Hh r P)) (gs.wk : C ⊢[PRAAx] _)
    have f2 := le_mul_mono (le_refl (rho r Q)) (ih.wk : C ⊢[PRAAx] _)
    refine .orE (LeanProofs.IPRA.AnalyticNumberTheory.RateShell.half_succ (Γ := C) (j := jj r Q)) ?_ ?_
    · let D : List (Fm PTm n) := ((rem (jj r Q) two ≐ zero) ⋏ (quo (succ (jj r Q)) two ≐ quo (jj r Q) two) ⋏
        (rem (succ (jj r Q)) two ≐ one)) :: C
      have p0 : D ⊢[PRAAx] rem (jj r Q) two ≐ zero := Prf.andE₁ Prf.hyp0
      have q0 : D ⊢[PRAAx] quo (succ (jj r Q)) two ≐ quo (jj r Q) two := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
      have p1 : D ⊢[PRAAx] rem (succ (jj r Q)) two ≐ one := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
      have eH : D ⊢[PRAAx] Hh r Q ≐ Hh r (succ Q) :=
        (congrPw (.eqRefl _) ((congrAp2 quoF hJ.wk (.eqRefl _)).eqTrans q0)).eqSymm
      have eP : D ⊢[PRAAx] one ≐ rem (jj r (succ Q)) two := ((congrAp2 remF hJ.wk (.eqRefl _)).eqTrans p1).eqSymm
      have f2' : D ⊢[PRAAx] le (rho r Q * (Hh r Q * Hh r P * Gab aP aN r y P Q + Ac r c * UU r P Q * Hh r P * eight +
          Ac r c * UU r P Q * Hh r Q * (two * rem (jj r P) two)))
          (rho r Q * (Ac r c * UU r P Q * Hh r Q * eight + Ac r c * UU r P Q * Hh r P * (two * zero))) :=
        le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _)
          (congrMul (.eqRefl _) p0)))) f2.wk
      have core : D ⊢[PRAAx] le (Hh r Q * Hh r P * Gab aP aN r y P (succ Q) +
          Ac r c * (rho r Q * UU r P Q) * Hh r P * eight + Ac r c * (rho r Q * UU r P Q) * Hh r Q * (two * rem (jj r P) two))
          (Ac r c * (rho r Q * UU r P Q) * Hh r Q * eight + Ac r c * (rho r Q * UU r P Q) * Hh r P * (two * one)) := by
        have f1' := f1.wk (ψ := ((rem (jj r Q) two ≐ zero) ⋏ (quo (succ (jj r Q)) two ≐ quo (jj r Q) two) ⋏
          (rem (succ (jj r Q)) two ≐ one)))
        have f3' : D ⊢[PRAAx] _ := f3.wk.wk
        have g4 := natEq (Γ := D) (g4p.wk.wk)
        ipra_le sl f1' + sl f2' + sl f3' + 𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) with g4 + g4
      exact le_congr (congrAdd (congrAdd (congrMul (congrMul eH (.eqRefl _)) (.eqRefl _))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) (.eqRefl _)) (.eqRefl _)))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) eH) (.eqRefl _)))
        (congrAdd (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) eH) (.eqRefl _))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) (.eqRefl _)) (congrMul (.eqRefl _) eP))) core
    · let D : List (Fm PTm n) := ((rem (jj r Q) two ≐ one) ⋏ (quo (succ (jj r Q)) two ≐ succ (quo (jj r Q) two)) ⋏
        (rem (succ (jj r Q)) two ≐ zero)) :: C
      have p0 : D ⊢[PRAAx] rem (jj r Q) two ≐ one := Prf.andE₁ Prf.hyp0
      have q0 : D ⊢[PRAAx] quo (succ (jj r Q)) two ≐ succ (quo (jj r Q) two) := Prf.andE₁ (Prf.andE₂ Prf.hyp0)
      have p1 : D ⊢[PRAAx] rem (succ (jj r Q)) two ≐ zero := Prf.andE₂ (Prf.andE₂ Prf.hyp0)
      have eH : D ⊢[PRAAx] Hh r Q * two ≐ Hh r (succ Q) :=
        ((congrPw (.eqRefl _) ((congrAp2 quoF hJ.wk (.eqRefl _)).eqTrans q0)).eqTrans (pw_succ two _)).eqSymm
      have eP : D ⊢[PRAAx] zero ≐ rem (jj r (succ Q)) two := ((congrAp2 remF hJ.wk (.eqRefl _)).eqTrans p1).eqSymm
      have f2' : D ⊢[PRAAx] le (rho r Q * (Hh r Q * Hh r P * Gab aP aN r y P Q + Ac r c * UU r P Q * Hh r P * eight +
          Ac r c * UU r P Q * Hh r Q * (two * rem (jj r P) two)))
          (rho r Q * (Ac r c * UU r P Q * Hh r Q * eight + Ac r c * UU r P Q * Hh r P * (two * one))) :=
        le_congr (.eqRefl _) (congrMul (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _)
          (congrMul (.eqRefl _) p0)))) f2.wk
      have core : D ⊢[PRAAx] le (Hh r Q * two * Hh r P * Gab aP aN r y P (succ Q) +
          Ac r c * (rho r Q * UU r P Q) * Hh r P * eight +
          Ac r c * (rho r Q * UU r P Q) * (Hh r Q * two) * (two * rem (jj r P) two))
          (Ac r c * (rho r Q * UU r P Q) * (Hh r Q * two) * eight + Ac r c * (rho r Q * UU r P Q) * Hh r P * (two * zero)) := by
        have f1' := f1.wk (ψ := ((rem (jj r Q) two ≐ one) ⋏ (quo (succ (jj r Q)) two ≐ succ (quo (jj r Q) two)) ⋏
          (rem (succ (jj r Q)) two ≐ zero)))
        have f3' : D ⊢[PRAAx] _ := f3.wk.wk
        have g4 := natEq (Γ := D) (g4p.wk.wk)
        ipra_le sl f1' + sl f1' + sl f2' + sl f2' + sl f3' + sl f3' + 𝔞 (Ac r c * UU r P Q * Hh r P) +
          𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P)
          with g4 + g4 + g4 + g4
      exact le_congr (congrAdd (congrAdd (congrMul (congrMul eH (.eqRefl _)) (.eqRefl _))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) (.eqRefl _)) (.eqRefl _)))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) eH) (.eqRefl _)))
        (congrAdd (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) eH) (.eqRefl _))
          (congrMul (congrMul (congrMul (.eqRefl _) eUU.wk.eqSymm) (.eqRefl _)) (congrMul (.eqRefl _) eP))) core
  · let C : List (Fm PTm n) := le (jj r (succ Q)) (jj r Q) :: Γ
    have hJ : C ⊢[PRAAx] jj r (succ Q) ≐ jj r Q := le_antisymm Prf.hyp0 jm.wk
    have m0 : C ⊢[PRAAx] monus (jj r (succ Q)) (jj r Q) ≐ zero := (congrMonus hJ (.eqRefl _)).eqTrans (monus_self _)
    have r1 : C ⊢[PRAAx] rho r Q ≐ one :=
      (congrPw (.eqRefl _) ((congrMul (.eqRefl _) m0).eqTrans (mul_zero _))).eqTrans (pw_zero two)
    have r0 : C ⊢[PRAAx] pred (rho r Q) ≐ zero := (congrPred r1).eqTrans (pred_succ _)
    have eG : C ⊢[PRAAx] le (Gab aP aN r y P (succ Q)) (Gab aP aN r y P Q) := by
      refine le_congr (.eqRefl _) ?_ gs.wk
      exact (congrAdd ((congrMul r1 (.eqRefl _)).eqTrans (one_mul _)) ((congrMul r0 (.eqRefl _)).eqTrans
        (zero_mul _))).eqTrans (add_zero _)
    have eU : C ⊢[PRAAx] UU r P Q ≐ UU r P (succ Q) :=
      congrMul (.eqRefl _) (congrPw (.eqRefl _) (congrMul (.eqRefl _) hJ.eqSymm))
    have eH : C ⊢[PRAAx] Hh r Q ≐ Hh r (succ Q) := congrPw (.eqRefl _) (congrAp2 quoF hJ.eqSymm (.eqRefl _))
    have eR : C ⊢[PRAAx] rem (jj r Q) two ≐ rem (jj r (succ Q)) two := congrAp2 remF hJ.eqSymm (.eqRefl _)
    have m := le_mul_mono (le_refl (Hh r Q * Hh r P)) eG
    have core : C ⊢[PRAAx] le (Hh r Q * Hh r P * Gab aP aN r y P (succ Q) + Ac r c * UU r P Q * Hh r P * eight +
        Ac r c * UU r P Q * Hh r Q * (two * rem (jj r P) two))
        (Ac r c * UU r P Q * Hh r Q * eight + Ac r c * UU r P Q * Hh r P * (two * rem (jj r Q) two)) := by
      have ih' := ih.wk (ψ := le (jj r (succ Q)) (jj r Q))
      ipra_le sl m + sl ih'
    exact le_congr (congrAdd (congrAdd (congrMul (congrMul eH (.eqRefl _)) (.eqRefl _))
        (congrMul (congrMul (congrMul (.eqRefl _) eU) (.eqRefl _)) (.eqRefl _)))
        (congrMul (congrMul (congrMul (.eqRefl _) eU) eH) (.eqRefl _)))
      (congrAdd (congrMul (congrMul (congrMul (.eqRefl _) eU) eH) (.eqRefl _))
        (congrMul (congrMul (congrMul (.eqRefl _) eU) (.eqRefl _)) (congrMul (.eqRefl _) eR))) core

/-! ## The invariant for every `Q ≥ P` -/

/-- `GInv(P, Q)` for every `Q ≥ P ≥ 1`. -/
theorem ginv_all {r c y P : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hP : Γ ⊢[PRAAx] le one P)
    (hc : Γ ⊢[PRAAx] InM aP aN r c y) {Q : PTm n} (hPQ : Γ ⊢[PRAAx] le P Q) :
    Γ ⊢[PRAAx] GInv aP aN r c y P Q := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (Syn.shift P) (var 0) ⟶
      GInv aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) (Syn.shift P) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [GInv, Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
        LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI ?_
      exact lt_irrefl zero _ (le_trans hP.wk Prf.hyp0)
    · simp only [GInv, Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
        LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let φ : Fm PTm (n + 1) := le (Syn.shift P) (var 0) ⟶
        GInv aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) (Syn.shift P) (var 0)
      let Δ : List (Fm PTm (n + 1)) := le (Syn.shift P) (succ (var 0)) :: φ :: Γ.map Fm.shift
      have hr' : Δ ⊢[PRAAx] le one (Syn.shift r) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
        exact b.wk.wk
      have hP' : Δ ⊢[PRAAx] le one (Syn.shift P) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift P) := by simpa [Fm.shift, Syn.shift] using hP.shift
        exact b.wk.wk
      have hc' : Δ ⊢[PRAAx] InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] InM aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) := by
          have h := hc.shift
          simp only [InM, Fm.shift, Fm.subst_all, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul,
            PTm.subst_monus, LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
            Syn.subst_var, Syn.up_zero, subst_up_shift_pal,
            LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth.subst_sh] at h
          exact h
        exact b.wk.wk
      have hle : Δ ⊢[PRAAx] le (Syn.shift P) (succ (var 0)) := Prf.hyp0
      refine .orE (lt_or_le (var 0) (Syn.shift P)) ?_ ?_
      · -- `P = Q + 1`
        have h1 : (lt (var 0) (Syn.shift P) :: Δ) ⊢[PRAAx] Syn.shift P ≐ succ (var 0) :=
          le_antisymm hle.wk Prf.hyp0
        exact ginv_eq aP aN h1
      · -- `P ≤ Q`
        let E : List (Fm PTm (n + 1)) := le (Syn.shift P) (var 0) :: Δ
        have hPQ' : E ⊢[PRAAx] le (Syn.shift P) (var 0) := Prf.hyp0
        have ih : E ⊢[PRAAx] GInv aP aN (Syn.shift r) (Syn.shift c) (Syn.shift y) (Syn.shift P) (var 0) :=
          .impE (hyp2 : E ⊢[PRAAx] φ) hPQ'
        exact ginv_step aP aN hr'.wk (le_trans hP'.wk hPQ') ih (inM_at aP aN hc'.wk (var 0))
  have a := Prf.allE Q hall
  simp only [GInv, Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
    LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at a
  exact .impE a hPQ

/-! ## Monotonicity of the shell index -/

theorem lg_le {P Q : PTm n} (hP : Γ ⊢[PRAAx] le one P) (h : Γ ⊢[PRAAx] le P Q) : Γ ⊢[PRAAx] le (lg P) (lg Q) := by
  refine .orE (lt_or_le (lg Q) (lg P)) ?_ Prf.hyp0
  let C : List (Fm PTm n) := lt (lg Q) (lg P) :: Γ
  have b1 := Prf.andE₁ (lg_bracket (Γ := C) hP.wk)
  have b2 := Prf.andE₂ (lg_bracket (Γ := C) (le_trans hP.wk h.wk))
  have p := pw_le_exp (Γ := C) two_pos (Prf.hyp0 : C ⊢[PRAAx] lt (lg Q) (lg P))
  have c : C ⊢[PRAAx] le (succ Q) Q := le_trans b2 (le_trans p (le_trans b1 h.wk))
  exact lt_irrefl Q _ c

theorem hh_le {r P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hP : Γ ⊢[PRAAx] le one P) (h : Γ ⊢[PRAAx] le P Q) :
    Γ ⊢[PRAAx] le (Hh r P) (Hh r Q) :=
  pw_le_exp two_pos (LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet.quo_mono two_pos
    (LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet.quo_mono (two_r_pos hr) (lg_le hP h)))

/-- `2^{h_P}|G(Q)| ≤ 10 A u_P u_Q` for `1 ≤ P ≤ Q`. -/
theorem final_g {r c y P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hP : Γ ⊢[PRAAx] le one P)
    (hc : Γ ⊢[PRAAx] InM aP aN r c y) (hPQ : Γ ⊢[PRAAx] le P Q) :
    Γ ⊢[PRAAx] le (Hh r P * Gab aP aN r y P Q) (eight * (Ac r c * UU r P Q) + two * (Ac r c * UU r P Q)) := by
  have gi := ginv_all aP aN hr hP hc hPQ
  have hHQ : Γ ⊢[PRAAx] le one (Hh r Q) := one_le_pw' (by ipra_le 1) _
  have hp : Γ ⊢[PRAAx] Hh r Q ≐ succ (pred (Hh r Q)) := pos_of_one_le hHQ
  have hl := hh_le hr hP hPQ
  have rm : Γ ⊢[PRAAx] le (rem (jj r Q) two) one := by
    have d := Prf.andE₂ (div_mod_at (Γ := Γ) (x := jj r Q) (y := two) (c := one) (.eqRefl _))
    ipra_le sl d
  have s1 := le_mul_mono (le_refl (Ac r c * UU r P Q * Hh r P)) rm
  have s2 := le_mul_mono (le_refl (Ac r c * UU r P Q)) hl
  have core : Γ ⊢[PRAAx] le (Hh r Q * (Hh r P * Gab aP aN r y P Q))
      (Hh r Q * (eight * (Ac r c * UU r P Q) + two * (Ac r c * UU r P Q))) := by
    ipra_le sl gi + sl s1 + sl s1 + sl s2 + sl s2 + 𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) +
      𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) +
      𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) + 𝔞 (Ac r c * UU r P Q * Hh r P) +
      𝔞 (Ac r c * UU r P Q * Hh r Q * rem (jj r P) two) + 𝔞 (Ac r c * UU r P Q * Hh r Q * rem (jj r P) two)
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) core)

/-! ## The Cauchy estimate -/

/-- `W(P) u_Q − W(Q) u_P` as the pair `X⁺ = W⁺_P u_Q + W⁻_Q u_P`, `X⁻ = W⁻_P u_Q + W⁺_Q u_P`. -/
abbrev XP (r y P Q : PTm n) : PTm n := Wv aP r y P * uu r Q + Wv aN r y Q * uu r P
abbrev XN (r y P Q : PTm n) : PTm n := Wv aN r y P * uu r Q + Wv aP r y Q * uu r P

/-- `2^{h_P}|W(P)u_Q − W(Q)u_P| ≤ 14 A u_P u_Q` for `1 ≤ P ≤ Q`. -/
theorem cauchy_core {r c y P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hP : Γ ⊢[PRAAx] le one P)
    (hc : Γ ⊢[PRAAx] InM aP aN r c y) (hPQ : Γ ⊢[PRAAx] le P Q) :
    Γ ⊢[PRAAx] le (Hh r P * absd (XP aP aN r y P Q) (XN aP aN r y P Q))
      (eight * (Ac r c * UU r P Q) + two * (Ac r c * UU r P Q) + two * (Ac r c * UU r P Q) +
        two * (Ac r c * UU r P Q)) := by
  have hQ : Γ ⊢[PRAAx] le one Q := le_trans hP hPQ
  have d1 : Γ ⊢[PRAAx] le (absd (XP aP aN r y P Q) (XN aP aN r y P Q))
      (Gab aP aN r y P Q + Mab aP aN y P * uu r Q + Mab aP aN y Q * uu r P) := by
    have a1 := le_absd_r (Γ := Γ) (GP aP aN r y P Q) (GN aP aN r y P Q)
    have a2 := le_mul_mono (le_absd_l (Γ := Γ) (Mv aP y P) (Mv aN y P)) (le_refl (uu r Q))
    have a3 := le_mul_mono (le_absd_r (Γ := Γ) (Mv aP y Q) (Mv aN y Q)) (le_refl (uu r P))
    have b1 := le_absd_l (Γ := Γ) (GP aP aN r y P Q) (GN aP aN r y P Q)
    have b2 := le_mul_mono (le_absd_r (Γ := Γ) (Mv aP y P) (Mv aN y P)) (le_refl (uu r Q))
    have b3 := le_mul_mono (le_absd_l (Γ := Γ) (Mv aP y Q) (Mv aN y Q)) (le_refl (uu r P))
    refine absd_le ?_ ?_
    · ipra_le sl a1 + sl a2 + sl a3
    · ipra_le sl b1 + sl b2 + sl b3
  have e := le_mul_mono (le_refl (Hh r P)) d1
  have fg := final_g aP aN hr hP hc hPQ
  have m1 := le_mul_mono (m_bound' aP aN hr hP (inM_at aP aN hc P)) (le_refl (uu r Q))
  have hl := hh_le hr hP hPQ
  have m2a := le_mul_mono (le_mul_mono hl (le_refl (Mab aP aN y Q))) (le_refl (uu r P))
  have m2b := le_mul_mono (m_bound' aP aN hr hQ (inM_at aP aN hc Q)) (le_refl (uu r P))
  ipra_le sl e + sl fg + sl m1 + sl m2a + sl m2b

/-- `P ≥ 2^{4r(t+K)}` gives `2^t 2^K ≤ 2^{⌊j(P)/2⌋}`. -/
theorem threshold {r P t K : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hT : Γ ⊢[PRAAx] le (pw two (k4 r * (t + K))) P) :
    Γ ⊢[PRAAx] le (pw two t * pw two K) (Hh r P) := by
  have hP : Γ ⊢[PRAAx] le one P := le_trans (one_le_pw' (by ipra_le 1) _) hT
  have b := Prf.andE₂ (lg_bracket hP)
  have hl : Γ ⊢[PRAAx] le (k4 r * (t + K)) (lg P) := by
    refine .orE (lt_or_le (lg P) (k4 r * (t + K))) ?_ Prf.hyp0
    let C : List (Fm PTm n) := lt (lg P) (k4 r * (t + K)) :: Γ
    have p := pw_le_exp (Γ := C) two_pos (Prf.hyp0 : C ⊢[PRAAx] lt (lg P) (k4 r * (t + K)))
    exact lt_irrefl P _ (le_trans b.wk (le_trans p hT.wk))
  have hq : Γ ⊢[PRAAx] quo (two * r * (two * (t + K))) (two * r) ≐ two * (t + K) :=
    LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement.quo_mul (two_r_pos hr) (.eqRefl _)
  have hj : Γ ⊢[PRAAx] le (two * (t + K)) (jj r P) := by
    have q := LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet.quo_mono (two_r_pos hr)
      (le_congr (by ipra_ring) (.eqRefl _) hl : Γ ⊢[PRAAx] le (two * r * (two * (t + K))) (lg P))
    exact le_congr hq (.eqRefl _) q
  have hq2 : Γ ⊢[PRAAx] quo (two * (t + K)) two ≐ t + K :=
    LeanProofs.IPRA.AnalyticNumberTheory.LogRefinement.quo_mul two_pos (.eqRefl _)
  have hh : Γ ⊢[PRAAx] le (t + K) (quo (jj r P) two) :=
    le_congr hq2 (.eqRefl _) (LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet.quo_mono two_pos hj)
  exact le_congr (pw_add two t K) (.eqRefl _) (pw_le_exp two_pos hh)

/-- `16 A ≤ 2^{c+r+4}`. -/
theorem kc_ge (r c : PTm n) :
    Γ ⊢[PRAAx] le (two * (two * (two * (two * Ac r c)))) (pw two (Kc r c)) := by
  have cb := LeanProofs.IPRA.Topology.CollisionScales.lt_pw_two (Γ := Γ) c
  have cb' := le_mul_mono (le_refl (two * (two * (two * two)))) (le_mul_mono cb (le_refl (pw two r)))
  have eK : Γ ⊢[PRAAx] pw two (Kc r c) ≐ two * (two * (two * two)) * (pw two c * pw two r) := by
    refine ((pw_succ two _).eqTrans (congrMul ((pw_succ two _).eqTrans (congrMul ((pw_succ two _).eqTrans
      (congrMul ((pw_succ two _).eqTrans (congrMul (pw_add two c r) (.eqRefl _))) (.eqRefl _))) (.eqRefl _)))
      (.eqRefl _))).eqTrans ?_
    ipra_ring
  have f := natEq eK
  ipra_le sl cb' with f

/-- `thm:rate` (3), one order: for `P ≤ Q` above `2^{4r(t+K)}`, `2^t |W(P)u_Q − W(Q)u_P| ≤ u_P u_Q`, i.e.
`|S_r(P) − S_r(Q)| ≤ 2^{−t}`, with `K = c + r + 4`. -/
theorem cauchy_le {r c y t P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hc : Γ ⊢[PRAAx] InM aP aN r c y)
    (hT : Γ ⊢[PRAAx] le (pw two (k4 r * (t + Kc r c))) P) (hPQ : Γ ⊢[PRAAx] le P Q) :
    Γ ⊢[PRAAx] le (pw two t * absd (XP aP aN r y P Q) (XN aP aN r y P Q)) (UU r P Q) := by
  have hP : Γ ⊢[PRAAx] le one P := le_trans (one_le_pw' (by ipra_le 1) _) hT
  have core := cauchy_core aP aN hr hP hc hPQ
  have thr := threshold hr hT
  have kc := kc_ge (Γ := Γ) r c
  have s1 := le_mul_mono (le_refl (pw two t)) core
  have s2 := le_mul_mono (le_mul_mono (le_refl (pw two t)) kc) (le_refl (UU r P Q))
  have s3 := le_mul_mono thr (le_refl (UU r P Q))
  have hHP : Γ ⊢[PRAAx] le one (Hh r P) := one_le_pw' (by ipra_le 1) _
  have hp : Γ ⊢[PRAAx] Hh r P ≐ succ (pred (Hh r P)) := pos_of_one_le hHP
  have fin : Γ ⊢[PRAAx] le (Hh r P * (pw two t * absd (XP aP aN r y P Q) (XN aP aN r y P Q))) (Hh r P * UU r P Q) := by
    ipra_le sl s1 + sl s2 + sl s3 + 𝔞 (pw two t * (Ac r c * UU r P Q)) + 𝔞 (pw two t * (Ac r c * UU r P Q))
  exact mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) fin)

/-- `thm:rate` (3): both orders. -/
theorem cauchy {r c y t P Q : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hc : Γ ⊢[PRAAx] InM aP aN r c y)
    (hTP : Γ ⊢[PRAAx] le (pw two (k4 r * (t + Kc r c))) P) (hTQ : Γ ⊢[PRAAx] le (pw two (k4 r * (t + Kc r c))) Q) :
    Γ ⊢[PRAAx] le (pw two t * absd (XP aP aN r y P Q) (XN aP aN r y P Q)) (UU r P Q) := by
  refine .orE (le_total P Q) ?_ ?_
  · exact cauchy_le aP aN hr.wk hc.wk hTP.wk Prf.hyp0
  · have h := cauchy_le (Γ := le Q P :: Γ) aP aN hr.wk hc.wk hTQ.wk Prf.hyp0
    have eA : (le Q P :: Γ) ⊢[PRAAx] XP aP aN r y Q P ≐ XN aP aN r y P Q := add_comm _ _
    have eB : (le Q P :: Γ) ⊢[PRAAx] XN aP aN r y Q P ≐ XP aP aN r y P Q := add_comm _ _
    exact le_congr (congrMul (.eqRefl _) ((congrAdd (congrMonus eA eB) (congrMonus eB eA)).eqTrans (add_comm _ _)))
      (mul_comm _ _) h

end LeanProofs.IPRA.AnalyticNumberTheory.RateCauchy
