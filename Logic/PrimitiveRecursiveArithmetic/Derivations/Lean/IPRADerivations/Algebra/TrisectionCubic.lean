import IPRADerivations.Algebra.CubeRootTwo
import IPRADerivations.Core.Descent
import IPRADerivations.Core.CertificateTactics

/-!
# `X³ − 3X − 1` has no rational root (`three_impossibilities_ipra`)

The packet's second impossibility reduces the trisection of `60°` to the cubic
`Y³ − 3Y − 1 = 0` satisfied by `Y = 2 cos 20°` (from the triple-angle identity,
`Algebra.PolynomialFormulas.triple_angle`), and shows that this cubic has no
rational root.

For a root `a/b` with `b > 0`, clearing denominators gives `a³ − 3ab² − b³ = 0`.
Splitting the sign of `a`, there are two natural-number equations:

* `a ≥ 0`: `a³ = 3ab² + b³`;
* `a = −c ≤ 0`: `3cb² = c³ + b³`.

Each is refuted for `b ≠ 0` by 2-adic infinite descent (`Core.Descent`): every
parity case except `a, b` both even is impossible, and halving both gives a
smaller solution. The bounds `a ≤ 3b` and `c ≤ 2b` hold for all solutions.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.TrisectionCubic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ double_cancel lt_succ_of_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Indicators of equations -/

theorem chi01 (L R b : PTm n) :
    Γ ⊢[PRAAx] (eqb L R * sg b ≐ zero) ⋎ (eqb L R * sg b ≐ one) := by
  refine .orE (eq_or_ne L R) ?_ ?_
  · refine .orE (zero_or_succ b) ?_ ?_
    · refine .orI₁ ((congrMul (.eqRefl _) ?_).eqTrans (mul_zero _))
      exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero
    · refine .orI₂ ((congrMul (eqb_of_eq Prf.hyp1) ?_).eqTrans (one_mul _))
      exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans (sg_succ _)
  · exact .orI₁ ((congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _))

theorem eq_of_chi {L R b : PTm n} (h : Γ ⊢[PRAAx] eqb L R * sg b ≐ one) : Γ ⊢[PRAAx] L ≐ R := by
  refine .orE (eq_or_ne L R) Prf.hyp0 ?_
  refine .botE _ (succ_ne_zero (a := zero) ?_)
  exact h.wk.eqSymm.eqTrans ((congrMul (eqb_of_ne Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _))

theorem chi_of {L R b c : PTm n} (h : Γ ⊢[PRAAx] L ≐ R) (hb : Γ ⊢[PRAAx] b ≐ succ c) :
    Γ ⊢[PRAAx] eqb L R * sg b ≐ one :=
  (congrMul (eqb_of_eq h) ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hb)).eqTrans
    (sg_succ _))).eqTrans (one_mul _)

theorem chi_zero (L R : PTm n) : Γ ⊢[PRAAx] eqb L R * sg zero ≐ zero :=
  (congrMul (.eqRefl _) sg_zero).eqTrans (mul_zero _)

/-! ## Parity contradictions -/

/-- `L = R` with `L` even and `R` odd is absurd. -/
theorem even_odd_absurd {Δ : List (Fm PTm 2)} {L R : PTm 2} (φ : Fm PTm 2) (K M : PTm 2)
    (e : Δ ⊢[PRAAx] L ≐ R) (hL : Δ ⊢[PRAAx] L ≐ two * K) (hR : Δ ⊢[PRAAx] R ≐ two * M + one) :
    Δ ⊢[PRAAx] φ :=
  even_ne_odd φ (hL.eqSymm.eqTrans (e.eqTrans hR))

/-- `L = R` with `L` odd and `R` even is absurd. -/
theorem odd_even_absurd {Δ : List (Fm PTm 2)} {L R : PTm 2} (φ : Fm PTm 2) (K M : PTm 2)
    (e : Δ ⊢[PRAAx] L ≐ R) (hL : Δ ⊢[PRAAx] L ≐ two * K + one) (hR : Δ ⊢[PRAAx] R ≐ two * M) :
    Δ ⊢[PRAAx] φ :=
  even_ne_odd φ (hR.eqSymm.eqTrans (e.eqSymm.eqTrans hL))

/-- Rewrite by the two parity equations in the context and close by `ring`. -/
macro "par_ring" : tactic =>
  `(tactic| (refine withEq Prf.hyp0 (fun e₁ => withEq Prf.hyp1 (fun e₂ => ?_))) <;>
    (apply deriveNat) <;> ipra_simps <;> (try rw [e₁]) <;> (try rw [e₂]) <;> ring)

/-! ## The halving step, shared by both sign cases -/

/-- Variables `0 = a`, `1 = b`, and their halves. -/
abbrev A : PTm 2 := var 0
abbrev B : PTm 2 := var 1
abbrev H : PTm 2 := half (var 0)
abbrev G : PTm 2 := half (var 1)

/-- If `b = 2g` with `b ≠ 0`, then `g ≠ 0` and `g < b`. -/
theorem half_lt {Δ : List (Fm PTm 2)} (hb : Δ ⊢[PRAAx] B ≐ succ (pred B))
    (h2 : Δ ⊢[PRAAx] B ≐ two * G) : Δ ⊢[PRAAx] (G ≐ succ (pred G)) ⋏ lt G B := by
  refine .orE (zero_or_succ G) ?_ ?_
  · refine .botE _ (succ_ne_zero (a := pred B) ?_)
    exact hb.wk.eqSymm.eqTrans (h2.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))
  refine .andI Prf.hyp0 (le_of_eq_add (d := pred G) ?_)
  refine withEq Prf.hyp0 fun e₁ => withEq h2.wk fun e₂ => ?_
  ipra_lc e₂ + e₁

/-! ## The case `a ≥ 0`: `a³ = 3ab² + b³` -/

section Nonneg

abbrev L₁ (a b : PTm n) : PTm n := a * a * a
abbrev R₁ (a b : PTm n) : PTm n := num 3 * a * (b * b) + b * b * b

/-- The indicator of a solution with `b ≠ 0`. -/
abbrev χ₁ : PTm 2 := eqb (L₁ (var 0) (var 1)) (R₁ (var 0) (var 1)) * sg (var 1)
/-- Solutions have `a ≤ 3b`. -/
abbrev β₁ : PTm 1 := succ (num 3 * var 0)

theorem inst2_χ₁ (a b : PTm n) : inst2 χ₁ a b = eqb (L₁ a b) (R₁ a b) * sg b := by
  simp [inst2]

/-- The context of the halving step. -/
abbrev Θ₁ : List (Fm PTm 2) := [B ≐ succ (pred B), eqb (L₁ A B) (R₁ A B) * sg B ≐ one]

/-- `a ∸ (3b + 1)`. -/
abbrev D₁ : PTm 2 := monus A (succ (num 3 * B))

theorem hyps₁ : Descent.Hyps χ₁ β₁ H G where
  h01 := by rw [inst2_χ₁]; exact chi01 _ _ _
  h0 := by rw [inst2_χ₁]; exact chi_zero _ _
  hb := by
    rw [inst2_χ₁]
    simp only [inst1, ConciseIPRA.PTm.subst_succ, PTm.subst_mul, PTm.subst_num, Syn.subst_var,
      Matrix.cons_val_zero]
    have e := eq_of_chi (Prf.hyp0 :
      ([eqb (L₁ A B) (R₁ A B) * sg B ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] _)
    refine .orE (lt_or_le (num 3 * B) A) ?_ (lt_succ_of_le Prf.hyp0)
    refine .botE _ (succ_ne_zero (a := num 17 * (B * B * B) + num 24 * (B * B) * D₁
      + num 24 * (B * B) + num 9 * B * (D₁ * D₁) + num 18 * B * D₁ + num 9 * B
      + D₁ * D₁ * D₁ + num 3 * (D₁ * D₁) + num 3 * D₁) ?_)
    refine withEq e.wk fun e₁ => withEq (eq_add_of_le Prf.hyp0) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination e₁
  hstep := by
    rw [inst2_χ₁, inst2_χ₁]
    have e : Θ₁ ⊢[PRAAx] L₁ A B ≐ R₁ A B := eq_of_chi Prf.hyp1
    have hb : Θ₁ ⊢[PRAAx] B ≐ succ (pred B) := Prf.hyp0
    refine .orE (even_or_odd B) ?_ ?_
    · refine .orE (even_or_odd A) ?_ ?_
      · -- a, b even: the halves form a smaller solution.
        have hg := half_lt (Δ := (A ≐ two * H) :: (B ≐ two * G) :: Θ₁) hb.wk.wk Prf.hyp1
        have e' : ((A ≐ two * H) :: (B ≐ two * G) :: Θ₁) ⊢[PRAAx] L₁ H G ≐ R₁ H G := by
          refine double_cancel (double_cancel (double_cancel ?_))
          refine withEq e.wk.wk fun e₀ => withEq Prf.hyp0 fun e₁ => withEq Prf.hyp1 fun e₂ => ?_
          apply deriveNat; ipra_simps; rw [e₁, e₂] at e₀; linear_combination e₀
        exact .andI (chi_of e' (Prf.andE₁ hg)) (Prf.andE₂ hg)
      · exact odd_even_absurd _ (num 4 * (H * H * H) + num 6 * (H * H) + num 3 * H)
          (num 4 * (G * G * G) + num 12 * (G * G) * H + num 6 * (G * G)) e.wk.wk
          (by par_ring) (by par_ring)
    · refine .orE (even_or_odd A) ?_ ?_
      · exact even_odd_absurd _ (num 4 * (H * H * H))
          (num 4 * (G * G * G) + num 12 * (G * G) * H + num 6 * (G * G) + num 12 * G * H
            + num 3 * G + num 3 * H) e.wk.wk (by par_ring) (by par_ring)
      · exact odd_even_absurd _ (num 4 * (H * H * H) + num 6 * (H * H) + num 3 * H)
          (num 4 * (G * G * G) + num 12 * (G * G) * H + num 12 * (G * G) + num 12 * G * H
            + num 9 * G + num 3 * H + num 2) e.wk.wk (by par_ring) (by par_ring)

/-- `a³ = 3ab² + b³ → b = 0`. -/
abbrev nonnegFormula : Fm PTm 2 := (L₁ A B ≐ R₁ A B) ⟶ (B ≐ zero)

theorem nonneg_root : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 nonnegFormula := by
  refine closeUniv 2 (.impI ?_)
  refine .orE (zero_or_succ B) Prf.hyp0 ?_
  have h := Descent.descent hyps₁
  rw [inst2_χ₁] at h
  exact .botE _ (h.trans (by
    intro ψ hψ; simp only [List.mem_singleton] at hψ; subst hψ
    exact chi_of Prf.hyp1 Prf.hyp0))

end Nonneg

/-! ## The case `a = −c ≤ 0`: `3cb² = c³ + b³` -/

section Nonpos

abbrev L₂ (c b : PTm n) : PTm n := num 3 * c * (b * b)
abbrev R₂ (c b : PTm n) : PTm n := c * c * c + b * b * b

abbrev χ₂ : PTm 2 := eqb (L₂ (var 0) (var 1)) (R₂ (var 0) (var 1)) * sg (var 1)
/-- Solutions have `c ≤ 2b`. -/
abbrev β₂ : PTm 1 := succ (two * var 0)

theorem inst2_χ₂ (a b : PTm n) : inst2 χ₂ a b = eqb (L₂ a b) (R₂ a b) * sg b := by
  simp [inst2]

abbrev Θ₂ : List (Fm PTm 2) := [B ≐ succ (pred B), eqb (L₂ A B) (R₂ A B) * sg B ≐ one]

/-- `c ∸ (2b + 1)`. -/
abbrev D₂ : PTm 2 := monus A (succ (two * B))

theorem hyps₂ : Descent.Hyps χ₂ β₂ H G where
  h01 := by rw [inst2_χ₂]; exact chi01 _ _ _
  h0 := by rw [inst2_χ₂]; exact chi_zero _ _
  hb := by
    rw [inst2_χ₂]
    simp only [inst1, ConciseIPRA.PTm.subst_succ, PTm.subst_mul, Syn.subst_var,
      Matrix.cons_val_zero, ConciseIPRA.PTm.subst_zero]
    have e := eq_of_chi (Prf.hyp0 :
      ([eqb (L₂ A B) (R₂ A B) * sg B ≐ one] : List (Fm PTm 2)) ⊢[PRAAx] _)
    refine .orE (lt_or_le (two * B) A) ?_ (lt_succ_of_le Prf.hyp0)
    refine .botE _ (succ_ne_zero (a := num 3 * (B * B * B) + num 9 * (B * B) * D₂
      + num 9 * (B * B) + num 6 * B * (D₂ * D₂) + num 12 * B * D₂ + num 6 * B
      + D₂ * D₂ * D₂ + num 3 * (D₂ * D₂) + num 3 * D₂) ?_)
    refine withEq e.wk fun e₁ => withEq (eq_add_of_le Prf.hyp0) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₂] at e₁; linear_combination -e₁
  hstep := by
    rw [inst2_χ₂, inst2_χ₂]
    have e : Θ₂ ⊢[PRAAx] L₂ A B ≐ R₂ A B := eq_of_chi Prf.hyp1
    have hb : Θ₂ ⊢[PRAAx] B ≐ succ (pred B) := Prf.hyp0
    refine .orE (even_or_odd B) ?_ ?_
    · refine .orE (even_or_odd A) ?_ ?_
      · have hg := half_lt (Δ := (A ≐ two * H) :: (B ≐ two * G) :: Θ₂) hb.wk.wk Prf.hyp1
        have e' : ((A ≐ two * H) :: (B ≐ two * G) :: Θ₂) ⊢[PRAAx] L₂ H G ≐ R₂ H G := by
          refine double_cancel (double_cancel (double_cancel ?_))
          refine withEq e.wk.wk fun e₀ => withEq Prf.hyp0 fun e₁ => withEq Prf.hyp1 fun e₂ => ?_
          apply deriveNat; ipra_simps; rw [e₁, e₂] at e₀; linear_combination e₀
        exact .andI (chi_of e' (Prf.andE₁ hg)) (Prf.andE₂ hg)
      · exact even_odd_absurd _ (num 12 * (G * G) * H + num 6 * (G * G))
          (num 4 * (G * G * G) + num 4 * (H * H * H) + num 6 * (H * H) + num 3 * H) e.wk.wk
          (by par_ring) (by par_ring)
    · refine .orE (even_or_odd A) ?_ ?_
      · exact even_odd_absurd _ (num 12 * (G * G) * H + num 12 * G * H + num 3 * H)
          (num 4 * (G * G * G) + num 6 * (G * G) + num 3 * G + num 4 * (H * H * H)) e.wk.wk
          (by par_ring) (by par_ring)
      · exact odd_even_absurd _ (num 12 * (G * G) * H + num 6 * (G * G) + num 12 * G * H
            + num 6 * G + num 3 * H + num 1)
          (num 4 * (G * G * G) + num 6 * (G * G) + num 3 * G + num 4 * (H * H * H)
            + num 6 * (H * H) + num 3 * H + num 1) e.wk.wk (by par_ring) (by par_ring)

/-- `3cb² = c³ + b³ → b = 0`. -/
abbrev nonposFormula : Fm PTm 2 := (L₂ A B ≐ R₂ A B) ⟶ (B ≐ zero)

theorem nonpos_root : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 nonposFormula := by
  refine closeUniv 2 (.impI ?_)
  refine .orE (zero_or_succ B) Prf.hyp0 ?_
  have h := Descent.descent hyps₂
  rw [inst2_χ₂] at h
  exact .botE _ (h.trans (by
    intro ψ hψ; simp only [List.mem_singleton] at hψ; subst hψ
    exact chi_of Prf.hyp1 Prf.hyp0))

end Nonpos

end LeanProofs.IPRA.Algebra.TrisectionCubic
