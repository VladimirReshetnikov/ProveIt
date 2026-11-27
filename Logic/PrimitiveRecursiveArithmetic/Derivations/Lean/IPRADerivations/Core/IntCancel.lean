import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# Cancellation of a nonzero integer factor

`X ≠ 0 → X K = 0 → K = 0` for integer terms (`ZT`). The ring of differences of `Q Γ` need not
be a domain, so cancellation is proved in the object theory: with `X = a - b` and `a ≠ b`,
one of `a = b + δ`, `b = a + δ` holds with `δ ≥ 1`, and `δ (c - e) = 0` gives `δ c = δ e`,
hence `c = e` (`mul_cancel`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem cancel_case {X K : ZT n} {δ : PTm n} (hδ : Γ ⊢[PRAAx] δ ≐ succ (pred δ))
    (hX : Γ ⊢[PRAAx] X.pos ≐ X.neg + δ ⋎ (X.neg ≐ X.pos + δ)) (h : Γ ⊢[PRAAx] ZT.eq (X * K) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) := by

  refine .orE hX ?_ ?_
  · have h₁ := natEq (Prf.hyp0 : ((X.pos ≐ X.neg + δ) :: Γ) ⊢[PRAAx] _)
    have e' : ((X.pos ≐ X.neg + δ) :: Γ) ⊢[PRAAx] δ * K.pos ≐ δ * K.neg := by
      have h₂ := ZT.toZ_eq (h.wk (ψ := X.pos ≐ X.neg + δ))
      apply deriveNat
      simp only [ZT.toZ_mul, ZT.toZ_natLit] at h₂
      simp only [ZT.toZ] at h₂
      ipra_simps
      try simp only [Nat.cast_zero, sub_zero] at *
      linear_combination h₂ - (Groth.ι (Q.mk _ K.pos) - Groth.ι (Q.mk _ K.neg)) * h₁
    apply ZT.derive
    have h₃ := natEq (mul_cancel hδ.wk e')
    simp only [ZT.toZ, ZT.natLit, ZT.ofNat]; ipra_simps
    try simp only [Nat.cast_zero, sub_zero] at *
    linear_combination h₃
  · have h₁ := natEq (Prf.hyp0 : ((X.neg ≐ X.pos + δ) :: Γ) ⊢[PRAAx] _)
    have e' : ((X.neg ≐ X.pos + δ) :: Γ) ⊢[PRAAx] δ * K.pos ≐ δ * K.neg := by
      have h₂ := ZT.toZ_eq (h.wk (ψ := X.neg ≐ X.pos + δ))
      apply deriveNat
      simp only [ZT.toZ_mul, ZT.toZ_natLit] at h₂
      simp only [ZT.toZ] at h₂
      ipra_simps
      try simp only [Nat.cast_zero, sub_zero] at *
      linear_combination -h₂ - (Groth.ι (Q.mk _ K.pos) - Groth.ι (Q.mk _ K.neg)) * h₁
    apply ZT.derive
    have h₃ := natEq (mul_cancel hδ.wk e')
    simp only [ZT.toZ, ZT.natLit, ZT.ofNat]; ipra_simps
    try simp only [Nat.cast_zero, sub_zero] at *
    linear_combination h₃

/-- `X ≠ 0 → X K = 0 → K = 0`. -/
theorem zt_mul_cancel_left {X K : ZT n} (hX : Γ ⊢[PRAAx] neg (ZT.eq X (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (X * K) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) := by
  refine .orE (lt_or_le X.neg X.pos) ?_ ?_
  · -- `a = b + S d`.
    have w := eq_add_of_le (Prf.hyp0 : (lt X.neg X.pos :: Γ) ⊢[PRAAx] le (succ X.neg) X.pos)
    refine cancel_case (δ := succ (monus X.pos (succ X.neg))) (congrSucc (pred_succ _).eqSymm)
      (.orI₁ (w.eqTrans (by ipra_ring))) h.wk
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · have w := eq_add_of_le (Prf.hyp0 : (lt X.pos X.neg :: le X.pos X.neg :: Γ) ⊢[PRAAx] le (succ X.pos) X.neg)
      refine cancel_case (δ := succ (monus X.neg (succ X.pos))) (congrSucc (pred_succ _).eqSymm)
        (.orI₂ (w.eqTrans (by ipra_ring))) h.wk.wk
    · refine .botE _ (.impE hX.wk.wk ?_)
      apply ZT.derive
      have h₁ := natEq (Prf.hyp0 : ((X.pos ≐ X.neg) :: le X.pos X.neg :: Γ) ⊢[PRAAx] _)
      simp only [ZT.toZ, ZT.natLit, ZT.ofNat]; ipra_simps
      try simp only [Nat.cast_zero, sub_zero] at *
      linear_combination h₁

/-- `X ≠ Y → (X - Y) K = 0 → K = 0`. -/
theorem zt_mul_cancel_sub {X Y K : ZT n} (hXY : Γ ⊢[PRAAx] neg (ZT.eq X Y))
    (h : Γ ⊢[PRAAx] ZT.eq ((X - Y) * K) (ZT.natLit 0)) : Γ ⊢[PRAAx] ZT.eq K (ZT.natLit 0) := by
  refine zt_mul_cancel_left (.impI (.impE hXY.wk ?_)) h
  ipra_lc ZT.toZ_eq (Prf.hyp0 : (ZT.eq (X - Y) (ZT.natLit 0) :: Γ) ⊢[PRAAx] _)

/-- A positive natural term embedded as an integer is nonzero. -/
theorem zt_ofNat_nonzero {d : PTm n} (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat d) (ZT.natLit 0)) := by
  refine .impI ?_
  have equal : (ZT.eq (ZT.ofNat d) (ZT.natLit 0) :: Γ) ⊢[PRAAx] d ≐ zero :=
    (add_zero d).eqSymm.eqTrans (Prf.hyp0.eqTrans (add_zero zero))
  exact lt_zero_absurd _ (le_congr (.eqRefl _) equal hd.wk)

/-- Cancel a positive natural factor in an equality of integer terms. -/
theorem zt_mul_eq_cancel_nat_left {d : PTm n} {x y : ZT n} (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat d * x) (ZT.ofNat d * y)) : Γ ⊢[PRAAx] ZT.eq x y := by
  have value := ZT.toZ_eq h
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at value
  have scaled : Γ ⊢[PRAAx] d * (x.pos + y.neg) ≐ d * (y.pos + x.neg) := by
    apply deriveNat
    simp only [ZT.toZ] at value
    ipra_simps
    linear_combination value
  exact mul_eq_cancel_at (Common.pos_of_one_le hd) scaled

/-- Cancel a nonzero integer factor in an equality of integer terms. -/
theorem zt_mul_eq_cancel_left {r x y : ZT n} (hr : Γ ⊢[PRAAx] neg (ZT.eq r (ZT.natLit 0)))
    (h : Γ ⊢[PRAAx] ZT.eq (r * x) (r * y)) : Γ ⊢[PRAAx] ZT.eq x y := by
  have product : Γ ⊢[PRAAx] ZT.eq (r * (x - y)) (ZT.natLit 0) := by
    ipra_lc ZT.toZ_eq h
  ipra_lc ZT.toZ_eq (zt_mul_cancel_left hr product)

end LeanProofs.IPRA
