import IPRADerivations.Analysis.PolynomialRootName

/-!
# Quantitative uniqueness from an actual polynomial factor guard

Packet `foundations/fiber_ipra_2026-11-16`, Section 7.7. For the fixed
polynomial degree `d+1`, the computed factor has denominator
`C * (da*db)^d`. The rational lower bound `m/M` is therefore the object
inequality `m*C*(da*db)^d ≤ M*polynomialFactor`.

The finite separation theorem derives a cross-distance bound from this guard
and the two actual polynomial residuals. Subsequent name endpoints retain
explicit regularity, interval-membership and residual-schedule contracts.
Their conclusion is a finite-query agreement estimate in ordinary iPRA.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PolynomialRootUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialBisection
open LeanProofs.IPRA.Analysis.PolynomialRootName
  (abs_mul abs_scale signed_le_abs naturalPower_product)
open LeanProofs.IPRA.Analysis.RationalSummableTails (cross cross_triangle)
open LeanProofs.IPRA.Analysis.RationalClosure (succ_le_two_pow)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri zabs_neg subst_zabs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem cancel_positive {c a b : PTm n} (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] le (c * a) (c * b)) : Γ ⊢[PRAAx] le a b := by
  have ce : Γ ⊢[PRAAx] c ≐ succ (monus c one) :=
    (eq_add_of_le hc).eqTrans (by ipra_ring)
  exact mul_le_cancel (le_congr (congrMul ce (.eqRefl _)) (congrMul ce (.eqRefl _)) h)

/-- Actual denominator-cleared residual at one rational sample. -/
def residual (degree : ℕ) (code C T : PTm n) (a : ZT n) (da : PTm n) : Fm PTm n :=
  le (T * zabs (evaluate degree code a da)) (C * naturalPower da degree)

/-- The source's positive factor margin, using the actual computed divided difference. -/
def factorLower (d : ℕ) (code C m M : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) : Fm PTm n :=
  zle (ZT.ofNat (m * C * naturalPower (da * db) d))
    (ZT.ofNat M * polynomialFactor (d + 1) code a da b db)

/-- Polynomial differences are bounded by the actual weighted endpoint residuals. -/
theorem factor_error_bound (degree : ℕ) (code : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    Γ ⊢[PRAAx] le
      (zabs (polynomialFactor degree code a da b db * cross a b da db))
      (naturalPower da degree * zabs (evaluate degree code b db) +
        naturalPower db degree * zabs (evaluate degree code a da)) := by
  have factor := ZT.toZ_eq (factor_identity (Γ := Γ) degree code a da b db)
  have identity :
      ZT.toZ Γ (polynomialFactor degree code a da b db * cross a b da db) =
        ZT.toZ Γ (ZT.ofNat (naturalPower da degree) * evaluate degree code b db) +
        ZT.toZ Γ (-(ZT.ofNat (naturalPower db degree) * evaluate degree code a da)) := by
    simp only [cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_neg] at factor ⊢
    linear_combination -factor
  exact le_congr (.eqRefl _)
    (congrAdd (abs_scale _ _) ((zabs_neg _).eqTrans (abs_scale _ _))) (zabs_tri identity)

private theorem residual_power_algebra (d : ℕ) (C M da db : PTm n) :
    Γ ⊢[PRAAx]
      M * (naturalPower da (d + 1) * (C * naturalPower db (d + 1)) +
        naturalPower db (d + 1) * (C * naturalPower da (d + 1))) ≐
      (C * naturalPower (da * db) d) * (two * M * da * db) := by
  change Γ ⊢[PRAAx]
    M * ((naturalPower da d * da) * (C * (naturalPower db d * db)) +
      (naturalPower db d * db) * (C * (naturalPower da d * da))) ≐
      (C * naturalPower (da * db) d) * (two * M * da * db)
  have product := natEq (naturalPower_product (Γ := Γ) da db d)
  apply deriveNat
  ipra_simps
  rw [product]
  ring

/-- Approximate polynomial zeros are quantitatively close under the actual
factor lower bound. The shared rational error is `1/T`.
Every cancelled factor is proved positive in the object theory. -/
theorem approximate_zero_distance (d : ℕ) (code C m M T : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hda : Γ ⊢[PRAAx] le one da) (hdb : Γ ⊢[PRAAx] le one db)
    (hGuard : Γ ⊢[PRAAx] factorLower d code C m M a da b db)
    (ha : Γ ⊢[PRAAx] residual (d + 1) code C T a da)
    (hb : Γ ⊢[PRAAx] residual (d + 1) code C T b db) :
    Γ ⊢[PRAAx] le (m * T * zabs (cross a b da db)) (two * M * da * db) := by
  let F := polynomialFactor (d + 1) code a da b db
  let X := cross a b da db
  let P := C * naturalPower (da * db) d
  have lowerSigned := zle_trans hGuard (signed_le_abs (Γ := Γ) (ZT.ofNat M * F))
  have lowerNat : Γ ⊢[PRAAx] le (m * C * naturalPower (da * db) d) (M * zabs F) :=
    le_congr (add_zero _) ((add_zero _).eqTrans (abs_scale M F)) lowerSigned
  have productLower : Γ ⊢[PRAAx] le
      ((m * C * naturalPower (da * db) d) * zabs X) (M * zabs (F * X)) :=
    le_congr (.eqRefl _)
      ((mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) (abs_mul F X).eqSymm))
      (mul_le_mul_right (zabs X) lowerNat)
  have scaledLower : Γ ⊢[PRAAx] le (P * (m * T * zabs X)) ((M * T) * zabs (F * X)) :=
    le_congr (by dsimp only [P]; ipra_ring) (by ipra_ring) (mul_le_mul_right T productLower)
  have triangle : Γ ⊢[PRAAx] le ((M * T) * zabs (F * X))
      (M * (naturalPower da (d + 1) * (T * zabs (evaluate (d + 1) code b db)) +
        naturalPower db (d + 1) * (T * zabs (evaluate (d + 1) code a da)))) :=
    le_congr (mul_comm _ _) (by ipra_ring)
      (mul_le_mul_right (M * T) (factor_error_bound (d + 1) code a da b db))
  have endpoints : Γ ⊢[PRAAx] le
      (M * (naturalPower da (d + 1) * (T * zabs (evaluate (d + 1) code b db)) +
        naturalPower db (d + 1) * (T * zabs (evaluate (d + 1) code a da))))
      (M * (naturalPower da (d + 1) * (C * naturalPower db (d + 1)) +
        naturalPower db (d + 1) * (C * naturalPower da (d + 1)))) :=
    le_mul_mono (le_refl M) (add_le_add₂ (le_mul_mono (le_refl _) hb) (le_mul_mono (le_refl _) ha))
  have joined : Γ ⊢[PRAAx] le (P * (m * T * zabs X)) (P * (two * M * da * db)) :=
    le_trans scaledLower (le_trans triangle
      (le_congr (.eqRefl _) (residual_power_algebra d C M da db) endpoints))
  have basePositive : Γ ⊢[PRAAx] le one (da * db) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hda hdb)
  have positive : Γ ⊢[PRAAx] le one P :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hC (naturalPower_positive (da * db) d basePositive))
  exact cancel_positive positive joined

/-- All coefficients, margin/error data and signed rational points are internal. -/
def approximateFormula (d : ℕ) : Fm PTm 11 :=
  let a : ZT 11 := ⟨var 5, var 6⟩
  let b : ZT 11 := ⟨var 8, var 9⟩
  le one (var 1) ⟶ le one (var 2) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
    le one (var 7) ⟶ le one (var 10) ⟶
    factorLower d (var 0) (var 1) (var 2) (var 3) a (var 7) b (var 10) ⟶
    residual (d + 1) (var 0) (var 1) (var 4) a (var 7) ⟶
    residual (d + 1) (var 0) (var 1) (var 4) b (var 10) ⟶
    le (var 2 * var 4 * zabs (cross a b (var 7) (var 10))) (two * var 3 * var 7 * var 10)

theorem approximate_zero_closed (d : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11 (approximateFormula d) := by
  refine closeUniv 11 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))))
  exact approximate_zero_distance d (var 0) (var 1) (var 2) (var 3) (var 4)
    ⟨var 5, var 6⟩ (var 7) ⟨var 8, var 9⟩ (var 10)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

#print axioms factor_error_bound
#print axioms approximate_zero_distance
#print axioms approximate_zero_closed

private theorem one_le_two_power (k : PTm n) : Γ ⊢[PRAAx] le one (pw two k) :=
  le_trans (le_of_eq_add (d := k) (by ipra_ring)) (succ_le_two_pow k)

/-- Precision sufficient to absorb the explicit inverse margin `2M/m`. -/
def guardPrecision (N M : PTm n) : PTm n := N + succ (two * M)

theorem guard_budget (N m M : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le ((two * M) * pw two N) (m * pw two (guardPrecision N M)) := by
  let S := succ (two * M)
  have exponential : Γ ⊢[PRAAx] le (two * M) (pw two S) :=
    le_trans (le_trans (le_succ_self _) (le_succ_self _)) (succ_le_two_pow S)
  have margin : Γ ⊢[PRAAx] le (two * M) (m * pw two S) :=
    le_congr (one_mul _) (.eqRefl _) (le_mul_mono hm exponential)
  have rearrange : Γ ⊢[PRAAx] m * pw two S * pw two N ≐ m * pw two (N + S) :=
    (by ipra_ring : Γ ⊢[PRAAx] m * pw two S * pw two N ≐ m * (pw two N * pw two S)).eqTrans
      (congrMul (.eqRefl _) (pw_add two N S).eqSymm)
  exact le_congr (.eqRefl _) rearrange (mul_le_mul_right (pw two N) margin)

/-- Actual approximate zeros at the explicit guard precision are `2^-N` apart. -/
theorem dyadic_approximate_zero (d : ℕ) (code C m M N : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hda : Γ ⊢[PRAAx] le one da) (hdb : Γ ⊢[PRAAx] le one db)
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hGuard : Γ ⊢[PRAAx] factorLower d code C m M a da b db)
    (ha : Γ ⊢[PRAAx] residual (d + 1) code C (pw two (guardPrecision N M)) a da)
    (hb : Γ ⊢[PRAAx] residual (d + 1) code C (pw two (guardPrecision N M)) b db) :
    Γ ⊢[PRAAx] le (pw two N * zabs (cross a b da db)) (da * db) := by
  have separation := approximate_zero_distance d code C m M (pw two (guardPrecision N M))
    a da b db hC hda hdb hGuard ha hb
  have budget := mul_le_mul_right (zabs (cross a b da db)) (guard_budget N m M hm)
  have scaled : Γ ⊢[PRAAx] le ((two * M) * (pw two N * zabs (cross a b da db)))
      ((two * M) * (da * db)) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) budget)
      (le_congr (.eqRefl _) (mul_assoc _ _ _) separation)
  have positive : Γ ⊢[PRAAx] le one (two * M) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono (le_succ_self one) hM)
  exact cancel_positive positive scaled

/-- Two rational error estimates with a common denominator compose by addition. -/
theorem common_triangle (a b c : ZT n) (da db dc T E F : PTm n)
    (hdb : Γ ⊢[PRAAx] le one db)
    (hab : Γ ⊢[PRAAx] le (T * zabs (cross a b da db)) (E * da * db))
    (hbc : Γ ⊢[PRAAx] le (T * zabs (cross b c db dc)) (F * db * dc)) :
    Γ ⊢[PRAAx] le (T * zabs (cross a c da dc)) ((E + F) * da * dc) := by
  have triangle : Γ ⊢[PRAAx] le (db * (T * zabs (cross a c da dc)))
      (dc * (T * zabs (cross a b da db)) + da * (T * zabs (cross b c db dc))) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right T (cross_triangle a b c da db dc))
  have endpoints := add_le_add₂ (le_mul_mono (le_refl dc) hab) (le_mul_mono (le_refl da) hbc)
  have joined : Γ ⊢[PRAAx] le (db * (T * zabs (cross a c da dc))) (db * ((E + F) * da * dc)) :=
    le_trans triangle (le_congr (.eqRefl _) (by ipra_ring) endpoints)
  exact cancel_positive hdb joined

/-- The three errors used in name comparison, with all denominators independent. -/
theorem three_errors (a b c e : ZT n) (da db dc de T : PTm n)
    (hdb : Γ ⊢[PRAAx] le one db) (hdc : Γ ⊢[PRAAx] le one dc)
    (hab : Γ ⊢[PRAAx] le (T * zabs (cross a b da db)) (da * db))
    (hbc : Γ ⊢[PRAAx] le (T * zabs (cross b c db dc)) (db * dc))
    (hce : Γ ⊢[PRAAx] le (T * zabs (cross c e dc de)) (dc * de)) :
    Γ ⊢[PRAAx] le (T * zabs (cross a e da de)) (num 3 * da * de) := by
  have first := common_triangle a b c da db dc T one one hdb
    (le_congr (.eqRefl _) (by ipra_ring) hab) (le_congr (.eqRefl _) (by ipra_ring) hbc)
  have last := common_triangle a c e da dc de T (one + one) one hdc first
    (le_congr (.eqRefl _) (by ipra_ring) hce)
  exact le_congr (.eqRefl _) (by ipra_ring) last

/-- Two extra precision bits absorb the three independent comparison errors. -/
theorem absorb_three (N da db : PTm n) (X : ZT n)
    (h : Γ ⊢[PRAAx] le (pw two (succ (succ N)) * zabs X) (num 3 * da * db)) :
    Γ ⊢[PRAAx] le (pw two N * zabs X) (da * db) := by
  have power : Γ ⊢[PRAAx] pw two (succ (succ N)) ≐ num 4 * pw two N :=
    (pw_succ two (succ N)).eqTrans
      ((congrMul (pw_succ two N) (.eqRefl _)).eqTrans (by ipra_ring))
  have widened : Γ ⊢[PRAAx] le (pw two (succ (succ N)) * zabs X) (num 4 * da * db) :=
    le_trans h (le_of_eq_add (d := da * db) (by ipra_ring))
  have scaled : Γ ⊢[PRAAx] le (num 4 * (pw two N * zabs X)) (num 4 * (da * db)) :=
    le_congr ((congrMul power (.eqRefl _)).eqTrans (by ipra_ring)) (by ipra_ring) widened
  exact mul_le_cancel scaled

#print axioms dyadic_approximate_zero
#print axioms common_triangle
#print axioms three_errors
#print axioms absorb_three

@[simp] private theorem subst_one {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (one : PTm n) = one := by
  simp only [one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] private theorem subst_two {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (two : PTm n) = two := by
  simp only [two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

@[simp] private theorem subst_zle {k : ℕ} (σ : Fin n → PTm k) (u v : ZT n) :
    (zle u v).subst σ = zle (u.subst σ) (v.subst σ) := by simp [zle, ZT.subst]

@[simp] private theorem subst_zpow {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) (d : ℕ) :
    (Foundations.QuantitativeIdentities.zpow a d).subst σ =
      Foundations.QuantitativeIdentities.zpow (a.subst σ) d := by
  induction d with
  | zero => simp [Foundations.QuantitativeIdentities.zpow]
  | succ d ih => simp only [Foundations.QuantitativeIdentities.zpow, ZT.subst_mul, ih]

@[simp] private theorem subst_powerFactor {k : ℕ} (σ : Fin n → PTm k) (d : ℕ) (a b : ZT n) :
    (powerFactor d a b).subst σ = powerFactor d (a.subst σ) (b.subst σ) := by
  induction d with
  | zero => simp only [powerFactor, ZT.subst_natLit]
  | succ d ih => simp only [powerFactor, ZT.subst_add, ZT.subst_mul, subst_zpow, ih]

@[simp] private theorem subst_polynomialFactor {k : ℕ} (σ : Fin n → PTm k) (d : ℕ)
    (code : PTm n) (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    (polynomialFactor d code a da b db).subst σ =
      polynomialFactor d (Syn.subst σ code) (a.subst σ) (Syn.subst σ da) (b.subst σ) (Syn.subst σ db) := by
  induction d with
  | zero => simp only [polynomialFactor, ZT.subst_natLit]
  | succ d ih => simp only [polynomialFactor, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat,
      PTm.subst_mul, subst_coefficient, subst_powerFactor, ih]

@[simp] private theorem subst_residual {k : ℕ} (σ : Fin n → PTm k) (degree : ℕ)
    (code C T : PTm n) (a : ZT n) (da : PTm n) :
    (residual degree code C T a da).subst σ =
      residual degree (Syn.subst σ code) (Syn.subst σ C) (Syn.subst σ T) (a.subst σ) (Syn.subst σ da) := by
  simp only [residual, subst_le, subst_zabs, PTm.subst_mul, subst_evaluate, subst_naturalPower]

@[simp] private theorem subst_factorLower {k : ℕ} (σ : Fin n → PTm k) (d : ℕ)
    (code C m M : PTm n) (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    (factorLower d code C m M a da b db).subst σ =
      factorLower d (Syn.subst σ code) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ M)
        (a.subst σ) (Syn.subst σ da) (b.subst σ) (Syn.subst σ db) := by
  simp only [factorLower, subst_zle, ZT.subst_ofNat, ZT.subst_mul, PTm.subst_mul,
    subst_naturalPower, subst_polynomialFactor]

/-- An encoded rational point lies in the supplied rational interval. -/
def pointDomain (initial s : PTm n) : Fm PTm n :=
  le one (denominator s) ⋏
    zle (left initial * ZT.ofNat (denominator s)) (left s * ZT.ofNat (denominator initial)) ⋏
    zle (left s * ZT.ofNat (denominator initial)) (right initial * ZT.ofNat (denominator s))

@[simp] theorem subst_pointDomain {k : ℕ} (σ : Fin n → PTm k) (initial s : PTm n) :
    (pointDomain initial s).subst σ = pointDomain (Syn.subst σ initial) (Syn.subst σ s) := by
  simp only [pointDomain, Fm.subst_and, subst_zle, ZT.subst_mul, ZT.subst_ofNat,
    subst_left, subst_right, subst_denominator]
  simp only [subst_le, subst_one, subst_denominator]

/-- Uniform source guard throughout the interval, with the actual computed factor. -/
def uniformGuard (d : ℕ) (code C initial m M : PTm n) : Fm PTm n :=
  .all (.all (
    pointDomain (Syn.shift (Syn.shift initial)) (var 1) ⟶
    pointDomain (Syn.shift (Syn.shift initial)) (var 0) ⟶
    factorLower d (Syn.shift (Syn.shift code)) (Syn.shift (Syn.shift C))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift M))
      (left (var 1)) (denominator (var 1)) (left (var 0)) (denominator (var 0))))

theorem uniformGuard_at (d : ℕ) (code C initial m M s t : PTm n)
    (h : Γ ⊢[PRAAx] uniformGuard d code C initial m M)
    (hs : Γ ⊢[PRAAx] pointDomain initial s) (ht : Γ ⊢[PRAAx] pointDomain initial t) :
    Γ ⊢[PRAAx] factorLower d code C m M (left s) (denominator s) (left t) (denominator t) := by
  have inst := Prf.allE t (Prf.allE s h)
  have body : Γ ⊢[PRAAx] pointDomain initial s ⟶ pointDomain initial t ⟶
      factorLower d code C m M (left s) (denominator s) (left t) (denominator t) := by
    simpa [uniformGuard, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using inst
  exact Prf.impE (Prf.impE body hs) ht

def difference (s t : PTm n) : ZT n := cross (left s) (left t) (denominator s) (denominator t)

@[simp] private theorem subst_difference {k : ℕ} (σ : Fin n → PTm k) (s t : PTm n) :
    (difference s t).subst σ = difference (Syn.subst σ s) (Syn.subst σ t) := by
  simp only [difference, RationalSummableTails.subst_cross, subst_left, subst_denominator]

theorem difference_symm (s t : PTm n) :
    Γ ⊢[PRAAx] zabs (difference s t) ≐ zabs (difference t s) := by
  have opposite : ZT.toZ Γ (difference s t) = ZT.toZ Γ (-(difference t s)) := by
    simp only [difference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg]
    ring
  exact (zabs_congr opposite).eqTrans (zabs_neg _)

/-- Each actual PR sample is a positive-denominator point in the interval. -/
def covered (A : PR 2) (initial x : PTm n) : Fm PTm n :=
  .all (pointDomain (Syn.shift initial) (ap2 A (var 0) (Syn.shift x)))

theorem covered_at (A : PR 2) (initial x k : PTm n) (h : Γ ⊢[PRAAx] covered A initial x) :
    Γ ⊢[PRAAx] pointDomain initial (ap2 A k x) := by
  simpa only [covered, subst_pointDomain, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] using Prf.allE k h

/-- Regularity of one input name, separate from agreement of the two names. -/
def regularAt (A : PR 2) (x N K : PTm n) : Fm PTm n :=
  le N K ⟶ le (pw two N * zabs (difference (ap2 A N x) (ap2 A K x)))
    (denominator (ap2 A N x) * denominator (ap2 A K x))

@[simp] private theorem subst_regularAt {k : ℕ} (σ : Fin n → PTm k) (A : PR 2) (x N K : PTm n) :
    (regularAt A x N K).subst σ = regularAt A (Syn.subst σ x) (Syn.subst σ N) (Syn.subst σ K) := by
  simp only [regularAt, Fm.subst_imp, subst_le, subst_zabs, PTm.subst_mul,
    subst_difference, subst_ap2, subst_two, subst_denominator]

def regularContract (A : PR 2) (x : PTm n) : Fm PTm n :=
  .all (.all (regularAt A (Syn.shift (Syn.shift x)) (var 1) (var 0)))

theorem regular_at (A : PR 2) (x N K : PTm n) (h : Γ ⊢[PRAAx] regularContract A x)
    (order : Γ ⊢[PRAAx] le N K) :
    Γ ⊢[PRAAx] le (pw two N * zabs (difference (ap2 A N x) (ap2 A K x)))
      (denominator (ap2 A N x) * denominator (ap2 A K x)) := by
  have inst := Prf.allE K (Prf.allE N h)
  have body : Γ ⊢[PRAAx] regularAt A x N K := by
    simpa [regularContract, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using inst
  exact Prf.impE body order

def pointResidual (degree : ℕ) (code C T s : PTm n) : Fm PTm n :=
  residual degree code C T (left s) (denominator s)

@[simp] private theorem subst_pointResidual {k : ℕ} (σ : Fin n → PTm k) (degree : ℕ) (code C T s : PTm n) :
    (pointResidual degree code C T s).subst σ =
      pointResidual degree (Syn.subst σ code) (Syn.subst σ C) (Syn.subst σ T) (Syn.subst σ s) := by
  simp only [pointResidual, subst_residual, subst_left, subst_denominator]

/-- The actual residual queries refine precision and make polynomial errors vanish. -/
def vanishing (degree : ℕ) (A μ : PR 2) (code C x : PTm n) : Fm PTm n :=
  .all (le (var 0) (ap2 μ (var 0) (Syn.shift x)) ⋏
    pointResidual degree (Syn.shift code) (Syn.shift C) (pw two (var 0))
      (ap2 A (ap2 μ (var 0) (Syn.shift x)) (Syn.shift x)))

theorem vanishing_at (degree : ℕ) (A μ : PR 2) (code C x K : PTm n)
    (h : Γ ⊢[PRAAx] vanishing degree A μ code C x) :
    Γ ⊢[PRAAx] le K (ap2 μ K x) ⋏
      pointResidual degree code C (pw two K) (ap2 A (ap2 μ K x) x) := by
  simpa only [vanishing, Fm.subst_and, subst_le, subst_pointResidual, subst_ap2,
    subst_two, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE K h

/-- Finite-query equivalence of the two names, with the explicit two-bit shift. -/
def agreement (A B : PR 2) (N x : PTm n) : Fm PTm n :=
  le (pw two N * zabs (difference (ap2 A (succ (succ N)) x) (ap2 B (succ (succ N)) x)))
    (denominator (ap2 A (succ (succ N)) x) * denominator (ap2 B (succ (succ N)) x))

/-- Two regular polynomial-root names in the guarded interval agree. The
three comparison errors are derived from their own moduli and residuals. -/
theorem name_agreement_at (d : ℕ) (A B μ ν : PR 2) (N x code C initial m M : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hGuard : Γ ⊢[PRAAx] uniformGuard d code C initial m M)
    (hInA : Γ ⊢[PRAAx] covered A initial x) (hInB : Γ ⊢[PRAAx] covered B initial x)
    (hRegA : Γ ⊢[PRAAx] regularContract A x) (hRegB : Γ ⊢[PRAAx] regularContract B x)
    (hResA : Γ ⊢[PRAAx] vanishing (d + 1) A μ code C x)
    (hResB : Γ ⊢[PRAAx] vanishing (d + 1) B ν code C x) :
    Γ ⊢[PRAAx] agreement A B N x := by
  let i := succ (succ N)
  let K := guardPrecision i M
  let a := ap2 A i x
  let b := ap2 A (ap2 μ K x) x
  let c := ap2 B (ap2 ν K x) x
  let e := ap2 B i x
  have ra := vanishing_at (d + 1) A μ code C x K hResA
  have rb := vanishing_at (d + 1) B ν code C x K hResB
  have db := covered_at A initial x (ap2 μ K x) hInA
  have dc := covered_at B initial x (ap2 ν K x) hInB
  have guard := uniformGuard_at d code C initial m M b c hGuard db dc
  have root := dyadic_approximate_zero d code C m M i (left b) (denominator b) (left c) (denominator c)
    hC (Prf.andE₁ db) (Prf.andE₁ dc) hm hM guard (Prf.andE₂ ra) (Prf.andE₂ rb)
  have ia : Γ ⊢[PRAAx] le i (ap2 μ K x) := le_trans (le_add_right _ _) (Prf.andE₁ ra)
  have ib : Γ ⊢[PRAAx] le i (ap2 ν K x) := le_trans (le_add_right _ _) (Prf.andE₁ rb)
  have first := regular_at A x i (ap2 μ K x) hRegA ia
  have lastForward := regular_at B x i (ap2 ν K x) hRegB ib
  have last : Γ ⊢[PRAAx] le (pw two i * zabs (difference c e)) (denominator c * denominator e) :=
    le_congr (congrMul (.eqRefl _) (difference_symm e c)) (mul_comm _ _) lastForward
  have all := three_errors (left a) (left b) (left c) (left e)
    (denominator a) (denominator b) (denominator c) (denominator e) (pw two i)
    (Prf.andE₁ db) (Prf.andE₁ dc) first root last
  exact absorb_three N (denominator a) (denominator e) (difference a e) all

/-- All seven data variables are object-language naturals; name programs and
the fixed polynomial degree are external schema parameters. -/
def namesFormula (d : ℕ) (A B μ ν : PR 2) : Fm PTm 7 :=
  le one (denominator (var 4)) ⟶ zle (left (var 4)) (right (var 4)) ⟶
    le one (var 3) ⟶ le one (var 5) ⟶ le one (var 6) ⟶
    uniformGuard d (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
    covered A (var 4) (var 1) ⟶ covered B (var 4) (var 1) ⟶
    regularContract A (var 1) ⟶ regularContract B (var 1) ⟶
    vanishing (d + 1) A μ (var 2) (var 3) (var 1) ⟶
    vanishing (d + 1) B ν (var 2) (var 3) (var 1) ⟶ agreement A B (var 0) (var 1)

theorem names_unique (d : ℕ) (A B μ ν : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 (namesFormula d A B μ ν) := by
  refine closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))))))))
  exact name_agreement_at d A B μ ν (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp))

#print axioms uniformGuard_at
#print axioms name_agreement_at
#print axioms names_unique

private theorem left_value_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    ZT.toZ Γ (left s) = ZT.toZ Γ (left t) := by
  simp only [left, unpack, ZT.toZ]
  rw [natEq (congrFst (congrFst h)), natEq (congrSnd (congrFst h))]

private theorem denominator_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] denominator s ≐ denominator t := congrSnd (congrSnd h)

theorem difference_congr {s s' t t' : PTm n}
    (hs : Γ ⊢[PRAAx] s ≐ s') (ht : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] zabs (difference s t) ≐ zabs (difference s' t') := by
  apply zabs_congr
  simp only [difference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]
  rw [left_value_congr hs, left_value_congr ht, natEq (denominator_congr hs), natEq (denominator_congr ht)]

theorem pointDomain_congr (initial : PTm n) {s t : PTm n}
    (hst : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] pointDomain initial s) :
    Γ ⊢[PRAAx] pointDomain initial t := by
  have source : Γ ⊢[PRAAx] (pointDomain (Syn.shift initial) (var 0)).subst (Syn.inst s) := by
    simpa only [subst_pointDomain, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h
  have target := Prf.eqSubst (pointDomain (Syn.shift initial) (var 0)) (Syn.inst s) (Syn.inst t)
    (fun i => Fin.cases hst (fun _ => .eqRefl _) i) source
  simpa only [subst_pointDomain, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using target

theorem pointResidual_congr (degree : ℕ) (code C T : PTm n) {s t : PTm n}
    (hst : Γ ⊢[PRAAx] s ≐ t) (h : Γ ⊢[PRAAx] pointResidual degree code C T s) :
    Γ ⊢[PRAAx] pointResidual degree code C T t := by
  have source : Γ ⊢[PRAAx]
      (pointResidual degree (Syn.shift code) (Syn.shift C) (Syn.shift T) (var 0)).subst (Syn.inst s) := by
    simpa only [subst_pointResidual, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h
  have target := Prf.eqSubst (pointResidual degree (Syn.shift code) (Syn.shift C) (Syn.shift T) (var 0))
    (Syn.inst s) (Syn.inst t) (fun i => Fin.cases hst (fun _ => .eqRefl _) i) source
  simpa only [subst_pointResidual, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using target

/-- Explicit PR program returning the entire actual reindexed bisection state. -/
def bisectionPointF (degree : ℕ) : PR 2 :=
  PTm.toPR (PolynomialRootName.sampleState degree (var 0) (var 1))

theorem bisectionPoint_at (degree : ℕ) (k x : PTm n) :
    Γ ⊢[PRAAx] ap2 (bisectionPointF degree) k x ≐ PolynomialRootName.sampleState degree k x := by
  have h := toPR_eq (Γ := Γ) (PolynomialRootName.sampleState degree (var 0) (var 1) : PTm 2) ![k, x]
  simpa only [bisectionPointF, ap2, PolynomialRootName.subst_sampleState, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- Actual bisection samples lie in the original rational interval. -/
theorem actual_sample_domain (degree : ℕ) (k x : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible degree x) :
    Γ ⊢[PRAAx] pointDomain (PolynomialRootName.initialState x) (PolynomialRootName.sampleState degree k x) := by
  let s := PolynomialRootName.sampleState degree k x
  let initial := PolynomialRootName.initialState x
  let K := k + PolynomialRootName.offset x
  let t := pw two K
  have hb := PolynomialRootName.sample_bracket degree k x h
  have hn := run_nested degree K (PolynomialRootName.coefficientCode x) initial h
  have hd := run_denominator (Γ := Γ) degree K (PolynomialRootName.coefficientCode x) initial
  change Γ ⊢[PRAAx] denominator s ≐ denominator initial * t at hd
  have lower := zle_scale (denominator initial) (Prf.andE₁ hn)
  have upper := zle_scale (denominator initial)
    (zle_trans (Prf.andE₁ (Prf.andE₂ hb)) (Prf.andE₂ hn))
  have endpointL : ZT.toZ Γ (ZT.ofNat (denominator initial) * (ZT.ofNat t * left initial)) =
      ZT.toZ Γ (left initial * ZT.ofNat (denominator s)) := by
    simp only [ZT.toZ_mul, ZT.toZ_ofNat]
    rw [natEq hd]
    simp only [Q.mk_mul, map_mul]
    ring
  have endpointR : ZT.toZ Γ (ZT.ofNat (denominator initial) * (ZT.ofNat t * right initial)) =
      ZT.toZ Γ (right initial * ZT.ofNat (denominator s)) := by
    simp only [ZT.toZ_mul, ZT.toZ_ofNat]
    rw [natEq hd]
    simp only [Q.mk_mul, map_mul]
    ring
  have middle : ZT.toZ Γ (ZT.ofNat (denominator initial) * left s) =
      ZT.toZ Γ (left s * ZT.ofNat (denominator initial)) := by
    simp only [ZT.toZ_mul]
    ring
  exact .andI (Prf.andE₁ hb) (.andI (zle_congr endpointL middle lower) (zle_congr middle endpointR upper))

theorem bisection_covered (degree : ℕ) (x : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible degree x) :
    Γ ⊢[PRAAx] covered (bisectionPointF degree) (PolynomialRootName.initialState x) x := by
  apply Prf.allI
  have shifted : Γ.map Fm.shift ⊢[PRAAx] PolynomialRootName.admissible degree (Syn.shift x) := by
    simpa only [Fm.shift, PolynomialRootName.subst_admissible, Syn.shift] using h.shift
  have actual := actual_sample_domain degree (var 0) (Syn.shift x) shifted
  have result := pointDomain_congr _ (bisectionPoint_at degree (var 0) (Syn.shift x)).eqSymm actual
  simpa only [Syn.shift, PolynomialRootName.subst_initialState] using result

theorem bisection_regular_at (degree : ℕ) (x N K : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible degree x) (order : Γ ⊢[PRAAx] le N K) :
    Γ ⊢[PRAAx] le (pw two N * zabs (difference (ap2 (bisectionPointF degree) N x) (ap2 (bisectionPointF degree) K x)))
      (denominator (ap2 (bisectionPointF degree) N x) * denominator (ap2 (bisectionPointF degree) K x)) := by
  have first := bisectionPoint_at (Γ := Γ) degree N x
  have second := bisectionPoint_at (Γ := Γ) degree K x
  have actual := PolynomialRootName.regular_between degree x h order
  exact le_congr (congrMul (.eqRefl _) (difference_congr first second).eqSymm)
    (congrMul (denominator_congr first).eqSymm (denominator_congr second).eqSymm) actual

theorem bisection_regular (degree : ℕ) (x : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible degree x) :
    Γ ⊢[PRAAx] regularContract (bisectionPointF degree) x := by
  refine .allI (.allI (.impI ?_))
  have shifted : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      PolynomialRootName.admissible degree (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift, PolynomialRootName.subst_admissible, Syn.shift] using h.shift.shift
  exact bisection_regular_at degree (Syn.shift (Syn.shift x)) (var 1) (var 0) shifted.wk Prf.hyp0

/-- Both regularity and residual convergence of the canonical input are proved
from its initial sign bracket and coefficient-denominator positivity. -/
theorem bisection_vanishing (degree : ℕ) (x : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible degree x)
    (hC : Γ ⊢[PRAAx] le one (PolynomialRootName.coefficientDenominator x)) :
    Γ ⊢[PRAAx] vanishing degree (bisectionPointF degree) (PolynomialRootName.residualScheduleF degree)
      (PolynomialRootName.coefficientCode x) (PolynomialRootName.coefficientDenominator x) x := by
  apply Prf.allI
  have shifted : Γ.map Fm.shift ⊢[PRAAx] PolynomialRootName.admissible degree (Syn.shift x) := by
    simpa only [Fm.shift, PolynomialRootName.subst_admissible, Syn.shift] using h.shift
  have positive : Γ.map Fm.shift ⊢[PRAAx] le one (PolynomialRootName.coefficientDenominator (Syn.shift x)) := by
    simpa only [Fm.shift, subst_le, subst_one, PolynomialRootName.subst_coefficientDenominator, Syn.shift] using hC.shift
  let μ := ap2 (PolynomialRootName.residualScheduleF degree) (var 0) (Syn.shift x)
  have actual : Γ.map Fm.shift ⊢[PRAAx] pointResidual degree
      (PolynomialRootName.coefficientCode (Syn.shift x)) (PolynomialRootName.coefficientDenominator (Syn.shift x))
      (pw two (var 0)) (PolynomialRootName.sampleState degree μ (Syn.shift x)) := by
    simpa only [pointResidual, residual, PolynomialRootName.residualAt,
      PolynomialRootName.sampleNumerator, PolynomialRootName.sampleDenominator, evaluationDenominator] using
      PolynomialRootName.residual_program_at degree (var 0) (Syn.shift x) shifted positive
  have output := pointResidual_congr degree _ _ _ (bisectionPoint_at degree μ (Syn.shift x)).eqSymm actual
  have result := Prf.andI (PolynomialRootName.residualProgram_ge (Γ := Γ.map Fm.shift) degree (var 0) (Syn.shift x)) output
  simpa only [μ, Syn.shift, PolynomialRootName.subst_coefficientCode,
    PolynomialRootName.subst_coefficientDenominator] using result

/-- The actual bisection root name agrees with any other compatible regular
root name under the source's uniform factor margin. -/
theorem bisection_agreement_at (d : ℕ) (B ν : PR 2) (N x m M : PTm n)
    (h : Γ ⊢[PRAAx] PolynomialRootName.admissible (d + 1) x)
    (hC : Γ ⊢[PRAAx] le one (PolynomialRootName.coefficientDenominator x))
    (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hGuard : Γ ⊢[PRAAx] uniformGuard d (PolynomialRootName.coefficientCode x)
      (PolynomialRootName.coefficientDenominator x) (PolynomialRootName.initialState x) m M)
    (hInB : Γ ⊢[PRAAx] covered B (PolynomialRootName.initialState x) x)
    (hRegB : Γ ⊢[PRAAx] regularContract B x)
    (hResB : Γ ⊢[PRAAx] vanishing (d + 1) B ν (PolynomialRootName.coefficientCode x)
      (PolynomialRootName.coefficientDenominator x) x) :
    Γ ⊢[PRAAx] agreement (bisectionPointF (d + 1)) B N x :=
  name_agreement_at d (bisectionPointF (d + 1)) B (PolynomialRootName.residualScheduleF (d + 1)) ν
    N x (PolynomialRootName.coefficientCode x) (PolynomialRootName.coefficientDenominator x)
    (PolynomialRootName.initialState x) m M hC hm hM hGuard
    (bisection_covered (d + 1) x h) hInB (bisection_regular (d + 1) x h) hRegB
    (bisection_vanishing (d + 1) x h hC) hResB

def bisectionFormula (d : ℕ) (B ν : PR 2) : Fm PTm 4 :=
  PolynomialRootName.admissible (d + 1) (var 1) ⟶
    le one (PolynomialRootName.coefficientDenominator (var 1)) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
    uniformGuard d (PolynomialRootName.coefficientCode (var 1)) (PolynomialRootName.coefficientDenominator (var 1))
      (PolynomialRootName.initialState (var 1)) (var 2) (var 3) ⟶
    covered B (PolynomialRootName.initialState (var 1)) (var 1) ⟶ regularContract B (var 1) ⟶
    vanishing (d + 1) B ν (PolynomialRootName.coefficientCode (var 1))
      (PolynomialRootName.coefficientDenominator (var 1)) (var 1) ⟶
    agreement (bisectionPointF (d + 1)) B (var 0) (var 1)

theorem bisection_root_unique (d : ℕ) (B ν : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (bisectionFormula d B ν) := by
  refine closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))))
  exact bisection_agreement_at d B ν (var 0) (var 1) (var 2) (var 3)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

#print axioms actual_sample_domain
#print axioms bisection_covered
#print axioms bisection_regular
#print axioms bisection_vanishing
#print axioms bisection_root_unique

/-- Canonical factor margin for any fixed degree. The constant case has the
computed zero factor, rather than an artificial positive diagonal value. -/
def coefficientGuard (degree : ℕ) (code C m M : PTm n)
    (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) : Fm PTm n :=
  zle (ZT.ofNat (m * C * naturalPower (da * db) (degree - 1)))
    (ZT.ofNat M * polynomialFactor degree code a da b db)

@[simp] private theorem subst_coefficientGuard {k : ℕ} (σ : Fin n → PTm k) (degree : ℕ)
    (code C m M : PTm n) (a : ZT n) (da : PTm n) (b : ZT n) (db : PTm n) :
    (coefficientGuard degree code C m M a da b db).subst σ =
      coefficientGuard degree (Syn.subst σ code) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ M)
        (a.subst σ) (Syn.subst σ da) (b.subst σ) (Syn.subst σ db) := by
  simp only [coefficientGuard, subst_zle, ZT.subst_ofNat, ZT.subst_mul, PTm.subst_mul,
    subst_naturalPower, subst_polynomialFactor]

def uniformPolynomialGuard (degree : ℕ) (code C initial m M : PTm n) : Fm PTm n :=
  .all (.all (
    pointDomain (Syn.shift (Syn.shift initial)) (var 1) ⟶
    pointDomain (Syn.shift (Syn.shift initial)) (var 0) ⟶
    coefficientGuard degree (Syn.shift (Syn.shift code)) (Syn.shift (Syn.shift C))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift M))
      (left (var 1)) (denominator (var 1)) (left (var 0)) (denominator (var 0))))

theorem uniformPolynomialGuard_at (degree : ℕ) (code C initial m M s t : PTm n)
    (h : Γ ⊢[PRAAx] uniformPolynomialGuard degree code C initial m M)
    (hs : Γ ⊢[PRAAx] pointDomain initial s) (ht : Γ ⊢[PRAAx] pointDomain initial t) :
    Γ ⊢[PRAAx] coefficientGuard degree code C m M (left s) (denominator s) (left t) (denominator t) := by
  have inst := Prf.allE t (Prf.allE s h)
  have body : Γ ⊢[PRAAx] pointDomain initial s ⟶ pointDomain initial t ⟶
      coefficientGuard degree code C m M (left s) (denominator s) (left t) (denominator t) := by
    simpa [uniformPolynomialGuard, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using inst
  exact Prf.impE (Prf.impE body hs) ht

/-- A constant polynomial has zero canonical divided difference, so a strictly
positive canonical margin is inconsistent on any supplied interval point. -/
theorem constant_guard_impossible (code C initial m M s : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hm : Γ ⊢[PRAAx] le one m)
    (hGuard : Γ ⊢[PRAAx] uniformPolynomialGuard 0 code C initial m M)
    (hs : Γ ⊢[PRAAx] pointDomain initial s) : Γ ⊢[PRAAx] Fm.bot := by
  have h := uniformPolynomialGuard_at 0 code C initial m M s s hGuard hs hs
  have zero : Γ ⊢[PRAAx] zle (ZT.ofNat (m * C)) (ZT.natLit 0) := by
    apply zle_congr _ _ h
    · change ZT.toZ Γ (ZT.ofNat (m * C * one)) = ZT.toZ Γ (ZT.ofNat (m * C))
      simp only [ZT.toZ_ofNat, Q.mk_mul, map_mul, Q.mk_one, map_one]
      ring
    · simp only [polynomialFactor, ZT.toZ_mul, ZT.toZ_natLit]
      ring
  have lower : Γ ⊢[PRAAx] le one (m * C) :=
    le_congr (one_mul one) (.eqRefl _) (le_mul_mono hm hC)
  have upper : Γ ⊢[PRAAx] le (m * C) ConciseIPRA.PTm.zero :=
    le_congr (add_zero _) (add_zero _) zero
  exact not_succ_le_self ConciseIPRA.PTm.zero _ (le_trans lower upper)

/-- All fixed degrees, including the constant case under its actual canonical guard. -/
theorem polynomial_names_agree_at (degree : ℕ) (A B μ ν : PR 2) (N x code C initial m M : PTm n)
    (hC : Γ ⊢[PRAAx] le one C) (hm : Γ ⊢[PRAAx] le one m) (hM : Γ ⊢[PRAAx] le one M)
    (hGuard : Γ ⊢[PRAAx] uniformPolynomialGuard degree code C initial m M)
    (hInA : Γ ⊢[PRAAx] covered A initial x) (hInB : Γ ⊢[PRAAx] covered B initial x)
    (hRegA : Γ ⊢[PRAAx] regularContract A x) (hRegB : Γ ⊢[PRAAx] regularContract B x)
    (hResA : Γ ⊢[PRAAx] vanishing degree A μ code C x)
    (hResB : Γ ⊢[PRAAx] vanishing degree B ν code C x) :
    Γ ⊢[PRAAx] agreement A B N x := by
  cases degree with
  | zero =>
    exact .botE _ (constant_guard_impossible code C initial m M (ap2 A ConciseIPRA.PTm.zero x)
      hC hm hGuard (covered_at A initial x ConciseIPRA.PTm.zero hInA))
  | succ d =>
    have guard : Γ ⊢[PRAAx] uniformGuard d code C initial m M := by
      simpa only [uniformPolynomialGuard, coefficientGuard, uniformGuard, factorLower,
        Nat.add_sub_cancel] using hGuard
    exact name_agreement_at d A B μ ν N x code C initial m M hC hm hM guard hInA hInB hRegA hRegB hResA hResB

def allNamesFormula (degree : ℕ) (A B μ ν : PR 2) : Fm PTm 7 :=
  le one (denominator (var 4)) ⟶ zle (left (var 4)) (right (var 4)) ⟶
    le one (var 3) ⟶ le one (var 5) ⟶ le one (var 6) ⟶
    uniformPolynomialGuard degree (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
    covered A (var 4) (var 1) ⟶ covered B (var 4) (var 1) ⟶
    regularContract A (var 1) ⟶ regularContract B (var 1) ⟶
    vanishing degree A μ (var 2) (var 3) (var 1) ⟶
    vanishing degree B ν (var 2) (var 3) (var 1) ⟶ agreement A B (var 0) (var 1)

theorem polynomial_names_unique (degree : ℕ) (A B μ ν : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7 (allNamesFormula degree A B μ ν) := by
  refine closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI
    (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))))))))
  exact polynomial_names_agree_at degree A B μ ν (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp))

def allBisectionFormula (degree : ℕ) (B ν : PR 2) : Fm PTm 4 :=
  PolynomialRootName.admissible degree (var 1) ⟶
    le one (PolynomialRootName.coefficientDenominator (var 1)) ⟶ le one (var 2) ⟶ le one (var 3) ⟶
    uniformPolynomialGuard degree (PolynomialRootName.coefficientCode (var 1))
      (PolynomialRootName.coefficientDenominator (var 1)) (PolynomialRootName.initialState (var 1)) (var 2) (var 3) ⟶
    covered B (PolynomialRootName.initialState (var 1)) (var 1) ⟶ regularContract B (var 1) ⟶
    vanishing degree B ν (PolynomialRootName.coefficientCode (var 1))
      (PolynomialRootName.coefficientDenominator (var 1)) (var 1) ⟶ agreement (bisectionPointF degree) B (var 0) (var 1)

/-- The actual bisection name is the unique compatible regular root name under
the computed uniform factor guard, as a closed finite-query object sentence. -/
theorem bisection_root_unique_all_degrees (degree : ℕ) (B ν : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (allBisectionFormula degree B ν) := by
  refine closeUniv 4 (.impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_))))))))
  let Δ : List (Fm PTm 4) :=
    [vanishing degree B ν (PolynomialRootName.coefficientCode (var 1))
      (PolynomialRootName.coefficientDenominator (var 1)) (var 1),
     regularContract B (var 1), covered B (PolynomialRootName.initialState (var 1)) (var 1),
     uniformPolynomialGuard degree (PolynomialRootName.coefficientCode (var 1))
      (PolynomialRootName.coefficientDenominator (var 1)) (PolynomialRootName.initialState (var 1)) (var 2) (var 3),
     le one (var 3), le one (var 2), le one (PolynomialRootName.coefficientDenominator (var 1)),
     PolynomialRootName.admissible degree (var 1)]
  have h : Δ ⊢[PRAAx] PolynomialRootName.admissible degree (var 1) := Prf.hyp (by simp [Δ])
  have hC : Δ ⊢[PRAAx] le one (PolynomialRootName.coefficientDenominator (var 1)) := Prf.hyp (by simp [Δ])
  exact polynomial_names_agree_at degree (bisectionPointF degree) B (PolynomialRootName.residualScheduleF degree) ν
    (var 0) (var 1) (PolynomialRootName.coefficientCode (var 1)) (PolynomialRootName.coefficientDenominator (var 1))
    (PolynomialRootName.initialState (var 1)) (var 2) (var 3) hC
    (Prf.hyp (by simp [Δ])) (Prf.hyp (by simp [Δ])) (Prf.hyp (by simp [Δ]))
    (bisection_covered degree (var 1) h) (Prf.hyp (by simp [Δ]))
    (bisection_regular degree (var 1) h) (Prf.hyp (by simp [Δ]))
    (bisection_vanishing degree (var 1) h hC) (Prf.hyp (by simp [Δ]))

#print axioms constant_guard_impossible
#print axioms polynomial_names_unique
#print axioms bisection_root_unique_all_degrees

end LeanProofs.IPRA.Analysis.PolynomialRootUniqueness
