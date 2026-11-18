import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Core.Gcd

/-!
# Rational coherence from finite adjacent-error sums

Packet `foundations/fiber_ipra_2026-11-16`, Section 7.2. A sample has the
signed numerator `p(k,x)-q(k,x)` and its own positive denominator `d(k,x)`.
Its adjacent error majorant is `e(k,x)/f(k,x)`, with positive `f(k,x)`.

The actual PR accumulator starts with `(E,D)=(0,1)` and adds one error by
`(E,D) ↦ (E*f + e*D,D*f)`. Object QF induction proves denominator positivity
and the exact cross-multiplied telescoping inequality. No common sample
denominator, pairwise discrepancy premise or rational evaluator is assumed.
A separately supplied finite-sum tail certificate then yields the rational
tail estimate after cancellation of the proved positive accumulator denominator.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalSummableTails

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_tri subst_zabs)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] private theorem subst_one {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (one : PTm n) = one := by
  simp only [one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- Signed sample numerator, with precision and data both internal. -/
def value (p q : PR 2) (k x : PTm n) : ZT n := ⟨ap2 p k x, ap2 q k x⟩

/-- Numerator of `b/db-a/da` after clearing the two denominators. -/
def cross (a b : ZT n) (da db : PTm n) : ZT n :=
  b * ZT.ofNat da - a * ZT.ofNat db

/-- The actual discrepancy numerator between any two sample indices. -/
def difference (p q d : PR 2) (N M x : PTm n) : ZT n :=
  cross (value p q N x) (value p q M x) (ap2 d N x) (ap2 d M x)

@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (p q : PR 2) (k x : PTm n) :
    (value p q k x).subst σ = value p q (Syn.subst σ k) (Syn.subst σ x) := by
  simp [value, ZT.subst]

@[simp] theorem subst_cross {m : ℕ} (σ : Fin n → PTm m) (a b : ZT n) (da db : PTm n) :
    (cross a b da db).subst σ = cross (a.subst σ) (b.subst σ) (Syn.subst σ da) (Syn.subst σ db) := by
  simp [cross]

@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m)
    (p q d : PR 2) (N M x : PTm n) :
    (difference p q d N M x).subst σ =
      difference p q d (Syn.subst σ N) (Syn.subst σ M) (Syn.subst σ x) := by
  simp [difference]

private theorem pair_congr {a a' b b' : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] pairT a b ≐ pairT a' b' :=
  congrAdd (congrMul (congrAdd ha hb) (congrAdd ha hb)) ha

/-- Step variables are offset, old `(E,D)` code, and packed `(N,x)`. -/
def accumulatorStep (e f : PR 2) : PTm 3 :=
  let k := fstT (var 2) + var 0
  let x := sndT (var 2)
  pairT (fstT (var 1) * ap2 f k x + ap2 e k x * sndT (var 1))
    (sndT (var 1) * ap2 f k x)

/-- Actual primitive recursive rational-addition accumulator. -/
def accumulatorF (e f : PR 2) : PR 2 := rec2 (pairT zero one) (accumulatorStep e f)

def accumulator (e f : PR 2) (N r x : PTm n) : PTm n :=
  ap2 (accumulatorF e f) r (pairT N x)

def sumNum (e f : PR 2) (N r x : PTm n) : PTm n := fstT (accumulator e f N r x)
def sumDen (e f : PR 2) (N r x : PTm n) : PTm n := sndT (accumulator e f N r x)

@[simp] theorem subst_accumulator {m : ℕ} (σ : Fin n → PTm m)
    (e f : PR 2) (N r x : PTm n) :
    Syn.subst σ (accumulator e f N r x) =
      accumulator e f (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ x) := by
  simp only [accumulator, subst_ap2, subst_pairT]

@[simp] theorem subst_sumNum {m : ℕ} (σ : Fin n → PTm m)
    (e f : PR 2) (N r x : PTm n) :
    Syn.subst σ (sumNum e f N r x) =
      sumNum e f (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ x) := by
  simp only [sumNum, subst_fstT, subst_accumulator]

@[simp] theorem subst_sumDen {m : ℕ} (σ : Fin n → PTm m)
    (e f : PR 2) (N r x : PTm n) :
    Syn.subst σ (sumDen e f N r x) =
      sumDen e f (Syn.subst σ N) (Syn.subst σ r) (Syn.subst σ x) := by
  simp only [sumDen, subst_sndT, subst_accumulator]

theorem accumulator_zero (e f : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] accumulator e f N zero x ≐ pairT zero one := by
  simpa only [accumulator, accumulatorF, subst_pairT, ConciseIPRA.PTm.subst_zero,
    subst_one] using rec2_zero (Γ := Γ) (pairT zero one) (accumulatorStep e f) (pairT N x)

private theorem accumulator_step_at (e f : PR 2) (r old N x : PTm n) :
    Γ ⊢[PRAAx] Syn.subst ![r, old, pairT N x] (accumulatorStep e f) ≐
      pairT (fstT old * ap2 f (N + r) x + ap2 e (N + r) x * sndT old)
        (sndT old * ap2 f (N + r) x) := by
  simp only [accumulatorStep, subst_pairT, subst_fstT, subst_sndT, subst_ap2,
    PTm.subst_add, PTm.subst_mul, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hf := congrAp2 (Γ := Γ) f (congrAdd (fst_pair N x) (.eqRefl r)) (snd_pair N x)
  have he := congrAp2 (Γ := Γ) e (congrAdd (fst_pair N x) (.eqRefl r)) (snd_pair N x)
  exact pair_congr (congrAdd (congrMul (.eqRefl _) hf) (congrMul he (.eqRefl _)))
    (congrMul (.eqRefl _) hf)

theorem accumulator_succ (e f : PR 2) (N r x : PTm n) :
    Γ ⊢[PRAAx] accumulator e f N (succ r) x ≐
      pairT (sumNum e f N r x * ap2 f (N + r) x + ap2 e (N + r) x * sumDen e f N r x)
        (sumDen e f N r x * ap2 f (N + r) x) :=
  (rec2_succ (pairT zero one) (accumulatorStep e f) r (pairT N x)).eqTrans
    (accumulator_step_at e f r _ N x)

theorem sumNum_zero (e f : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sumNum e f N zero x ≐ zero :=
  (congrFst (accumulator_zero e f N x)).eqTrans (fst_pair zero one)

theorem sumDen_zero (e f : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] sumDen e f N zero x ≐ one :=
  (congrSnd (accumulator_zero e f N x)).eqTrans (snd_pair zero one)

theorem sumNum_succ (e f : PR 2) (N r x : PTm n) :
    Γ ⊢[PRAAx] sumNum e f N (succ r) x ≐
      sumNum e f N r x * ap2 f (N + r) x + ap2 e (N + r) x * sumDen e f N r x :=
  (congrFst (accumulator_succ e f N r x)).eqTrans (fst_pair _ _)

theorem sumDen_succ (e f : PR 2) (N r x : PTm n) :
    Γ ⊢[PRAAx] sumDen e f N (succ r) x ≐ sumDen e f N r x * ap2 f (N + r) x :=
  (congrSnd (accumulator_succ e f N r x)).eqTrans (snd_pair _ _)

/-- Every denominator in this supplied PR family is positive. -/
def positive (d : PR 2) (x : PTm n) : Fm PTm n :=
  .all (le one (ap2 d (var 0) (Syn.shift x)))

@[simp] theorem subst_positive {m : ℕ} (σ : Fin n → PTm m) (d : PR 2) (x : PTm n) :
    (positive d x).subst σ = positive d (Syn.subst σ x) := by
  simp only [positive, Fm.subst_all, subst_le, subst_one, subst_ap2,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

theorem positive_at {d : PR 2} {x : PTm n} (h : Γ ⊢[PRAAx] positive d x) (k : PTm n) :
    Γ ⊢[PRAAx] le one (ap2 d k x) := by
  simpa only [positive, subst_le, subst_one, subst_ap2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k h

/-- The product denominator of the actual finite rational sum is positive. -/
theorem sumDen_positive (e f : PR 2) (N r x : PTm n)
    (hf : Γ ⊢[PRAAx] positive f x) :
    Γ ⊢[PRAAx] le one (sumDen e f N r x) := by
  have hall : Γ ⊢[PRAAx] .all (le one
      (sumDen e f (Syn.shift N) (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_one, subst_sumDen, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact le_congr (.eqRefl _) (sumDen_zero e f N x).eqSymm (le_refl one)
    · simp only [subst_le, subst_one, subst_sumDen, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      have shifted : Γ.map Fm.shift ⊢[PRAAx] positive f (Syn.shift x) := by
        simpa only [Fm.shift, subst_positive, Syn.shift] using hf.shift
      exact le_congr (one_mul one) (sumDen_succ e f _ _ _).eqSymm
        (le_mul_mono Prf.hyp0 (positive_at shifted (Syn.shift N + var 0)).wk)
  simpa only [subst_le, subst_one, subst_sumDen, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE r hall

private theorem abs_scale (c : PTm n) (u : ZT n) :
    Γ ⊢[PRAAx] zabs (ZT.ofNat c * u) ≐ c * zabs u := by
  refine (zabs_congr (v := ⟨c * u.pos, c * u.neg⟩) ?_).eqTrans (ad_mul c u.pos u.neg)
  rw [ZT.toZ_mul, ZT.toZ_ofNat]
  change Groth.ι (Q.mk Γ c) *
      (Groth.ι (Q.mk Γ u.pos) - Groth.ι (Q.mk Γ u.neg)) =
    Groth.ι (Q.mk Γ (c * u.pos)) - Groth.ι (Q.mk Γ (c * u.neg))
  simp only [Q.mk_mul, map_mul]
  ring

/-- The denominator-cleared triangle inequality for three rational samples. -/
theorem cross_triangle (a b c : ZT n) (da db dc : PTm n) :
    Γ ⊢[PRAAx] le (db * zabs (cross a c da dc))
      (dc * zabs (cross a b da db) + da * zabs (cross b c db dc)) := by
  have identity : ZT.toZ Γ (ZT.ofNat db * cross a c da dc) =
      ZT.toZ Γ (ZT.ofNat dc * cross a b da db) +
      ZT.toZ Γ (ZT.ofNat da * cross b c db dc) := by
    simp only [cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]
    ring
  exact le_congr (abs_scale db _) (congrAdd (abs_scale dc _) (abs_scale da _))
    (zabs_tri identity)

private theorem cancel_positive {c a b : PTm n} (hc : Γ ⊢[PRAAx] le one c)
    (h : Γ ⊢[PRAAx] le (c * a) (c * b)) : Γ ⊢[PRAAx] le a b := by
  have ce : Γ ⊢[PRAAx] c ≐ succ (monus c one) :=
    (eq_add_of_le hc).eqTrans (by ipra_ring)
  exact mul_le_cancel (le_congr (congrMul ce (.eqRefl _)) (congrMul ce (.eqRefl _)) h)

/-- Adding one error majorant preserves the exact rational discrepancy bound. -/
theorem rational_step (a b c : ZT n) (da db dc E D e f : PTm n)
    (hdb : Γ ⊢[PRAAx] le one db)
    (ih : Γ ⊢[PRAAx] le (D * zabs (cross a b da db)) (E * da * db))
    (motion : Γ ⊢[PRAAx] le (f * zabs (cross b c db dc)) (e * db * dc)) :
    Γ ⊢[PRAAx] le ((D * f) * zabs (cross a c da dc)) ((E * f + e * D) * da * dc) := by
  have tri := mul_le_mul_right (D * f) (cross_triangle (Γ := Γ) a b c da db dc)
  have old := mul_le_mul_right (f * dc) ih
  have next := mul_le_mul_right (D * da) motion
  have triangle : Γ ⊢[PRAAx]
      le (db * ((D * f) * zabs (cross a c da dc)))
        (D * zabs (cross a b da db) * (f * dc) + f * zabs (cross b c db dc) * (D * da)) :=
    le_congr (by ipra_ring) (by ipra_ring) tri
  have combined : Γ ⊢[PRAAx]
      le (db * ((D * f) * zabs (cross a c da dc)))
        (db * ((E * f + e * D) * da * dc)) :=
    le_trans triangle (le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ old next))
  exact cancel_positive hdb combined

private theorem value_congr (p q : PR 2) (x : PTm n) {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (value p q a x) = ZT.toZ Γ (value p q b x) := by
  have hp := natEq (congrAp2 p h (.eqRefl x))
  have hq := natEq (congrAp2 q h (.eqRefl x))
  simpa only [value, ZT.toZ] using congrArg₂ HSub.hSub hp hq

theorem difference_right_congr (p q d : PR 2) (N x : PTm n) {M M' : PTm n}
    (h : Γ ⊢[PRAAx] M ≐ M') :
    Γ ⊢[PRAAx] zabs (difference p q d N M x) ≐ zabs (difference p q d N M' x) := by
  have numerator := value_congr p q x h
  have denominator := natEq (congrAp2 d h (.eqRefl x))
  apply zabs_congr
  simp only [difference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat,
    numerator, denominator]

private theorem difference_self (p q d : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] zabs (difference p q d N N x) ≐ zero := by
  have h : ZT.toZ Γ (difference p q d N N x) = ZT.toZ Γ (ZT.natLit 0) := by
    simp only [difference, cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]
    ring
  exact (zabs_congr h).eqTrans ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _))

private theorem difference_zero (p q d : PR 2) (N x : PTm n) :
    Γ ⊢[PRAAx] zabs (difference p q d N (N + zero) x) ≐ zero :=
  (difference_right_congr p q d N x (add_zero N)).eqTrans (difference_self p q d N x)

/-- The exact rational adjacent-error contract, with its own error denominator. -/
def motion (p q d e f : PR 2) (x : PTm n) : Fm PTm n :=
  .all (le
    (ap2 f (var 0) (Syn.shift x) *
      zabs (difference p q d (var 0) (succ (var 0)) (Syn.shift x)))
    (ap2 e (var 0) (Syn.shift x) * ap2 d (var 0) (Syn.shift x) *
      ap2 d (succ (var 0)) (Syn.shift x)))

@[simp] theorem subst_motion {m : ℕ} (σ : Fin n → PTm m)
    (p q d e f : PR 2) (x : PTm n) :
    (motion p q d e f x).subst σ = motion p q d e f (Syn.subst σ x) := by
  simp only [motion, Fm.subst_all, subst_le, PTm.subst_mul, subst_zabs,
    subst_difference, subst_ap2, ConciseIPRA.PTm.subst_succ,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

theorem motion_at (p q d e f : PR 2) {x : PTm n} (h : Γ ⊢[PRAAx] motion p q d e f x)
    (k : PTm n) :
    Γ ⊢[PRAAx] le (ap2 f k x * zabs (difference p q d k (succ k) x))
      (ap2 e k x * ap2 d k x * ap2 d (succ k) x) := by
  simpa only [motion, subst_le, PTm.subst_mul, subst_zabs, subst_difference,
    subst_ap2, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] using Prf.allE k h

/-- One step of the finite rational telescoping invariant. -/
theorem discrepancy_step (p q d e f : PR 2) (N r x : PTm n)
    (hden : Γ ⊢[PRAAx] le one (ap2 d (N + r) x))
    (ih : Γ ⊢[PRAAx] le
      (sumDen e f N r x * zabs (difference p q d N (N + r) x))
      (sumNum e f N r x * ap2 d N x * ap2 d (N + r) x))
    (hm : Γ ⊢[PRAAx] le
      (ap2 f (N + r) x * zabs (difference p q d (N + r) (succ (N + r)) x))
      (ap2 e (N + r) x * ap2 d (N + r) x * ap2 d (succ (N + r)) x)) :
    Γ ⊢[PRAAx] le
      (sumDen e f N (succ r) x * zabs (difference p q d N (N + succ r) x))
      (sumNum e f N (succ r) x * ap2 d N x * ap2 d (N + succ r) x) := by
  have step := rational_step (value p q N x) (value p q (N + r) x)
    (value p q (succ (N + r)) x) (ap2 d N x) (ap2 d (N + r) x)
    (ap2 d (succ (N + r)) x) (sumNum e f N r x) (sumDen e f N r x)
    (ap2 e (N + r) x) (ap2 f (N + r) x) hden ih hm
  have index : Γ ⊢[PRAAx] N + succ r ≐ succ (N + r) := add_succ N r
  have numerator := difference_right_congr p q d N x index
  have denominator := congrAp2 d index (.eqRefl x)
  exact le_congr
    (congrMul (sumDen_succ e f N r x).eqSymm numerator.eqSymm)
    (congrMul (congrMul (sumNum_succ e f N r x).eqSymm (.eqRefl _)) denominator.eqSymm) step

/-- Finite rational telescoping at arbitrary internal starting index and length.
The only induction predicate is the displayed QF integer inequality. -/
theorem discrepancy (p q d e f : PR 2) (N r x : PTm n)
    (hd : Γ ⊢[PRAAx] positive d x) (hm : Γ ⊢[PRAAx] motion p q d e f x) :
    Γ ⊢[PRAAx] le
      (sumDen e f N r x * zabs (difference p q d N (N + r) x))
      (sumNum e f N r x * ap2 d N x * ap2 d (N + r) x) := by
  have hall : Γ ⊢[PRAAx] .all (le
      (sumDen e f (Syn.shift N) (var 0) (Syn.shift x) *
        zabs (difference p q d (Syn.shift N) (Syn.shift N + var 0) (Syn.shift x)))
      (sumNum e f (Syn.shift N) (var 0) (Syn.shift x) * ap2 d (Syn.shift N) (Syn.shift x) *
        ap2 d (Syn.shift N + var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_le, subst_zabs, PTm.subst_mul, subst_difference,
        subst_sumDen, subst_sumNum, subst_ap2, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      simp only [PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have left : Γ ⊢[PRAAx] sumDen e f N zero x *
          zabs (difference p q d N (N + zero) x) ≐ zero :=
        (congrMul (.eqRefl _) (difference_zero p q d N x)).eqTrans (mul_zero _)
      have right : Γ ⊢[PRAAx] sumNum e f N zero x * ap2 d N x * ap2 d (N + zero) x ≐ zero :=
        (congrMul (congrMul (sumNum_zero e f N x) (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)
      exact le_congr left.eqSymm right.eqSymm (le_refl zero)
    · simp only [subst_le, subst_zabs, PTm.subst_mul, subst_difference,
        subst_sumDen, subst_sumNum, subst_ap2, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift]
      simp only [PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hd' : Γ.map Fm.shift ⊢[PRAAx] positive d (Syn.shift x) := by
        simpa only [Fm.shift, subst_positive, Syn.shift] using hd.shift
      have hm' : Γ.map Fm.shift ⊢[PRAAx] motion p q d e f (Syn.shift x) := by
        simpa only [Fm.shift, subst_motion, Syn.shift] using hm.shift
      exact discrepancy_step p q d e f (Syn.shift N) (var 0) (Syn.shift x)
        (positive_at hd' (Syn.shift N + var 0)).wk Prf.hyp0
        (motion_at p q d e f hm' (Syn.shift N + var 0)).wk
  have instantiated := Prf.allE r hall
  simp only [subst_le, subst_zabs, PTm.subst_mul, subst_difference,
    subst_sumDen, subst_sumNum, subst_ap2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at instantiated
  simpa only [PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using instantiated

/-- The finite error sum is bounded by the rational tail `T(N,x)/U(N,x)`.
The tail denominator is positive and the comparison is about the actual
primitive-recursive rational accumulator. -/
def tail (e f T U : PR 2) (x : PTm n) : Fm PTm n :=
  positive U x ⋏ .all (.all (le
    (ap2 U (var 1) (Syn.shift (Syn.shift x)) *
      sumNum e f (var 1) (var 0) (Syn.shift (Syn.shift x)))
    (ap2 T (var 1) (Syn.shift (Syn.shift x)) *
      sumDen e f (var 1) (var 0) (Syn.shift (Syn.shift x)))))

theorem tail_at (e f T U : PR 2) {x : PTm n} (h : Γ ⊢[PRAAx] tail e f T U x)
    (N r : PTm n) :
    Γ ⊢[PRAAx] le (ap2 U N x * sumNum e f N r x)
      (ap2 T N x * sumDen e f N r x) := by
  have hs := Prf.allE r (Prf.allE N (Prf.andE₂ h))
  simpa [tail, Syn.subst_shift, Syn.up_succ, ← Syn.shift_subst, Syn.subst_subst] using hs

/-- Actual finite rational summation gives the supplied uniform tail bound. -/
theorem tail_bound (p q d e f T U : PR 2) (N r x : PTm n)
    (hd : Γ ⊢[PRAAx] positive d x) (hf : Γ ⊢[PRAAx] positive f x)
    (hm : Γ ⊢[PRAAx] motion p q d e f x) (ht : Γ ⊢[PRAAx] tail e f T U x) :
    Γ ⊢[PRAAx] le
      (ap2 U N x * zabs (difference p q d N (N + r) x))
      (ap2 T N x * ap2 d N x * ap2 d (N + r) x) := by
  have finite := mul_le_mul_right (ap2 U N x) (discrepancy p q d e f N r x hd hm)
  have majorant := mul_le_mul_right (ap2 d N x * ap2 d (N + r) x) (tail_at e f T U ht N r)
  have first : Γ ⊢[PRAAx] le
      (sumDen e f N r x * (ap2 U N x * zabs (difference p q d N (N + r) x)))
      ((ap2 U N x * sumNum e f N r x) * (ap2 d N x * ap2 d (N + r) x)) :=
    le_congr (by ipra_ring) (by ipra_ring) finite
  have combined : Γ ⊢[PRAAx] le
      (sumDen e f N r x * (ap2 U N x * zabs (difference p q d N (N + r) x)))
      (sumDen e f N r x * (ap2 T N x * ap2 d N x * ap2 d (N + r) x)) :=
    le_trans first (le_congr (.eqRefl _) (by ipra_ring) majorant)
  exact cancel_positive (sumDen_positive e f N r x hf) combined

/-- Source form with arbitrary ordered endpoints, rather than a chosen offset. -/
theorem tail_between (p q d e f T U : PR 2) (x : PTm n) {N M : PTm n}
    (hd : Γ ⊢[PRAAx] positive d x) (hf : Γ ⊢[PRAAx] positive f x)
    (hm : Γ ⊢[PRAAx] motion p q d e f x) (ht : Γ ⊢[PRAAx] tail e f T U x)
    (order : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] le (ap2 U N x * zabs (difference p q d N M x))
      (ap2 T N x * ap2 d N x * ap2 d M x) := by
  have index : Γ ⊢[PRAAx] N + monus M N ≐ M := (eq_add_of_le order).eqSymm
  exact le_congr
    (congrMul (.eqRefl _) (difference_right_congr p q d N x index))
    (congrMul (.eqRefl _) (congrAp2 d index (.eqRefl x)))
    (tail_bound p q d e f T U N (monus M N) x hd hf hm ht)

/-- Variables `0=N`, `1=r`, `2=x`. The finite rational sum has a proved
positive denominator as well as the exact cross-multiplied error bound. -/
def finiteFormula (p q d e f : PR 2) : Fm PTm 3 :=
  positive d (var 2) ⟶ positive f (var 2) ⟶ motion p q d e f (var 2) ⟶
    (le one (sumDen e f (var 0) (var 1) (var 2)) ⋏
      le (sumDen e f (var 0) (var 1) (var 2) *
          zabs (difference p q d (var 0) (var 0 + var 1) (var 2)))
        (sumNum e f (var 0) (var 1) (var 2) * ap2 d (var 0) (var 2) *
          ap2 d (var 0 + var 1) (var 2)))

theorem finite_telescoping (p q d e f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (finiteFormula p q d e f) := by
  refine closeUniv 3 (.impI (.impI (.impI (.andI ?_ ?_))))
  · exact sumDen_positive e f _ _ _ Prf.hyp1
  · exact discrepancy p q d e f _ _ _ Prf.hyp1.wk Prf.hyp0

/-- The rational tail statement at arbitrary start, finite length and data.
The positive tail denominator is retained in the public output. -/
def tailFormula (p q d e f T U : PR 2) : Fm PTm 3 :=
  positive d (var 2) ⟶ positive f (var 2) ⟶ motion p q d e f (var 2) ⟶
    tail e f T U (var 2) ⟶
      (le one (ap2 U (var 0) (var 2)) ⋏
        le (ap2 U (var 0) (var 2) *
            zabs (difference p q d (var 0) (var 0 + var 1) (var 2)))
          (ap2 T (var 0) (var 2) * ap2 d (var 0) (var 2) * ap2 d (var 0 + var 1) (var 2)))

theorem summable_tail (p q d e f T U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (tailFormula p q d e f T U) := by
  refine closeUniv 3 (.impI (.impI (.impI (.impI (.andI ?_ ?_)))))
  · exact positive_at (Prf.andE₁ Prf.hyp0) _
  · exact tail_bound p q d e f T U _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0

/-- Variables `0=N`, `1=M`, `2=x`. This is the full source rational
summable-tail conclusion with the order guard and every denominator explicit. -/
def endpointsFormula (p q d e f T U : PR 2) : Fm PTm 3 :=
  positive d (var 2) ⟶ positive f (var 2) ⟶ motion p q d e f (var 2) ⟶
    tail e f T U (var 2) ⟶ le (var 0) (var 1) ⟶
      (le one (ap2 U (var 0) (var 2)) ⋏
        le (ap2 U (var 0) (var 2) * zabs (difference p q d (var 0) (var 1) (var 2)))
          (ap2 T (var 0) (var 2) * ap2 d (var 0) (var 2) * ap2 d (var 1) (var 2)))

theorem summable_tail_endpoints (p q d e f T U : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (endpointsFormula p q d e f T U) := by
  refine closeUniv 3 (.impI (.impI (.impI (.impI (.impI (.andI ?_ ?_))))))
  · exact positive_at (Prf.andE₁ Prf.hyp1) _
  · exact tail_between p q d e f T U _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk
      Prf.hyp1.wk Prf.hyp1 Prf.hyp0

#print axioms accumulator_succ
#print axioms sumDen_positive
#print axioms cross_triangle
#print axioms rational_step
#print axioms finite_telescoping
#print axioms summable_tail
#print axioms summable_tail_endpoints

end LeanProofs.IPRA.Analysis.RationalSummableTails
