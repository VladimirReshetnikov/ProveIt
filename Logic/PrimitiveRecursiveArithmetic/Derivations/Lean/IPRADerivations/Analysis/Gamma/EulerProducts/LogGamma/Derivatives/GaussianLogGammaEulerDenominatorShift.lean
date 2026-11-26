import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerHead
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilySplit
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotientProperness
import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupDifference
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# The unit shift of the original finite Euler denominator

Splitting the first row of the original sum leaves the same N rows as
the prefix of the unit-shifted sum. The latter appends the original
logarithm at index N+1. The equality of the encoded row data identifies
the two prefixes, then the named difference cancels their common sum
at independent requested precisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDenominatorShift

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerHead (sumData rowBody rowData row_at subst_rowData sum_rows sum_regular shifted_source)
open GaussianNameArithmetic (addF addData add_fast add_equivalent subst_addData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_to_diagonal subst_crossEquivalent)
open GaussianNameRingLaws (add_commutative)
open GaussianNamedFiniteProductFamilyAppend (regular_prefix)
open GaussianNamedFiniteProductFamilyCongruence (equalRows)
open GaussianNamedFiniteSumFamilyCongruence (family_sum_cross)
open GaussianNamedFiniteSumFamilySplit (first_cross append_cross regular_tail)
open GaussianRightHalfPlaneLogarithm (source subst_data)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "EulerSum" => GaussianLogGammaEulerHead.sumF
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "fd" => GaussianNamedFiniteSumFamily.data
local notation "sf" => GaussianNamedFiniteSumFamily.nameF
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

def prefixData (A B D neg N : PTm n) : PTm n := fd N (rowData (A + D) B D neg)

private theorem log_input_congr (A C B D neg : PTm n) (h : Γ ⊢[PRAAx] A ≐ C) :
    Γ ⊢[PRAAx] P A B D neg ≐ P C B D neg := by
  simpa only [subst_data, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (P (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![A, B, D, neg]) (σ' := ![C, B, D, neg]) (fun i => by
        fin_cases i
        · exact h
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _)

private theorem cross_data_congr (f g : PR 2) (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] x ≐ x')
    (hy : Γ ⊢[PRAAx] y ≐ y') (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent f g x' y' := by
  simpa only [subst_crossEquivalent, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Prf.eqSubst (crossEquivalent f g (var 0) (var 1) : Fm PTm 2) ![x, y] ![x', y']
      (fun i => by fin_cases i; exact hx; exact hy)
      (by simpa only [subst_crossEquivalent, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using h)

private theorem add_data_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') :
    Γ ⊢[PRAAx] addData x y ≐ addData x' y' := by
  simpa only [subst_addData, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Prf.eqCongr (addData (var 0) (var 1) : PTm 2) (σ := ![x, y]) (σ' := ![x', y'])
      (fun i => by fin_cases i; exact hx; exact hy)

private theorem shifted_input (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] source (A + D) D neg :=
  .andI (.andI (le_trans h.andE₁.andE₁ (le_add_right A D)) h.andE₁.andE₂) h.andE₂

theorem shifted_row (A B D neg i : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (rowData (A + D) B D neg) ≐ P (A + succ i * D) B D neg := by
  have e : Γ ⊢[PRAAx] (A + D) + i * D ≐ A + succ i * D := by ipra_ring
  exact (row_at (Γ := Γ) i (A + D) B D neg).eqTrans
    (log_input_congr ((A + D) + i * D) (A + succ i * D) B D neg e)

theorem prefix_regular (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN EulerSum (prefixData A B D neg N) := by
  let x := rowData (A + D) B D neg
  have rows := sum_rows (A + D) B D neg N (shifted_input A D neg h)
  have init := regular_prefix (Γ := Γ) G rowBody N (succ N) x (le_succ_self N) rows
  exact GaussianNamedFiniteSumFamily.regular G rowBody N x init

theorem tail_cross (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (sf G (shiftBody rowBody)) EulerSum
      (fd N (rowData A B D neg)) (prefixData A B D neg N) := by
  apply family_sum_cross G G (shiftBody rowBody) rowBody N
  refine .allI (.impI ?_)
  let s (v : PTm n) := Syn.shift v
  let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
  let i : PTm (n + 1) := var 0
  let x := inst2 (shiftBody rowBody) i (rowData (s A) (s B) (s D) (s neg))
  let y := inst2 rowBody i (rowData (s A + s D) (s B) (s D) (s neg))
  let z := P (s A + succ i * s D) (s B) (s D) (s neg)
  have hs : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [Δ, s, Fm.shift, Syn.shift, source, GaussianRightHalfPlaneArgument.source] using h.shift.wk
  have reg : Δ ⊢[PRAAx] pointCN G z :=
    GaussianRightHalfPlaneLogarithm.regular (s A + succ i * s D) (s B) (s D) (s neg)
      (shifted_source (succ i) (s A) (s D) (s neg) hs)
  have left : Δ ⊢[PRAAx] x ≐ z := by
    simpa only [x, z, inst2_shiftBody] using row_at (succ i) (s A) (s B) (s D) (s neg)
  have right : Δ ⊢[PRAAx] y ≐ z := shifted_row (s A) (s B) (s D) (s neg) i
  simpa only [Δ, x, y, i, s, Syn.shift, subst_rowData, PTm.subst_add] using
    cross_data_congr G G z x z y left.eqSymm right.eqSymm (cross_refl G z reg)

theorem first_log (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent EulerSum (addF EulerSum G) (sumData A B D neg N)
      (addData (prefixData A B D neg N) (P A B D neg)) := by
  let x := rowData A B D neg
  let p := prefixData A B D neg N
  let s := fd N x
  let z := P A B D neg
  let t := sf G (shiftBody rowBody)
  have rows := sum_rows A B D neg N h
  have hZ : Γ ⊢[PRAAx] pointCN G z := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have hT : Γ ⊢[PRAAx] pointCN t s :=
    GaussianNamedFiniteSumFamily.regular G (shiftBody rowBody) N x (regular_tail G rowBody N x rows)
  have hP := prefix_regular A B D neg N h
  have e : Γ ⊢[PRAAx] inst2 rowBody zero x ≐ z :=
    (row_at zero A B D neg).eqTrans (log_input_congr (A + zero * D) A B D neg (by ipra_ring))
  have split : Γ ⊢[PRAAx] crossEquivalent EulerSum (addF G t) (sumData A B D neg N) (addData z s) :=
    cross_data_congr EulerSum (addF G t) (sumData A B D neg N) (sumData A B D neg N)
      (addData (inst2 rowBody zero x) s) (addData z s) (.eqRefl _)
      (add_data_congr (inst2 rowBody zero x) z s s e (.eqRefl s)) (first_cross G rowBody N x rows)
  have same := add_equivalent G G t EulerSum z z s p hZ hZ hT hP
    (cross_to_diagonal G G z z (cross_refl G z hZ))
    (cross_to_diagonal t EulerSum s p (tail_cross A B D neg N h))
  exact cross_trans EulerSum (addF G t) (addF EulerSum G) (sumData A B D neg N) (addData z s) (addData p z) split
    (cross_trans (addF G t) (addF G EulerSum) (addF EulerSum G) (addData z s) (addData z p) (addData p z)
      same (add_commutative G EulerSum z p hZ hP))

theorem last_log (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent EulerSum (addF EulerSum G) (sumData (A + D) B D neg N)
      (addData (prefixData A B D neg N) (P (A + succ N * D) B D neg)) := by
  let x := rowData (A + D) B D neg
  let p := prefixData A B D neg N
  let z := P (A + succ N * D) B D neg
  let s := sumData (A + D) B D neg N
  have rows := sum_rows (A + D) B D neg N (shifted_input A D neg h)
  exact cross_data_congr EulerSum (addF EulerSum G) s s (addData p (inst2 rowBody N x)) (addData p z) (.eqRefl s)
    (add_data_congr p p (inst2 rowBody N x) z (.eqRefl p) (shifted_row A B D neg N))
    (append_cross G rowBody N x rows)

/-- Only the two endpoint logarithms survive the unit shift. -/
theorem difference (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent (diffF EulerSum EulerSum) (diffF G G)
      (diffData (sumData (A + D) B D neg N) (sumData A B D neg N))
      (diffData (P (A + succ N * D) B D neg) (P A B D neg)) := by
  let p := prefixData A B D neg N
  let last := P (A + succ N * D) B D neg
  let first := P A B D neg
  have hP := prefix_regular A B D neg N h
  have hLast : Γ ⊢[PRAAx] pointCN G last :=
    GaussianRightHalfPlaneLogarithm.regular (A + succ N * D) B D neg (shifted_source (succ N) A D neg h)
  have hFirst : Γ ⊢[PRAAx] pointCN G first := GaussianRightHalfPlaneLogarithm.regular A B D neg h
  have both := GaussianNamedDifferenceQuotientProperness.difference_proper
    EulerSum (addF EulerSum G) EulerSum (addF EulerSum G)
    (sumData (A + D) B D neg N) (addData p last) (sumData A B D neg N) (addData p first)
    (sum_regular (A + D) B D neg N (shifted_input A D neg h)) (add_fast _ _ _ _ hP hLast)
    (sum_regular A B D neg N h) (add_fast _ _ _ _ hP hFirst)
    (last_log A B D neg N h) (first_log A B D neg N h)
  exact cross_trans _ _ _ _ _ _ both (GaussianBohrMollerupDifference.cancel_common EulerSum G G p last first hP hLast hFirst)

theorem actual_finite_Euler_denominator_unit_shift_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶
        crossEquivalent (diffF EulerSum EulerSum) (diffF G G)
          (diffData (sumData (var 0 + var 2) (var 1) (var 2) (var 3) (var 4))
            (sumData (var 0) (var 1) (var 2) (var 3) (var 4)))
          (diffData (P (var 0 + succ (var 4) * var 2) (var 1) (var 2) (var 3))
            (P (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 5 (.impI (difference _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDenominatorShift
