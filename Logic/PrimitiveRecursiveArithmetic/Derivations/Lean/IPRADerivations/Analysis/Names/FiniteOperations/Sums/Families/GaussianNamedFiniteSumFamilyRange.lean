import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamilySplit
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# Splitting a named Gaussian sum at a numerical index

The range starts at the supplied numerical index and reads each original
row at that index plus its local index. At one precision the resulting
rational sums satisfy the literal finite split. The full length budgets
both of the shorter sums at that same clock. Regularity and the
independent-precision equivalence then use the original named evaluators.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyRange

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteProductFamily (regularRows regular_at subst_regularRows)
open GaussianNamedFiniteProductFamilyAppend (regular_prefix)
open GaussianNamedFiniteSumFamily (body data finite nameF term_at sample_at regular subst_data)
open GaussianNamedFiniteSumFamilySplit (finite_sample_distance)
open GaussianNameArithmetic (addF addData add_fast subst_addData sum_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (equivalent_of_envelope add_sample_error three)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (qadd)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalSyntheticDivision (qadd_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Row `i` reads the original row at `N+i` from data `⟨N,x⟩`. -/
abbrev rangeBody (t : PTm 2) : PTm 2 := offB t

/-- A range consists of `r` rows, starting at `N` in the original family. -/
def rangeData (N r x : PTm n) : PTm n := data r (pairT N x)

ipra_subst rangeData

theorem range_row_at (t : PTm 2) (N i x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rangeBody t) i (pairT N x) ≐ inst2 t (N + i) x :=
  offset_at t N i x

/-- The literal prefix and interval sums at the same row clock. -/
theorem finite_split (f : PR 2) (t : PTm 2) (k N r x : PTm n) :
    Γ ⊢[PRAAx] finite f t k (N + r) x ≐
      qadd (finite f t k N x) (finite f (rangeBody t) k r (pairT N x)) := by
  refine (GaussianRationalMatrixFiniteSums.sum_split (body f t) N r (pairT k x)).eqTrans
    (qadd_congr (.eqRefl _) ?_)
  refine GaussianRationalFiniteSum.sum_congr_bounded _ _ r _ _ (.allI (.impI ?_))
  simp only [shift_pairT]
  let a := Syn.shift N
  let v := Syn.shift x
  let p := Syn.shift k
  let i : PTm (n + 1) := var 0
  exact (offset_at (body f t) a i (pairT p v)).eqTrans
    ((term_at f t (a + i) p v).eqTrans
      ((congrAp2 f (.eqRefl _) (range_row_at t a i v).eqSymm).eqTrans
        (term_at f (rangeBody t) i p (pairT a v)).eqSymm))

private theorem point_data_congr (f : PR 2) {a b : PTm n}
    (e : Γ ⊢[PRAAx] a ≐ b) (h : Γ ⊢[PRAAx] pointCN f a) : Γ ⊢[PRAAx] pointCN f b := by
  have h' : Γ ⊢[PRAAx] (pointCN f (var 0 : PTm (n + 1))).subst (Syn.inst a) := by
    simpa only [subst_pointCN, Syn.subst_var, Syn.inst_zero] using h
  simpa only [subst_pointCN, Syn.subst_var, Syn.inst_zero] using
    Prf.eqSubst1 (pointCN f (var 0 : PTm (n + 1))) e h'

/-- Every row in the range is one of the certified original rows. -/
theorem regular_range (f : PR 2) (t : PTm 2) (N r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (N + r) x) :
    Γ ⊢[PRAAx] regularRows f (rangeBody t) r (pairT N x) := by
  refine .allI (.impI ?_)
  let a := Syn.shift N
  let b := Syn.shift r
  let v := Syn.shift x
  let i : PTm (n + 1) := var 0
  let Δ := lt i b :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (a + b) v := by
    simpa only [Δ, a, b, v, Fm.shift, Syn.shift, subst_regularRows, PTm.subst_add] using h.shift.wk
  have hi : Δ ⊢[PRAAx] lt (a + i) (a + b) := by
    ipra_le sl (Prf.hyp0 : Δ ⊢[PRAAx] lt i b)
  have row := regular_at f t (a + b) v (a + i) hs hi
  simpa only [i, a, v, shift_pairT] using point_data_congr f (range_row_at t a i v).eqSymm row

theorem range_regular (f : PR 2) (t : PTm 2) (N r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (N + r) x) : Γ ⊢[PRAAx]
    pointCN (nameF f (rangeBody t)) (rangeData N r x) :=
  regular f (rangeBody t) r (pairT N x) (regular_range f t N r x h)

/-- Compare the full family sampler with the addition of the two parts
at an arbitrary requested precision. -/
theorem range_sample (f : PR 2) (t : PTm 2) (p N r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (N + r) x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f t) p (data (N + r) x))
      (ap2 (addF (nameF f t) (nameF f (rangeBody t))) p (addData (data N x) (rangeData N r x)))
      (num 7) (unit p) := by
  let k := exponent (N + r) p
  have hN := regular_prefix f t N (N + r) x (le_add_right N r) h
  have hr := regular_range f t N r x h
  have budget := query_budget (Γ := Γ) (N + r) p
  have kN : Γ ⊢[PRAAx] le (N * unit p) (unit k) :=
    le_trans (mul_le_mul_right (unit p) (le_add_right N r)) budget
  have kr : Γ ⊢[PRAAx] le (r * unit p) (unit k) :=
    le_trans (mul_le_mul_right (unit p) (le_add_left r N)) budget
  have first := finite_sample_distance f t k p N x hN kN
  have second := finite_sample_distance f (rangeBody t) k p r (pairT N x) hr kr
  have hp := unit_positive (Γ := Γ) p
  have exactSplit := (sample_at (Γ := Γ) f t p (N + r) x).eqTrans (finite_split f t k N r x)
  have sumError := distance_congr exactSplit.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ _ _ _ _ _ hp first second)
  have addError := distance_symmetric _ _ _ _ hp
    (add_sample_error (nameF f t) (nameF f (rangeBody t)) (data N x) (rangeData N r x) p
      (regular f t N x hN) (range_regular f t N r x h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp sumError addError)

theorem range_cross (f : PR 2) (t : PTm 2) (N r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t (N + r) x) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f t) (addF (nameF f t) (nameF f (rangeBody t))) (data (N + r) x)
      (addData (data N x) (rangeData N r x)) := by
  have hN := regular_prefix f t N (N + r) x (le_add_right N r) h
  refine equivalent_of_envelope _ _ _ _ (num 7) (regular f t (N + r) x h)
    (add_fast _ _ _ _ (regular f t N x hN) (range_regular f t N r x h)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] regularRows f t (Syn.shift N + Syn.shift r) (Syn.shift x) := by
    simpa only [Fm.shift, Syn.shift, subst_regularRows, PTm.subst_add] using h.shift
  simpa only [Syn.shift, subst_data, subst_rangeData, subst_addData, PTm.subst_add, PTm.subst_num] using
    range_sample f t (var 0) (Syn.shift N) (Syn.shift r) (Syn.shift x) hs

theorem actual_named_finite_family_range_regular_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (regularRows f t (var 0 + var 1) (var 2) ⟶ pointCN (nameF f (rangeBody t)) (rangeData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (range_regular f t _ _ _ Prf.hyp0))

theorem actual_named_finite_family_range_split_closed (f : PR 2) (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (regularRows f t (var 0 + var 1) (var 2) ⟶
        crossEquivalent (nameF f t) (addF (nameF f t) (nameF f (rangeBody t))) (data (var 0 + var 1) (var 2))
          (addData (data (var 0) (var 2)) (rangeData (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (range_cross f t _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyRange
