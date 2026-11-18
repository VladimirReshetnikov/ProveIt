import IPRADerivations.Analysis.GaussianDominantSyntax

/-!
# Actual scalar order reversal and positivity for dominant-term selection

The negative-score program swaps the two signed numerator components and
retains the decoded denominator. Both order reversal and value equality
are proved at those actual codes. Positive natural representations then
transfer nonzeroness through an actual rational comparison, with no
canonical-storage or supplied winner-positivity hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianDominantScalarOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalArgmin (left rationalLE rationalEq)
open LeanProofs.IPRA.Analysis.RationalValueBounds (negate)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem left_negate (a b : PTm n) : Γ ⊢[PRAAx] left (negate a) (negate b) ≐ left b a :=
  RationalValueBounds.crossLeft_negate b a

theorem negate_le (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE a b) : Γ ⊢[PRAAx]
    rationalLE (negate b) (negate a) :=
  le_congr (left_negate b a).eqSymm (left_negate a b).eqSymm h

theorem unnegate_le (a b : PTm n) (h : Γ ⊢[PRAAx] rationalLE (negate a) (negate b)) : Γ ⊢[PRAAx]
    rationalLE b a := le_congr (left_negate a b) (left_negate b a) h

theorem negate_le_iff (a b : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (rationalLE (negate a) (negate b)) (rationalLE b a) :=
  .iffI (.impI (unnegate_le a b Prf.hyp0)) (.impI (negate_le b a Prf.hyp0))

theorem negate_eq (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq a b) : Γ ⊢[PRAAx]
    rationalEq (negate a) (negate b) :=
  (left_negate a b).eqTrans (h.eqSymm.eqTrans (left_negate b a).eqSymm)

theorem unnegate_eq (a b : PTm n) (h : Γ ⊢[PRAAx] rationalEq (negate a) (negate b)) : Γ ⊢[PRAAx]
    rationalEq a b :=
  (left_negate b a).eqSymm.eqTrans (h.eqSymm.eqTrans (left_negate a b))

theorem negate_eq_iff (a b : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (rationalEq (negate a) (negate b)) (rationalEq a b) :=
  .iffI (.impI (unnegate_eq a b Prf.hyp0)) (.impI (negate_eq a b Prf.hyp0))

/-- A positive represented scalar cannot lie below a zero numerator.
Only the actual cross comparison and positive natural factors are used. -/
theorem positive_from_comparison (u v A B D E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hA : Γ ⊢[PRAAx] le one A)
    (hu : Γ ⊢[PRAAx] RationalArithmetic.represents u (ZT.ofNat A) D)
    (hv : Γ ⊢[PRAAx] RationalArithmetic.represents v (ZT.ofNat B) E)
    (h : Γ ⊢[PRAAx] rationalLE u v) : Γ ⊢[PRAAx] le one B := by
  have comparison := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _ hu hv h
  have positive := le_trans (GaussianRationalHorner.positive_product _ _ hE hA) comparison
  refine .orE (zero_or_succ B) ?_ ?_
  · have impossible : (B ≐ zero)::Γ ⊢[PRAAx] le one zero :=
      le_congr (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) positive.wk
    exact not_succ_le_self zero _ impossible
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem factor_positive_left (a b : PTm n) (h : Γ ⊢[PRAAx] le one (a*b)) : Γ ⊢[PRAAx] le one a := by
  refine .orE (zero_or_succ a) ?_ ?_
  · have impossible : (a ≐ zero)::Γ ⊢[PRAAx] le one zero :=
      le_congr (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)) h.wk
    exact not_succ_le_self zero _ impossible
  · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)

theorem negative_score_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (rationalLE (negate (var 0)) (negate (var 1))) (rationalLE (var 1) (var 0)) ⋏
      Fm.iff (rationalEq (negate (var 0)) (negate (var 1))) (rationalEq (var 0) (var 1))) :=
  closeUniv 2 (.andI (negate_le_iff _ _) (negate_eq_iff _ _))

theorem positive_comparison_numerator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ le one (var 2) ⟶
      RationalArithmetic.represents (var 0) (ZT.ofNat (var 2)) (var 4) ⟶
      RationalArithmetic.represents (var 1) (ZT.ofNat (var 3)) (var 5) ⟶
      rationalLE (var 0) (var 1) ⟶ le one (var 3)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI
    (positive_from_comparison _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianDominantScalarOrder
