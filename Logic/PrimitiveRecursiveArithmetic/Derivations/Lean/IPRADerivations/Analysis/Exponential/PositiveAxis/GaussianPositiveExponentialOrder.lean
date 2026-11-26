import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialTermBound
import IPRADerivations.Analysis.Exponential.Polynomials.GaussianFiniteExponentialWeightedNorm

/-!
# Order of the original finite exponential on the nonnegative real axis

Both genuine QF inductions use the original normalized Gaussian power
and finite factorial sum. Input order compares the original real scalar
coordinates; every output positivity and axis condition is derived.
The fraction endpoint retains arbitrary positive denominators and all
numerical cutoffs. Signed named exponential order is a separate consumer.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveExponentialOrder

open_ipra
open GaussianPositiveRealArithmetic (positive positive_power positive_inverse_factorial)
open GaussianPositiveExponentialProduct (real_product)
open GaussianRationalReciprocal (power power_zero power_succ)
open GaussianRationalPolynomialExponential (scalarSum scalarBody inverseFactorial)
open GaussianRationalExponentialTail (scalarPrefix prefix_succ)
open GaussianScalarExponentialDiagonal (coefficient)
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianDominantPairAlgebra (radiusPoint radius_represents radiusNumerator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powerOrder (u v k : PTm n) : Fm PTm n := rationalLE (fstT (power u k)) (fstT (power v k))
ipra_subst powerOrder

theorem power_order_zero (u v : PTm n) : Γ ⊢[PRAAx] powerOrder u v zero :=
  rationalLE_congr (congrFst (power_zero u)).eqSymm (congrFst (power_zero v)).eqSymm (RationalArgmin.reflexive _)

theorem power_order_step (u v k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v))
    (ih : Γ ⊢[PRAAx] powerOrder u v k) : Γ ⊢[PRAAx] powerOrder u v (succ k) := by
  have a := (congrFst (power_succ (Γ := Γ) u k)).eqTrans (real_product _ _ hu.andE₁)
  have b := (congrFst (power_succ (Γ := Γ) v k)).eqTrans (real_product _ _ hv.andE₁)
  exact rationalLE_congr a.eqSymm b.eqSymm
    (GaussianFiniteExponentialWeightedNorm.multiply_bounds _ _ _ _ hu.andE₂ (positive_power v k hv).andE₂ ih huv)

theorem power_monotone (u v k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v)) :
    Γ ⊢[PRAAx] powerOrder u v k := by
  have us : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift u) := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift v) := by simpa [Fm.shift,Syn.shift] using hv.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (fstT (Syn.shift u)) (fstT (Syn.shift v)) :=
    by simpa [Fm.shift,Syn.shift] using huv.shift
  have all : Γ ⊢[PRAAx] .all (powerOrder (Syn.shift u) (Syn.shift v) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_powerOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using power_order_zero u v
    · simp only [subst_powerOrder,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact power_order_step _ _ _ us.wk vs.wk hs.wk Prf.hyp0
  simpa only [subst_powerOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem coefficient_monotone (u v k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v)) : Γ ⊢[PRAAx]
    rationalLE (fstT (coefficient u k)) (fstT (coefficient v k)) :=
  rationalLE_congr (real_product (inverseFactorial k) (power u k) (positive_power u k hu).andE₁).eqSymm
    (real_product (inverseFactorial k) (power v k) (positive_power v k hv).andE₁).eqSymm
    (RationalArithmetic.multiply_monotone _ _ _ (positive_inverse_factorial k).andE₂ (power_monotone u v k hu hv huv))

def prefixOrder (u v k : PTm n) : Fm PTm n := rationalLE (fstT (scalarPrefix u k)) (fstT (scalarPrefix v k))
ipra_subst prefixOrder [scalarPrefix]

theorem prefix_order_zero (u v : PTm n) : Γ ⊢[PRAAx] prefixOrder u v zero :=
  rationalLE_congr (congrFst (GaussianRationalFiniteSum.sum_zero scalarBody u)).eqSymm
    (congrFst (GaussianRationalFiniteSum.sum_zero scalarBody v)).eqSymm (RationalArgmin.reflexive _)

theorem prefix_order_step (u v k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v))
    (ih : Γ ⊢[PRAAx] prefixOrder u v k) : Γ ⊢[PRAAx] prefixOrder u v (succ k) := by
  have a := (congrFst (prefix_succ (Γ := Γ) u k)).eqTrans (RationalGaussianRealPart.real_add _ _)
  have b := (congrFst (prefix_succ (Γ := Γ) v k)).eqTrans (RationalGaussianRealPart.real_add _ _)
  exact rationalLE_congr a.eqSymm b.eqSymm (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ ih
    (coefficient_monotone u v k hu hv huv))

theorem prefix_monotone (u v k : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v)) :
    Γ ⊢[PRAAx] prefixOrder u v k := by
  have us : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift u) := by simpa [Fm.shift,Syn.shift] using hu.shift
  have vs : Γ.map Fm.shift ⊢[PRAAx] positive (Syn.shift v) := by simpa [Fm.shift,Syn.shift] using hv.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (fstT (Syn.shift u)) (fstT (Syn.shift v)) :=
    by simpa [Fm.shift,Syn.shift] using huv.shift
  have all : Γ ⊢[PRAAx] .all (prefixOrder (Syn.shift u) (Syn.shift v) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simpa only [subst_prefixOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using prefix_order_zero u v
    · simp only [subst_prefixOrder,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact prefix_order_step _ _ _ us.wk vs.wk hs.wk Prf.hyp0
  simpa only [subst_prefixOrder,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k

theorem scalar_sum_monotone (u v K : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v)) : Γ ⊢[PRAAx]
    rationalLE (fstT (scalarSum u K)) (fstT (scalarSum v K)) :=
  prefix_monotone u v (succ K) hu hv huv

theorem argument_and_cutoff_monotone (u v K L : PTm n) (hu : Γ ⊢[PRAAx] positive u)
    (hv : Γ ⊢[PRAAx] positive v) (huv : Γ ⊢[PRAAx] rationalLE (fstT u) (fstT v))
    (hKL : Γ ⊢[PRAAx] le K L) : Γ ⊢[PRAAx]
    rationalLE (fstT (scalarSum u K)) (fstT (scalarSum v L)) :=
  RationalArgmin.transitive (scalar_sum_monotone u v K hu hv huv)
    (GaussianPositiveExponentialTermBound.prefix_real_mono v (succ K) (succ L) hv ((succ_monus_succ K L).eqTrans hKL))

theorem radius_real_representation (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (radiusPoint a b)) (ZT.ofNat a) b :=
  GaussianRationalHorner.scalar_congr (.eqRefl _) (by
    apply ZT.derive
    simp only [radiusNumerator,ComplexLogarithmRemainder.eval_re_code]) (.eqRefl _) (radius_represents a b hb).andE₁

/-- The order premise is the original cross-multiplied fraction order;
neither exponential output order nor coefficient order is assumed. -/
theorem original_fraction_order (a b c d K : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hd : Γ ⊢[PRAAx] le one d) (h : Γ ⊢[PRAAx] le (a*d) (c*b)) : Γ ⊢[PRAAx]
    rationalLE (fstT (scalarSum (radiusPoint a b) K)) (fstT (scalarSum (radiusPoint c d) K)) :=
  scalar_sum_monotone _ _ K (GaussianPositiveExponentialTermBound.actual_positive_fraction a b hb)
    (GaussianPositiveExponentialTermBound.actual_positive_fraction c d hd)
    (GaussianRationalMetric.comparison_of_cleared _ _ a c b d hb hd
      (radius_real_representation a b hb) (radius_real_representation c d hd)
      (le_congr (mul_comm a d) (.eqRefl _) h))

theorem original_nonnegative_power_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (positive (var 0) ⟶ positive (var 1) ⟶ rationalLE (fstT (var 0)) (fstT (var 1)) ⟶ powerOrder (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (.impI (.impI (power_monotone _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_nonnegative_finite_exponential_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (positive (var 0) ⟶ positive (var 1) ⟶ rationalLE (fstT (var 0)) (fstT (var 1)) ⟶
      rationalLE (fstT (scalarSum (var 0) (var 2))) (fstT (scalarSum (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (scalar_sum_monotone _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_positive_fraction_exponential_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le (var 0*var 3) (var 2*var 1) ⟶
      rationalLE (fstT (scalarSum (radiusPoint (var 0) (var 1)) (var 4)))
        (fstT (scalarSum (radiusPoint (var 2) (var 3)) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (original_fraction_order _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianPositiveExponentialOrder
