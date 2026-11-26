import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic
import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers

/-!
# Literal rational values of the balanced dyadic-radius certificate

The returned radius is an actual normalized rational fraction. Its powers
use the actual PR rational-power program, multiplied by the original
Gaussian coefficient's squared norm. The finite natural scan comparison
is proved equivalent to the literal rational comparison, preserving every
original decoded denominator. The same genuine failed coefficient gives
the source strict squared balanced witness with factor 4^N.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusValues

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax
  (unit unit_positive subst_unit coefficient numerator denominator denominator_positive coefficient_norm_represents score cap fitAt)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents subst_fraction)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radius (E j : PTm n) : PTm n := fraction (unit j) (unit E)
def scaledNorm (C N E j i : PTm n) : PTm n := RationalArithmetic.multiply
  (GaussianRationalMetric.qnormSq (coefficient C N i))
  (RationalNonnegativePowers.power (unit j) (unit E) (two*i))
def scaledNumerator (C N j i : PTm n) : PTm n := numerator C N i*unit (two*j*i)
def scaledDenominator (C N E i : PTm n) : PTm n := denominator C N i*unit (two*E*i)
def weightedNorm (C N E j i : PTm n) : PTm n :=
  RationalArithmetic.multiply (fraction (pw (two*two) N) one) (scaledNorm C N E j i)

ipra_subst radius
ipra_subst scaledNorm
ipra_subst scaledNumerator
ipra_subst scaledDenominator
ipra_subst weightedNorm

theorem radius_represents (E j : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (radius E j) (ZT.ofNat (unit j)) (unit E) := fraction_represents _ _ (unit_positive E)

theorem radius_canonical (E j : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (radius E j) :=
  RationalNormalForm.normalize_well_formed _ _ (unit_positive E)

/-- The power numerator and denominator are actual powers of the literal
radius components, identified with the scan's natural exponents. -/
theorem radius_power (E j i : PTm n) : Γ ⊢[PRAAx]
    RationalNonnegativePowers.power (unit j) (unit E) (two*i) ≐
      fraction (unit (two*j*i)) (unit (two*E*i)) :=
  (RationalNonnegativePowers.dyadic_power j E (two*i)).eqTrans
    (RationalNonnegativePowers.fraction_congr (congrAp2 powF (by ipra_ring) (.eqRefl _))
      (congrAp2 powF (by ipra_ring) (.eqRefl _)))

theorem radius_power_represents (E j i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (RationalNonnegativePowers.power (unit j) (unit E) (two*i))
      (ZT.ofNat (unit (two*j*i))) (unit (two*E*i)) :=
  GaussianRationalHorner.scalar_congr (radius_power E j i).eqSymm (by apply ZT.derive; rfl) (.eqRefl _)
    (fraction_represents _ _ (unit_positive (two*E*i)))

theorem scaled_denominator_positive (C N E i : PTm n) : Γ ⊢[PRAAx] le one (scaledDenominator C N E i) :=
  positive_product _ _ (denominator_positive C N i) (unit_positive (two*E*i))

/-- Actual original squared norm times the actual positive rational power
has exactly the independent-denominator value used by the integer scan. -/
theorem scaledNorm_represents (C N E j i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (scaledNorm C N E j i) (ZT.ofNat (scaledNumerator C N j i)) (scaledDenominator C N E i) := by
  have h := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (coefficient_norm_represents C N i) (radius_power_represents E j i)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  unfold scaledNumerator
  ipra_simps

/-- The scan predicate is the literal source rational inequality, not an
assumed evaluator or common-denominator specification. -/
theorem fit_iff (C N E j i : PTm n) : Γ ⊢[PRAAx] Fm.iff (fitAt C N E j i)
    (RationalArgmin.rationalLE (scaledNorm C N E j i) (GaussianRationalMetric.qnormSq (coefficient C N zero))) := by
  refine .iffI (.impI ?_) (.impI ?_)
  · exact GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
      (scaled_denominator_positive C N E i) (denominator_positive C N zero)
      (scaledNorm_represents C N E j i) (coefficient_norm_represents C N zero)
      (le_congr (by unfold score scaledNumerator; ipra_ring) (by unfold cap scaledDenominator; ipra_ring) Prf.hyp0)
  · have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (scaledNorm_represents (Γ := Γ) C N E j i).wk (coefficient_norm_represents (Γ := Γ) C N zero).wk Prf.hyp0
    exact le_congr (by unfold score scaledNumerator; ipra_ring) (by unfold cap scaledDenominator; ipra_ring) raw

/-- The next scanned fraction is literally twice the returned radius
under the original canonical rational multiplication operation. -/
theorem radius_double (E j : PTm n) : Γ ⊢[PRAAx]
    radius E (succ j) ≐ RationalArithmetic.multiply (radius E j) (fraction two one) :=
  (RationalNonnegativePowers.fraction_congr (pw_succ two j) (.eqRefl _)).eqTrans
    ((RationalNonnegativePowers.fraction_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] unit E*one ≐ unit E).eqSymm).eqTrans
      (RationalNonnegativePowers.fraction_multiply (unit j) (unit E) two one (unit_positive E) (le_refl _)).eqSymm)

theorem weightedNorm_represents (C N E j i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (weightedNorm C N E j i)
      (ZT.ofNat (pw (two*two) N*scaledNumerator C N j i)) (scaledDenominator C N E i) := by
  have h := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents (pw (two*two) N) one (le_refl _)) (scaledNorm_represents C N E j i)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := LeanProofs.IPRA.one_mul _) (h := h)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

/-- Strict failure of the balanced integer comparison refutes the actual
opposite rational ordering, cancelling only positive decoded denominators. -/
theorem not_le_of_balanced_witness (C N E j i : PTm n)
    (h : Γ ⊢[PRAAx] lt (cap C N E i) (pw (two*two) N*score C N E j i)) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (weightedNorm C N E j i) (GaussianRationalMetric.qnormSq (coefficient C N zero))) := by
  refine .impI ?_
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (weightedNorm_represents (Γ := Γ) C N E j i).wk (coefficient_norm_represents (Γ := Γ) C N zero).wk Prf.hyp0
  have opposite : (RationalArgmin.rationalLE (weightedNorm C N E j i) (GaussianRationalMetric.qnormSq (coefficient C N zero)))::Γ ⊢[PRAAx]
      le (pw (two*two) N*score C N E j i) (cap C N E i) :=
    le_congr (by unfold scaledNumerator score; ipra_ring) (by unfold scaledDenominator cap; ipra_ring) raw
  exact le_lt_absurd Fm.bot opposite h.wk

/-- A genuine doubled-radius failed comparison gives the exact source
rational squared balanced witness at the same original stored index. -/
theorem balanced_not_le (C N E j i : PTm n) (hiN : Γ ⊢[PRAAx] le i N)
    (hFail : Γ ⊢[PRAAx] lt (cap C N E i) (score C N E (succ j) i)) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (RationalArithmetic.multiply (fraction (pw (two*two) N) one) (scaledNorm C N E j i))
      (GaussianRationalMetric.qnormSq (coefficient C N zero))) :=
  not_le_of_balanced_witness C N E j i (GaussianBalancedRadiusArithmetic.actual_balanced_witness C N E j i hiN hFail)

theorem radius_nonnegative (E j : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (radius E j) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl _) (unit_positive E)
    (fraction_represents _ _ (le_refl _)) (radius_represents E j)
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le (unit j)))

theorem radius_positive (E j : PTm n) : Γ ⊢[PRAAx]
    neg (RationalArgmin.rationalLE (radius E j) (fraction zero one)) := by
  refine .impI ?_
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (radius_represents (Γ := Γ) E j).wk (fraction_represents (Γ := Γ) zero one (le_refl _)).wk Prf.hyp0
  have opposite : (RationalArgmin.rationalLE (radius E j) (fraction zero one))::Γ ⊢[PRAAx] le (unit j) zero :=
    le_congr (one_mul _) (zero_mul _) raw
  exact le_lt_absurd Fm.bot opposite (unit_positive j)

theorem scaledNorm_canonical (C N E j i : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (scaledNorm C N E j i) :=
  RationalArithmetic.multiply_guard _ _

theorem scaledNorm_nonnegative (C N E j i : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fraction zero one) (scaledNorm C N E j i) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (le_refl _) (scaled_denominator_positive C N E i)
    (fraction_represents _ _ (le_refl _)) (scaledNorm_represents C N E j i)
    (le_congr (by ipra_ring) (by ipra_ring) (zero_le (scaledNumerator C N j i)))

/-- Literal canonical equality with the independently denominated fraction
used in the source scan, rather than merely equality of an interpretation. -/
theorem scaledNorm_fraction (C N E j i : PTm n) : Γ ⊢[PRAAx]
    scaledNorm C N E j i ≐ fraction (scaledNumerator C N j i) (scaledDenominator C N E i) := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (scaledNorm_canonical C N E j i)
    (RationalNormalForm.normalize_well_formed _ _ (scaled_denominator_positive C N E i))
    (scaledNorm_represents C N E j i) (fraction_represents _ _ (scaled_denominator_positive C N E i))
    (scaled_denominator_positive C N E i) (scaled_denominator_positive C N E i)
  apply ZT.derive
  rfl

/-! The actual PR5 output carries the normalized radius and both literal
squared-norm values, together with the exact natural scale fields. -/
def output (C N E j i : PTm n) : PTm n := pairT (radius E j)
  (pairT (scaledNorm C N E j i) (pairT (weightedNorm C N E j i)
    (pairT (scaledNumerator C N j i) (scaledDenominator C N E i))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))

ipra_subst output

theorem program_at (C N E j i : PTm n) : Γ ⊢[PRAAx] PTm.app outputF ![C,N,E,j,i] ≐ output C N E j i := by
  simpa [outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,N,E,j,i]

theorem balanced_radius_fit_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (fitAt (var 0) (var 1) (var 2) (var 3) (var 4))
      (RationalArgmin.rationalLE (scaledNorm (var 0) (var 1) (var 2) (var 3) (var 4))
        (GaussianRationalMetric.qnormSq (coefficient (var 0) (var 1) zero)))) := closeUniv 5 (fit_iff _ _ _ _ _)

theorem balanced_radius_double_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (radius (var 0) (succ (var 1)) ≐ RationalArithmetic.multiply (radius (var 0) (var 1)) (fraction two one)) :=
  closeUniv 2 (radius_double _ _)

theorem balanced_radius_literal_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (var 4) (var 1) ⟶
      lt (cap (var 0) (var 1) (var 2) (var 4)) (score (var 0) (var 1) (var 2) (succ (var 3)) (var 4)) ⟶
        neg (RationalArgmin.rationalLE
          (RationalArithmetic.multiply (fraction (pw (two*two) (var 1)) one) (scaledNorm (var 0) (var 1) (var 2) (var 3) (var 4)))
          (GaussianRationalMetric.qnormSq (coefficient (var 0) (var 1) zero)))) :=
  closeUniv 5 (.impI (.impI (balanced_not_le _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem balanced_radius_value_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (scaledDenominator (var 0) (var 1) (var 2) (var 4))) ⋏
      (RationalArithmetic.represents (scaledNorm (var 0) (var 1) (var 2) (var 3) (var 4))
        (ZT.ofNat (scaledNumerator (var 0) (var 1) (var 3) (var 4))) (scaledDenominator (var 0) (var 1) (var 2) (var 4)) ⋏
       scaledNorm (var 0) (var 1) (var 2) (var 3) (var 4) ≐
         fraction (scaledNumerator (var 0) (var 1) (var 3) (var 4)) (scaledDenominator (var 0) (var 1) (var 2) (var 4)))) :=
  closeUniv 5 (.andI (scaled_denominator_positive _ _ _ _) (.andI (scaledNorm_represents _ _ _ _ _) (scaledNorm_fraction _ _ _ _ _)))

theorem balanced_radius_positive_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((RationalNormalForm.wellFormed (radius (var 0) (var 1))) ⋏
      (RationalArgmin.rationalLE (fraction zero one) (radius (var 0) (var 1)) ⋏
        neg (RationalArgmin.rationalLE (radius (var 0) (var 1)) (fraction zero one)))) :=
  closeUniv 2 (.andI (radius_canonical _ _) (.andI (radius_nonnegative _ _) (radius_positive _ _)))

theorem balanced_radius_values_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (PTm.app outputF ![var 0,var 1,var 2,var 3,var 4] ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusValues
