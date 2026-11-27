import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.Taylor.GaussianLogGammaEulerTaylorMajorant
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds
import IPRADerivations.Analysis.Integration.Quadrature.GaussianRationalQuadratureDifference

/-!
# Uniform continuity of the finite complex reciprocal sums

Each input has real part at least `1/M`. The zeroth reciprocal row
has Lipschitz coefficient `M²`. Integer translation preserves the
input distance, and the remaining reciprocal rows have coefficients
`1/k²`, whose literal finite sum is at most two.
-/

set_option autoImplicit false
set_option maxHeartbeats 450000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerSlopeContinuity

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction_represents)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint reciprocalSum rowBody row_at shifted_lower)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianNameReciprocal (inverse_difference inverse_distance_two)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalFiniteSum (sum_shift_first)
open GaussianRationalHorner (positive_product ofGaussian_represents qmul)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical comparison_to_cleared)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at finite_sum_difference)
open GaussianRationalReciprocal (reciprocal inverse_bound norm_positive bound_congr bounded_product bounded_sum)
open GaussianRationalSumMajorant (majorized termsMajorized majorized_congr from_representation sum_majorized)
open GaussianRationalSyntheticDivision (qadd_congr qzero_add qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)
open RationalAlgebra (multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (multiply_monotone)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rf" => GaussianEuclideanDistanceName.fraction
local notation "gf" => GaussianPositiveRationalLogarithm.fraction
local notation "sum" => GaussianRationalFiniteSum.sum

def input (A D neg a d sign M : PTm n) : Fm PTm n :=
  source A D neg ⋏ (source a d sign ⋏ (le one M ⋏ (le D (M * A) ⋏ le d (M * a))))

ipra_subst input [source, GaussianRightHalfPlaneArgument.source]

private theorem translated_distance (z w k H E : PTm n) (h : Γ ⊢[PRAAx] distanceBounded z w H E) :
    Γ ⊢[PRAAx] distanceBounded (shiftedPoint z k) (shiftedPoint w k) H E := by
  let q := gf k one
  have e : Γ ⊢[PRAAx] qsub (shiftedPoint z k) (shiftedPoint w k) ≐ qsub z w :=
    (GaussianNameArithmetic.sum_difference q q z w).eqTrans
      ((qadd_congr (GaussianCoefficientNormOrder.qsub_self q) (.eqRefl _)).eqTrans
        (qzero_add _ (qsub_canonical z w)))
  exact bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) h

private theorem shifted_margin (A B D neg M k : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) (hD : Γ ⊢[PRAAx] le D (M * A)) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.lower (shiftedPoint (argument A B D neg) k) M := by
  let a := A + k * D
  let z := native a B neg
  let q := argument a B D neg
  have hd := h.andE₂
  have size : Γ ⊢[PRAAx] le (D * D) ((M * M) * (a * a)) := by
    have hd' := le_trans hD (le_mul_mono (le_refl M) (le_add_right A (k * D)))
    exact le_congr (.eqRefl _) (by dsimp only [a]; ipra_ring) (le_mul_mono hd' hd')
  have norm := native_norm a B neg h.andE₁.andE₂
  have hn : Γ ⊢[PRAAx] le (a * a) (ComplexLogarithmRemainder.normSq z) :=
    le_congr (.eqRefl _) norm.eqSymm (le_add_right _ _)
  have clear := le_trans size (le_mul_mono (le_refl (M * M)) hn)
  have result : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q M :=
    GaussianRationalLowerBounds.lower_from_representation q z D one M hd hM
      (ofGaussian_represents z D hd) (le_congr (by ipra_ring) (.eqRefl _) clear)
  exact GaussianNameReciprocal.lower_congr (GaussianLogGammaEulerLinearSlope.shifted_point A B D neg k hd).eqSymm
    (.eqRefl _) result

private theorem first_error (A B D neg a b d sign M H E : PTm n) (h : Γ ⊢[PRAAx] input A D neg a d sign M)
    (hE : Γ ⊢[PRAAx] le one E) (close : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] distanceBounded (reciprocal (shiftedPoint (argument A B D neg) zero))
      (reciprocal (shiftedPoint (argument a b d sign) zero)) (M * M * H) E := by
  let z := argument A B D neg
  let w := argument a b d sign
  have hM := h.andE₂.andE₂.andE₁
  exact inverse_distance_two (shiftedPoint z zero) (shiftedPoint w zero) M M H E hM hM hE
    (shifted_margin A B D neg M zero h.andE₁ hM h.andE₂.andE₂.andE₂.andE₁)
    (shifted_margin a b d sign M zero h.andE₂.andE₁ hM h.andE₂.andE₂.andE₂.andE₂)
    (translated_distance z w zero H E close)

private theorem positive_error (A B D neg a b d sign k H E : PTm n)
    (hz : Γ ⊢[PRAAx] source A D neg) (hw : Γ ⊢[PRAAx] source a d sign)
    (hk : Γ ⊢[PRAAx] le one k) (hE : Γ ⊢[PRAAx] le one E)
    (close : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] distanceBounded (reciprocal (shiftedPoint (argument A B D neg) k))
      (reciprocal (shiftedPoint (argument a b d sign) k)) H (E * (k * k)) := by
  let z := argument A B D neg
  let w := argument a b d sign
  let u := shiftedPoint z k
  let v := shiftedPoint w k
  have lu := shifted_lower A B D neg k hz
  have lv := shifted_lower a b d sign k hw
  have near := translated_distance z w k H E close
  have first := bounded_product (reciprocal u) (qsub v u) one k H E hk hE
    (inverse_bound u k hk lu) (distance_symmetric u v H E hE near)
  have second := bounded_product (qmul (reciprocal u) (qsub v u)) (reciprocal v) (one * H) (k * E) one k
    (positive_product _ _ hk hE) hk first (inverse_bound v k hk lv)
  exact bound_congr (inverse_difference u v (norm_positive u k hk lu) (norm_positive v k hk lv)).eqSymm
    (by ipra_ring) (by ipra_ring) second

private abbrev difference := differenceBody rowBody rowBody
private abbrev budgetBody := scaledBody RationalReciprocalPowerTail.body
private def budgetData (H E : PTm n) : PTm n := pairT (rf H E) (RationalReciprocalPowerTail.data two zero)

private theorem budget_at (H E i : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] inst2 budgetBody i (budgetData H E) ≐ rf H (E * (succ i * succ i)) := by
  let k := succ i
  let j := succ (zero + i)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have read : Γ ⊢[PRAAx] inst2 RationalReciprocalPowerTail.body i (RationalReciprocalPowerTail.data two zero) ≐ rf one (k * k) := by
    have e : Γ ⊢[PRAAx] pw j two ≐ k * k :=
      (congrAp2 powF (.eqRefl two) (congrSucc (zero_add i))).eqTrans
        ((pw_succ k one).eqTrans (congrMul (pw_one k) (.eqRefl _)))
    exact (RationalReciprocalPowerTail.term_at (Γ := Γ) two zero i).eqTrans (fraction_congr (.eqRefl _) e)
  exact (scaled_term RationalReciprocalPowerTail.body i (rf H E) (RationalReciprocalPowerTail.data two zero)).eqTrans
    ((multiply_congr (.eqRefl _) read).eqTrans
      ((fraction_multiply H E one (k * k) hE (positive_product _ _ hk hk)).eqTrans
        (fraction_congr (by ipra_ring) (.eqRefl _))))

private theorem positive_majorized (A B D neg a b d sign H E i : PTm n)
    (hz : Γ ⊢[PRAAx] source A D neg) (hw : Γ ⊢[PRAAx] source a d sign) (hE : Γ ⊢[PRAAx] le one E)
    (close : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] majorized (inst2 (shiftBody difference) i (pairT (argument A B D neg) (argument a b d sign)))
      (inst2 budgetBody i (budgetData H E)) := by
  let z := argument A B D neg
  let w := argument a b d sign
  let k := succ i
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hd := positive_product _ _ hE (positive_product _ _ hk hk)
  have rep := fraction_represents H (E * (k * k)) hd
  have nonnegative := GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep
  have eq := (difference_body_at (Γ := Γ) rowBody rowBody k z w).eqTrans (qsub_congr (row_at z k) (row_at w k))
  rw [inst2_shiftBody]
  exact majorized_congr eq.eqSymm (budget_at H E i hE).eqSymm
    (from_representation _ _ H _ hd nonnegative rep (positive_error A B D neg a b d sign k H E hz hw hk hE close))

private theorem scalar_upper (H E N : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] rationalLE (RationalFiniteSum.sum budgetBody N (budgetData H E)) (rf (two * H) E) := by
  let q := rf H E
  have sign := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) q H E hE (fraction_represents H E hE)
  have bound := multiply_monotone q _ _ sign (GaussianLogGammaEulerTaylorMajorant.positive_square_sum N)
  exact rationalLE_congr
    (sum_homogeneous RationalReciprocalPowerTail.body N q (RationalReciprocalPowerTail.data two zero)).eqSymm
    ((fraction_multiply H E two one hE (le_refl one)).eqTrans (fraction_congr (mul_comm H two) (by ipra_ring))) bound

private theorem positive_sum (A B D neg a b d sign H E N : PTm n)
    (hz : Γ ⊢[PRAAx] source A D neg) (hw : Γ ⊢[PRAAx] source a d sign) (hE : Γ ⊢[PRAAx] le one E)
    (close : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] bounded (sum (shiftBody difference) N (pairT (argument A B D neg) (argument a b d sign))) (two * H) E := by
  let z := argument A B D neg
  let w := argument a b d sign
  let v := sum (shiftBody difference) N (pairT z w)
  let m := RationalFiniteSum.sum budgetBody N (budgetData H E)
  have rows : Γ ⊢[PRAAx] termsMajorized (shiftBody difference) budgetBody N (pairT z w) (budgetData H E) := by
    refine .allI (.impI ?_)
    let s (t : PTm n) := Syn.shift t
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] source (s A) (s D) (s neg) := by
      simpa [Δ, s, Fm.shift, Syn.shift, source, GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have hw' : Δ ⊢[PRAAx] source (s a) (s d) (s sign) := by
      simpa [Δ, s, Fm.shift, Syn.shift, source, GaussianRightHalfPlaneArgument.source] using hw.shift.wk
    have he : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ, s, Fm.shift, Syn.shift] using hE.shift.wk
    have hdist : Δ ⊢[PRAAx] distanceBounded (argument (s A) (s B) (s D) (s neg)) (argument (s a) (s b) (s d) (s sign))
        (s H) (s E) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, GaussianRationalMetric.subst_distanceBounded, subst_argument] using close.shift.wk
    simpa only [Δ, s, z, w, Syn.shift, subst_pairT, subst_argument, budgetData, GaussianEuclideanDistanceName.subst_fraction,
      RationalReciprocalPowerTail.subst_data, two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
      positive_majorized (s A) (s B) (s D) (s neg) (s a) (s b) (s d) (s sign) (s H) (s E) (var 0) hz' hw' he hdist
  have estimate : Γ ⊢[PRAAx] majorized v m := sum_majorized _ _ _ _ _ rows
  have clear := comparison_to_cleared m (rf (two * H) E) (GaussianPositiveRealArithmetic.numerator m) (two * H)
    (denominatorOf m) E (GaussianPositiveRealArithmetic.natural_representation m estimate.andE₁)
    (fraction_represents _ _ hE) (scalar_upper H E N hE)
  exact bounded_radius_mono v _ _ _ _ (RationalArgmin.denominator_positive m) hE
    (le_congr (mul_comm _ _) (.eqRefl _) clear) estimate.andE₂

def coefficient (M : PTm n) : PTm n := M * M + two

/-- Uniform estimate for the actual finite reciprocal sums on a common right half-plane margin. -/
theorem reciprocal_sum_lipschitz (A B D neg a b d sign M H E N : PTm n)
    (h : Γ ⊢[PRAAx] input A D neg a d sign M) (hE : Γ ⊢[PRAAx] le one E)
    (close : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] distanceBounded (reciprocalSum A B D neg (succ N)) (reciprocalSum a b d sign (succ N))
      (coefficient M * H) E := by
  let z := argument A B D neg
  let w := argument a b d sign
  let c := inst2 difference zero (pairT z w)
  let t := sum (shiftBody difference) N (pairT z w)
  have first : Γ ⊢[PRAAx] bounded c (M * M * H) E := by
    have eq := (difference_body_at rowBody rowBody (Γ := Γ) zero z w).eqTrans
      (qsub_congr (row_at z zero) (row_at w zero))
    exact bound_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (first_error A B D neg a b d sign M H E h hE close)
  have rest := positive_sum A B D neg a b d sign H E N h.andE₁ h.andE₂.andE₁ hE close
  have total := bounded_sum c t (M * M * H) E (two * H) E hE hE first rest
  have smaller := bounded_radius_mono _ _ _ (coefficient M * H) E (positive_product _ _ hE hE) hE
    (le_of_eq_add (d := zero) (by unfold coefficient; ipra_ring)) total
  have eq := (sum_shift_first (Γ := Γ) difference N (pairT z w)).eqSymm.eqTrans
    (finite_sum_difference rowBody rowBody (succ N) z w)
  exact bound_congr eq (.eqRefl _) (.eqRefl _) smaller

theorem actual_complex_finite_reciprocal_sum_Lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
      (input (var 0) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8) ⟶ le one (var 10) ⟶
        distanceBounded (argument (var 0) (var 1) (var 2) (var 3)) (argument (var 4) (var 5) (var 6) (var 7))
          (var 9) (var 10) ⟶
        distanceBounded (reciprocalSum (var 0) (var 1) (var 2) (var 3) (succ (var 11)))
          (reciprocalSum (var 4) (var 5) (var 6) (var 7) (succ (var 11))) (coefficient (var 8) * var 9) (var 10)) :=
  closeUniv 12 (.impI (.impI (.impI (reciprocal_sum_lipschitz _ _ _ _ _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerSlopeContinuity
