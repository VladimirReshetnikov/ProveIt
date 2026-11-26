import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalThreeTermBudget
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerAlgebra
import IPRADerivations.Core.LinearCombination

/-!
# Two actual rational Gaussian terms with a common relative norm bound

The actual original points determine a common positive denominator. The
native relative Euclidean triangle proves the sum estimate after scaling
both numerators by the common natural relative denominator L. No point
norm, weight or L is cancelled, so zero values remain valid. Negation,
canonical recoding, norm-order comparison and an actual unit-disk product
retain their exact relative bounds. All numerical values are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRelativeTwoTerm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul represents positive_product qadd_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq qnegative qsub bounded)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalRelativeNormAlgebra (relative)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale add zeroCode)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem norm_order_relative (u v : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq u) (qnormSq v)) : Γ ⊢[PRAAx]
    relative u one one v :=
  GaussianRationalRelativeNormAlgebra.of_cleared _ _ _ _ (le_congr (by ipra_ring) (by ipra_ring)
    (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
      (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive u) (raw_represents u))
      (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive v) (raw_represents v)) h))

theorem relative_norm_order (u v : PTm n) (h : Γ ⊢[PRAAx] relative u one one v) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (qnormSq u) (qnormSq v) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _
    (positive_product _ _ (raw_den_positive u) (raw_den_positive u))
    (positive_product _ _ (raw_den_positive v) (raw_den_positive v))
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive u) (raw_represents u))
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive v) (raw_represents v))
    (le_congr (by ipra_ring) (by ipra_ring) (GaussianRationalRelativeNormAlgebra.to_cleared u one one v h))

/-- No sign, point nonzeroness or positivity of the common relative
denominator L is needed for the two-term squared Euclidean estimate. -/
theorem relative_add (u v W V L base : PTm n)
    (hu : Γ ⊢[PRAAx] relative u W L base) (hv : Γ ⊢[PRAAx] relative v V L base) : Γ ⊢[PRAAx]
    relative (qadd u v) (W+V) L base := by
  let E := GaussianRationalThreeTermBudget.denominator u v qzero base
  let a := GaussianRationalThreeTermBudget.numerator0 u v qzero base
  let b := GaussianRationalThreeTermBudget.numerator1 u v qzero base
  let d := GaussianRationalThreeTermBudget.numeratorBase u v qzero base
  have hE : Γ ⊢[PRAAx] le one E := GaussianRationalThreeTermBudget.denominator_positive u v qzero base
  have pu : Γ ⊢[PRAAx] represents u a E := GaussianRationalThreeTermBudget.first_represents u v qzero base
  have pv : Γ ⊢[PRAAx] represents v b E := GaussianRationalThreeTermBudget.second_represents u v qzero base
  have pb : Γ ⊢[PRAAx] represents base d E := GaussianRationalThreeTermBudget.base_represents u v qzero base
  have au := GaussianRationalRelativeNormAlgebra.relative_to_cleared u base a d E W L hE pu pb hu
  have av := GaussianRationalRelativeNormAlgebra.relative_to_cleared v base b d E V L hE pv pb hv
  have su : Γ ⊢[PRAAx] le (normSq (scale L a)) (W*W*normSq d) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale L a).eqSymm (.eqRefl _) au
  have sv : Γ ⊢[PRAAx] le (normSq (scale L b)) (V*V*normSq d) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale L b).eqSymm (.eqRefl _) av
  have triangle := GaussianRelativeNormTriangle.relative_triangle _ _ _ _ _ su sv
  have actual : Γ ⊢[PRAAx] le (L*L*normSq (add a b)) ((W+V)*(W+V)*normSq d) :=
    le_congr (GaussianRationalNormClearing.norm_sum_scaled L a b) (.eqRefl _) triangle
  exact GaussianRationalRelativeNormAlgebra.from_representations (qadd u v) base (add a b) d E E (W+V) L hE hE
    (qadd_represents u v a b E hE pu pv) pb
    (mul_le_mul_right (E*E) actual)

theorem sum_bound (u v W V base : PTm n)
    (hu : Γ ⊢[PRAAx] relative u W one base) (hv : Γ ⊢[PRAAx] relative v V one base) : Γ ⊢[PRAAx]
    relative (qadd u v) (W+V) one base := relative_add u v W V one base hu hv

theorem norm_of_representations (q r a b D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a D) (hr : Γ ⊢[PRAAx] represents r b D)
    (hNorm : Γ ⊢[PRAAx] normSq a ≐ normSq b) : Γ ⊢[PRAAx] qnormSq q ≐ qnormSq r := by
  have hDD := positive_product D D hD hD
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (GaussianRationalMetric.qnormSq_canonical _)
    (GaussianRationalMetric.qnormSq_canonical _) (GaussianRationalMetric.qnormSq_represents _ _ _ hD hq)
    (GaussianRationalMetric.qnormSq_represents _ _ _ hD hr) hDD hDD
  ipra_lc 𝔞(D)*𝔞(D)*natEq hNorm

theorem norm_negative (q : PTm n) : Γ ⊢[PRAAx] qnormSq (qnegative q) ≐ qnormSq q :=
  norm_of_representations _ _ _ _ (rawDen q) (raw_den_positive q)
    (GaussianRationalMetric.qnegative_represents q (rawGaussian q) (rawDen q) (raw_represents q)) (raw_represents q)
    (ComplexLogarithmRemainder.normSq_neg _)

theorem norm_recode (q : PTm n) : Γ ⊢[PRAAx] qnormSq (qadd qzero q) ≐ qnormSq q := by
  apply norm_of_representations _ _ _ _ (rawDen q) (raw_den_positive q)
    (qadd_represents qzero q zeroCode (rawGaussian q) (rawDen q) (raw_den_positive q)
      (GaussianRationalHorner.zero_represents _) (raw_represents q)) (raw_represents q)
  apply GaussianRootAlgebra.normSq_equal
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero]; ring

theorem relative_negative (u W L base : PTm n) (h : Γ ⊢[PRAAx] relative u W L base) : Γ ⊢[PRAAx]
    relative (qnegative u) W L base :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _) (norm_negative u).eqSymm) (.eqRefl _) h
theorem relative_recode (u W L base : PTm n) (h : Γ ⊢[PRAAx] relative u W L base) : Γ ⊢[PRAAx]
    relative (qadd qzero u) W L base :=
  RationalArgmin.rationalLE_congr (RationalAlgebra.multiply_congr (.eqRefl _) (norm_recode u).eqSymm) (.eqRefl _) h

theorem relative_sub (u v W V L base : PTm n)
    (hu : Γ ⊢[PRAAx] relative u W L base) (hv : Γ ⊢[PRAAx] relative v V L base) : Γ ⊢[PRAAx]
    relative (qsub u v) (W+V) L base :=
  relative_add u (qnegative v) W V L base hu (relative_negative v V L base hv)
theorem sub_bound (u v W V base : PTm n)
    (hu : Γ ⊢[PRAAx] relative u W one base) (hv : Γ ⊢[PRAAx] relative v V one base) : Γ ⊢[PRAAx]
    relative (qsub u v) (W+V) one base := relative_sub u v W V one base hu hv

/-- A genuine disk bound on the multiplied point supplies the product
law; the original relative weight is unchanged. -/
theorem unit_product (u t W L base : PTm n) (ht : Γ ⊢[PRAAx] bounded t one one)
    (hu : Γ ⊢[PRAAx] relative u W L base) : Γ ⊢[PRAAx] relative (qmul u t) W L base :=
  GaussianRationalRelativeNormAlgebra.relative_congr (.eqRefl _) (one_mul W) (one_mul L) (.eqRefl _)
    (GaussianRationalRelativeNormAlgebra.relative_trans _ _ _ _ _ _ _
      (GaussianRationalRelativeNormAlgebra.product_relative u t one one (le_refl one) ht) hu)
theorem unit_product_left (t u W L base : PTm n) (ht : Γ ⊢[PRAAx] bounded t one one)
    (hu : Γ ⊢[PRAAx] relative u W L base) : Γ ⊢[PRAAx] relative (qmul t u) W L base :=
  GaussianRationalRelativeNormAlgebra.relative_congr (GaussianRationalPowerAlgebra.qmul_commutative u t)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (unit_product u t W L base ht hu)

theorem actual_two_term_relative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (relative (var 0) (var 2) (var 4) (var 5) ⟶ relative (var 1) (var 3) (var 4) (var 5) ⟶
      relative (qadd (var 0) (var 1)) (var 2+var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (relative_add _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_two_term_subtraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (relative (var 0) (var 2) (var 4) (var 5) ⟶ relative (var 1) (var 3) (var 4) (var 5) ⟶
      relative (qsub (var 0) (var 1)) (var 2+var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (relative_sub _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_norm_order_relative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (RationalArgmin.rationalLE (qnormSq (var 0)) (qnormSq (var 1))) (relative (var 0) one one (var 1))) :=
  closeUniv 2 (.andI (.impI (norm_order_relative _ _ Prf.hyp0)) (.impI (relative_norm_order _ _ Prf.hyp0)))
theorem actual_unit_disk_relative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (bounded (var 1) one one ⟶ relative (var 0) (var 2) (var 3) (var 4) ⟶
      relative (qmul (var 1) (var 0)) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (unit_product_left _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_norm_negation_recode_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((qnormSq (qnegative (var 0)) ≐ qnormSq (var 0)) ⋏ (qnormSq (qadd qzero (var 0)) ≐ qnormSq (var 0))) :=
  closeUniv 1 (.andI (norm_negative _) (norm_recode _))

end LeanProofs.IPRA.Analysis.GaussianRationalRelativeTwoTerm
