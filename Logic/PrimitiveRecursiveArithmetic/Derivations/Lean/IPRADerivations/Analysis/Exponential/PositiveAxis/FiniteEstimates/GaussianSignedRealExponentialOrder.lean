import IPRADerivations.Analysis.Exponential.PositiveAxis.NamedValues.GaussianRealExponentialPositiveRepresentative
import IPRADerivations.Analysis.Names.Rates.Order.GaussianNamedRealOrderTransport

/-!
# Order of the unchanged original exponential at signed real rationals

The original scalar order gives an actual nonnegative cross-gap fraction
delta with c+delta=d. The nonnegative representative of exp(c) is
dominated by its actual product with exp(delta), whose original Taylor
observations include the constant term one. Original named addition and
finite real-order transport yield the exact independent comparison of
the unchanged exponential names at arbitrary raw signed rational inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSignedRealExponentialOrder

open_ipra
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData originalData positive_regular sample_nonnegative sample_canonical)
open GaussianNamedPositiveExponentialOrder (realOrder scalar_coordinate_distance)
open GaussianRationalHorner (qadd qmul represents represents_congr canonical_unique positive_product)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents)
open RationalGaussianEmbedding (embed native)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianRationalPolynomialExponential (scalarSum scalarBody)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def gap (c d : PTm n) : PTm n := monus (RationalArgmin.left d c) (RationalArgmin.left c d)
def delta (c d : PTm n) : PTm n := radiusPoint (gap c d) (denominatorOf c*denominatorOf d)
def expF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def deltaData (c d : PTm n) : PTm n := exponentialInputData constantF (delta c d)
def productF : PR 2 := multiplyF positiveF expF
def productData (c d : PTm n) : PTm n := multiplyData positiveF expF (positiveData c) (deltaData c d)

ipra_subst gap
ipra_subst delta
ipra_subst deltaData [exponentialInputData]
ipra_subst productData

theorem delta_denominator_positive (c d : PTm n) : Γ ⊢[PRAAx] le one (denominatorOf c*denominatorOf d) :=
  positive_product _ _ (RationalArgmin.denominator_positive c) (RationalArgmin.denominator_positive d)

theorem delta_nonnegative (c d : PTm n) : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive (delta c d) :=
  GaussianPositiveExponentialTermBound.actual_positive_fraction _ _ (delta_denominator_positive c d)

theorem add_delta (c d : PTm n) (h : Γ ⊢[PRAAx] rationalLE c d) : Γ ⊢[PRAAx]
    qadd (embed c) (delta c d) ≐ embed d := by
  let C := denominatorOf c
  let D := denominatorOf d
  let E := C*D
  let a := native (numeratorOf c)
  let b := native (numeratorOf d)
  have e := delta_denominator_positive (Γ := Γ) c d
  have left := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) (embed c) a C D E
    (RationalGaussianEmbedding.embed_represents c) (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to (Γ := Γ) (embed d) b D C E
    (RationalGaussianEmbedding.embed_represents d) (mul_comm _ _)
  have sum := GaussianRationalHorner.qadd_represents (embed c) (delta c d)
    (ComplexLogarithmRemainder.scale D a) (radiusNumerator (gap c d)) E e left (radius_represents (gap c d) E e)
  have H := natEq (eq_add_of_le h)
  have value : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.add (ComplexLogarithmRemainder.scale D a) (radiusNumerator (gap c d)))
      (ComplexLogarithmRemainder.scale C b) := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale]
      simp only [a,b,native,radiusNumerator,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]
      simp only [C,D,gap,RationalArgmin.left,ZT.toZ] at H ⊢
      ipra_simps
      linear_combination -H
    · simp only [GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale]
      simp only [a,b,native,radiusNumerator,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  exact canonical_unique _ _ _ E (GaussianRationalHorner.qadd_canonical _ _) (RationalGaussianEmbedding.embed_canonical d) e
    (represents_congr (.eqRefl _) value (.eqRefl _) sum) right

theorem delta_sample (c d p : PTm n) : Γ ⊢[PRAAx] ap2 expF p (deltaData c d) ≐
    scalarSum (delta c d) (GaussianRadiusExponentialName.index (GaussianNameBounds.U constantF (delta c d)) p) :=
  (GaussianRadiusExponentialName.sample_at constantF _ p (delta c d)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr scalarBody (.eqRefl _) (constant_at _ (delta c d)))

theorem delta_sample_positive (c d p : PTm n) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (ap2 expF p (deltaData c d)) :=
  GaussianPositiveRealArithmetic.positive_congr (delta_sample c d p).eqSymm
    (GaussianPositiveExponentialProduct.positive_scalar_sum _ _ (delta_nonnegative c d))

theorem delta_sample_unit_lower (c d p : PTm n) : Γ ⊢[PRAAx]
    rationalLE (fstT GaussianRationalSyntheticDivision.qone) (fstT (ap2 expF p (deltaData c d))) :=
  RationalArgmin.rationalLE_congr (congrFst (GaussianScalarExponentialDiagonal.coefficient_zero _))
    (congrFst (delta_sample c d p)).eqSymm
    (GaussianPositiveExponentialTermBound.original_term_le _ zero _ (delta_nonnegative c d) (zero_le _))

theorem positive_product_observations (c d p q : PTm n) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 positiveF p (positiveData c)))
      (fstT (ap2 productF q (productData c d))) (unit p+unit q) (unit p*unit q) := by
  let X := positiveData c
  let Y := deltaData c d
  let s := GaussianFastValueCut.exponent (multiplyModulus positiveF expF X Y) q
  let a := ap2 positiveF s X
  let b := ap2 expF s Y
  have read : Γ ⊢[PRAAx] ap2 productF q (productData c d) ≐ qmul a b :=
    (GaussianNameArithmetic.multiply_at positiveF expF X Y q).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))
  have mono := RationalArithmetic.multiply_monotone (Γ := Γ) (fstT a) _ _ (sample_nonnegative c s).andE₂ (delta_sample_unit_lower c d s)
  have lhs := (GaussianPositiveExponentialProduct.real_product (Γ := Γ) a GaussianRationalSyntheticDivision.qone
    RationalGaussianEmbedding.axis_one).eqSymm.eqTrans (congrFst (GaussianReciprocalHorner.qmul_one_right a (sample_canonical c s)))
  have rhs := (GaussianPositiveExponentialProduct.real_product (Γ := Γ) a b (delta_sample_positive c d s).andE₁).eqSymm
  have middle : Γ ⊢[PRAAx] rationalLE (fstT a) (fstT (qmul a b)) := RationalArgmin.rationalLE_congr lhs rhs mono
  have near := GaussianNameEquivalence.point_at (Γ := Γ) positiveF X p s (positive_regular c)
  have grow : Γ ⊢[PRAAx] le (unit q) (unit s) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have small := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive p) (unit_positive s))
    (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le (𝔞(unit p)*𝔞(unit p))*sl grow) near
  have upper := RationalValueBounds.upper_order_right _ _ _ _ _
    (RationalValueBounds.upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
      (positive_product _ _ (unit_positive p) (unit_positive q)) small)) middle
  exact RationalValueBounds.upper_congr (.eqRefl _) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) upper

theorem positive_product_order (c d : PTm n) : Γ ⊢[PRAAx]
    realOrder positiveF productF (positiveData c) (productData c d) := by
  refine .allI (.allI ?_)
  simpa only [realOrder,Syn.shift,GaussianRealExponentialPositiveRepresentative.subst_positiveData,subst_productData] using
    positive_product_observations (Γ := (Γ.map Fm.shift).map Fm.shift) (Syn.shift (Syn.shift c)) (Syn.shift (Syn.shift d)) (var 1) (var 0)

theorem add_delta_names (c d : PTm n) (h : Γ ⊢[PRAAx] rationalLE c d) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameArithmetic.addF constantF constantF) constantF
      (GaussianNameArithmetic.addData (embed c) (delta c d)) (embed d) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameArithmetic.add_fast _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (Syn.shift c) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using h.shift
  let k := GaussianFastValueCut.exponent two (var 0 : PTm (n+1))
  have e := (GaussianExponentialReference.add_sample constantF constantF (embed (Syn.shift c)) (delta (Syn.shift c) (Syn.shift d)) (var 0)).eqTrans
    ((GaussianRationalSyntheticDivision.qadd_congr (constant_at k _) (constant_at k _)).eqTrans (add_delta _ _ hs))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianNameArithmetic.subst_addData,RationalGaussianEmbedding.subst_embed,subst_delta] using
    e.eqTrans (constant_at _ _).eqSymm

theorem product_matches_original (c d : PTm n) (h : Γ ⊢[PRAAx] rationalLE c d) : Γ ⊢[PRAAx]
    crossEquivalent productF expF (productData c d) (originalData d) := by
  let X := originalData c
  let Y := deltaData c d
  have hx := exponential_input (Γ := Γ) constantF (embed c) (constant_regular _)
  have hy := exponential_input (Γ := Γ) constantF (delta c d) (constant_regular _)
  have hz := exponential_input (Γ := Γ) constantF (embed d) (constant_regular _)
  have ex := GaussianRadiusExponentialName.name_regular constantF _ _ hx
  have ey := GaussianRadiusExponentialName.name_regular constantF _ _ hy
  have replacement := GaussianNameArithmetic.multiply_equivalent positiveF expF expF expF (positiveData c) X Y Y
    (positive_regular c) ex ey ey
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (GaussianRealExponentialPositiveRepresentative.original_signed_real_exponential c))
    (GaussianNameEquivalence.diagonal_refl expF Y)
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent constantF constantF constantF
    _ _ _ (embed c) (delta c d) (embed d) hx hy hz (add_delta_names c d h)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ replacement addition

/-- The only input is the original signed scalar comparison. Both
exponentials retain their original independently computed sample data. -/
theorem original_signed_exponential_order (c d : PTm n) (h : Γ ⊢[PRAAx] rationalLE c d) : Γ ⊢[PRAAx]
    realOrder expF expF (originalData c) (originalData d) :=
  GaussianNamedRealOrderTransport.transport expF positiveF productF expF (originalData c) (positiveData c)
    (productData c d) (originalData d)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianRealExponentialPositiveRepresentative.original_signed_real_exponential c))
    (product_matches_original c d h) (positive_product_order c d)

theorem actual_positive_cross_gap_addition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (var 0) (var 1) ⟶ qadd (embed (var 0)) (delta (var 0) (var 1)) ≐ embed (var 1)) :=
  closeUniv 2 (.impI (add_delta _ _ Prf.hyp0))

theorem actual_positive_cross_gap_exponential_unit_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (rationalLE (fstT GaussianRationalSyntheticDivision.qone) (fstT (ap2 expF (var 2) (deltaData (var 0) (var 1))))) :=
  closeUniv 3 (delta_sample_unit_lower _ _ _)

theorem original_signed_rational_exponential_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (var 0) (var 1) ⟶ realOrder expF expF (originalData (var 0)) (originalData (var 1))) :=
  closeUniv 2 (.impI (original_signed_exponential_order _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSignedRealExponentialOrder
