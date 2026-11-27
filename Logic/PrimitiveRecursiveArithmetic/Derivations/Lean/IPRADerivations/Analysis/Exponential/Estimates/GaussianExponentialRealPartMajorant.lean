import IPRADerivations.Analysis.Exponential.PositiveAxis.FiniteEstimates.GaussianSignedRealExponentialOrder
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant

/-!
# An original squared-exponential bound from its signed real coordinate

The actual conjugate-product observations of the original exponential
are original squared norms. Their majorant depends only on an upper
bound for the signed real coordinate. All actual constant, addition,
exponential and product clocks are retained. One finite scalar gap
removes auxiliary observations. This is a squared-modulus majorant;
the sharper Euler time powers remain separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialRealPartMajorant

open_ipra
open GaussianExponentialRealPart (projection squareF squareData squarePrecision doubleRealF doubleRealData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianRationalHorner (qadd qmul canonical_unique represents_congr)
open GaussianRationalNaturalScale (natScale naturalPoint)
open RationalGaussianEmbedding (embed native)
open GaussianRationalSyntheticBounds (natCode)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def doubleScalar (q : PTm n) : PTm n := RationalArithmetic.add (fstT q) (fstT q)
def expF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def expData (q : PTm n) : PTm n := exponentialInputData constantF q
def modulusF : PR 2 := squareF expF
def modulusData (q : PTm n) : PTm n := squareData expF (expData q)
def majorant (M : PTm n) : PTm n := pw (num 3) (two*M)

ipra_subst doubleScalar
ipra_subst expData [exponentialInputData]
ipra_subst modulusData
ipra_subst majorant

theorem conjugate_sum_real (q : PTm n) : Γ ⊢[PRAAx]
    qadd q (GaussianRationalConjugation.point q) ≐ embed (doubleScalar q) := by
  let r := projection q
  have unit := GaussianRationalNaturalScale.natScale_one_canonical (Γ := Γ) r (RationalGaussianEmbedding.embed_canonical _)
  have twice := (GaussianRationalNaturalScale.natScale_congr (Γ := Γ)
    (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one) (.eqRefl r)).eqTrans
      ((GaussianRationalNaturalScale.natScale_add one one r).eqTrans (GaussianRationalSyntheticDivision.qadd_congr unit unit))
  exact (GaussianExponentialRealPart.conjugate_sum q).eqTrans
    (twice.eqTrans (RationalGaussianEmbedding.embed_add _ _).eqSymm)

theorem double_constant_cross (q : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (doubleRealF constantF) constantF (doubleRealData q) (embed (doubleScalar q)) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianExponentialRealPart.double_real_regular _ _ (constant_regular _)) (constant_regular _)
  refine .allI ?_
  let k := GaussianFastValueCut.exponent two (var 0 : PTm (n+1))
  have second := (GaussianNameConjugation.sample_at (Γ := Γ.map Fm.shift) constantF k (Syn.shift q)).eqTrans
    (GaussianRationalConjugation.point_congr (constant_at k (Syn.shift q)))
  have e := (GaussianExponentialReference.add_sample constantF (GaussianNameConjugation.nameF constantF)
    (Syn.shift q) (Syn.shift q) (var 0)).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (constant_at k (Syn.shift q)) second).eqTrans (conjugate_sum_real (Syn.shift q)))
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,doubleRealF,doubleRealData,GaussianExponentialRealPart.subst_doubleRealData,
    GaussianNameArithmetic.subst_addData,RationalGaussianEmbedding.subst_embed,subst_doubleScalar] using
    e.eqTrans (constant_at (var 0) (embed (doubleScalar (Syn.shift q)))).eqSymm

theorem squared_exponential_real (q : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent modulusF expF (modulusData q)
      (GaussianRealExponentialPositiveRepresentative.originalData (doubleScalar q)) := by
  let R := GaussianNameBounds.U constantF q
  let S := GaussianNameBounds.U constantF (embed (doubleScalar q))
  have hq := exponential_input (Γ := Γ) constantF q (constant_regular _)
  have hs := exponential_input (Γ := Γ) constantF (embed (doubleScalar q)) (constant_regular _)
  have square := GaussianExponentialRealPart.exponential_norm_square constantF R q hq
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper (doubleRealF constantF) constantF
    (R+R) S (doubleRealData q) (embed (doubleScalar q)) (GaussianExponentialRealPart.double_real_input constantF R q hq) hs
    (double_constant_cross q)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ square proper

theorem embed_natural (R : PTm n) : Γ ⊢[PRAAx] embed (natCode R) ≐ naturalPoint R := by
  have rep := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (natCode R) (ZT.ofNat R) one
    (GaussianRationalSyntheticBounds.natCode_represents R)
  have eq : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (ZT.ofNat R))
      (ComplexLogarithmRemainder.scale R ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
    all_goals try ipra_simps
    all_goals ring
  exact canonical_unique _ _ _ one (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
    (represents_congr (.eqRefl _) eq (.eqRefl _) rep) (GaussianRationalNaturalScale.natural_point_represents R)

theorem natural_exponential_upper (R p : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 expF p (GaussianRealExponentialPositiveRepresentative.originalData (natCode R))))
      (natCode (pw (num 3) R)) := by
  have e := (GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF
    (GaussianNameBounds.U constantF (embed (natCode R))) p (embed (natCode R))).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      ((constant_at _ _).eqTrans (embed_natural R)))
  exact RationalArgmin.rationalLE_congr (congrFst e).eqSymm (.eqRefl _) (GaussianPositiveExponentialMajorant.positive_real_majorant _ _)

theorem double_real_upper (q M : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT q) (natCode M)) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (doubleScalar q) (natCode (two*M)) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) ((GaussianRationalSyntheticBounds.natCode_add M M).eqTrans
    (GaussianPositiveExponentialMajorant.natCode_congr (by ipra_ring)))
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ h h)

theorem majorant_budget (q M p t : PTm n) (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT q) (natCode M)) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack (fstT (ap2 modulusF p (modulusData q))) (natCode (majorant M)) one (unit p) (num 3) t := by
  have cross := GaussianNameEquivalence.cross_at _ _ _ _ p t (squared_exponential_real (Γ := Γ) q)
  have first := RationalValueBounds.upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t)) cross)
  have middle := real_order_at _ _ _ _ t t
    (GaussianSignedRealExponentialOrder.original_signed_exponential_order _ _ (double_real_upper q M h))
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ first middle
  have upper := RationalValueBounds.upper_order_right _ _ _ _ _ joined (natural_exponential_upper (two*M) t)
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive t))
      (GaussianRationalHorner.positive_product _ _ (unit_positive t) (unit_positive t))) upper
  exact le_of_eq_add (d := zero) (by ipra_ring)

/-- The actual square-name sample is bounded by 3^(2M)+2^-p. Its
input point may have an arbitrary signed imaginary coordinate. -/
theorem original_squared_modulus_upper (q M p : PTm n)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT q) (natCode M)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 modulusF p (modulusData q))) (natCode (majorant M)) one (unit p) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (num 3)
    (majorant_budget q M p
      (GaussianNamedRealOrderTransport.precision (fstT (ap2 modulusF p (modulusData q))) (natCode (majorant M)) (unit p) (num 3)) h)

theorem actual_squared_norm_sample (q p : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 modulusF p (modulusData q)) ≐
      GaussianRationalMetric.qnormSq (ap2 expF (squarePrecision expF p (expData q)) (expData q)) := by
  let a := GaussianRationalMetric.qnormSq (ap2 expF (squarePrecision expF p (expData q)) (expData q))
  have fixed : Γ ⊢[PRAAx] RationalArithmetic.recode a ≐ a :=
    RationalNormalForm.normalize_fixed_point _ (GaussianRationalMetric.qnormSq_canonical _)
  exact (congrFst (GaussianExponentialRealPart.square_sample expF p (expData q))).eqTrans
    ((fst_pair _ _).eqTrans fixed)

theorem original_actual_squared_norm_upper (q M p : PTm n)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT q) (natCode M)) : Γ ⊢[PRAAx]
    RationalValueBounds.upper
      (GaussianRationalMetric.qnormSq (ap2 expF (squarePrecision expF p (expData q)) (expData q)))
      (natCode (majorant M)) one (unit p) :=
  RationalValueBounds.upper_congr (actual_squared_norm_sample q p) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (original_squared_modulus_upper q M p h)

theorem original_complex_exponential_squared_real_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent modulusF expF (modulusData (var 0))
      (GaussianRealExponentialPositiveRepresentative.originalData (doubleScalar (var 0)))) :=
  closeUniv 1 (squared_exponential_real _)

theorem original_signed_real_part_squared_exponential_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArgmin.rationalLE (fstT (var 0)) (natCode (var 1)) ⟶
      RationalValueBounds.upper (fstT (ap2 modulusF (var 2) (modulusData (var 0)))) (natCode (majorant (var 1))) one (unit (var 2))) :=
  closeUniv 3 (.impI (original_squared_modulus_upper _ _ _ Prf.hyp0))

theorem original_actual_squared_exponential_norm_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalArgmin.rationalLE (fstT (var 0)) (natCode (var 1)) ⟶
      RationalValueBounds.upper
        (GaussianRationalMetric.qnormSq (ap2 expF (squarePrecision expF (var 2) (expData (var 0))) (expData (var 0))))
        (natCode (majorant (var 1))) one (unit (var 2))) :=
  closeUniv 3 (.impI (original_actual_squared_norm_upper _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianExponentialRealPartMajorant
