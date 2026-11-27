import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialRealPart

/-!
# An actual nonnegative representative of the signed real exponential

For every original raw signed rational c, take the original exponential
at c/2 and its actual conjugate product. The real-part square identity
identifies this nonnegative-sample name with the unchanged original
exponential at embed(c), preserving both computed radius and query clocks.
No sign assertion about the original negative Taylor observations, or
order law for the exponential, is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRealExponentialPositiveRepresentative

open_ipra
open RationalGaussianEmbedding (embed native)
open RationalSupMetric (numeratorOf denominatorOf)
open GaussianRationalHorner (ofGaussian represents canonical_unique represents_congr positive_product qadd)
open GaussianRationalConjugation (point)
open GaussianExponentialRealPart (squareF squareData doubleRealF doubleRealData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def halfPoint (c : PTm n) : PTm n := ofGaussian (native (numeratorOf c)) (two*denominatorOf c)
def halfRadius (c : PTm n) : PTm n := GaussianNameBounds.U constantF (halfPoint c)
def positiveF : PR 2 := squareF (GaussianRadiusExponentialName.nameF constantF)
def positiveData (c : PTm n) : PTm n := squareData (GaussianRadiusExponentialName.nameF constantF)
  (exponentialInputData constantF (halfPoint c))
def originalData (c : PTm n) : PTm n := exponentialInputData constantF (embed c)

ipra_subst halfPoint
ipra_subst halfRadius
ipra_subst positiveData [exponentialInputData]
ipra_subst originalData [exponentialInputData]

theorem half_denominator_positive (c : PTm n) : Γ ⊢[PRAAx] le one (two*denominatorOf c) :=
  positive_product _ _ (le_succ_self one) (RationalArgmin.denominator_positive c)

theorem half_conjugate (c : PTm n) : Γ ⊢[PRAAx] point (halfPoint c) ≐ halfPoint c := by
  let a := native (numeratorOf c)
  let E := two*denominatorOf c
  have e := half_denominator_positive (Γ := Γ) c
  have rep := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) a E e
  exact canonical_unique _ _ a E (GaussianRationalConjugation.point_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ e) e
    (represents_congr (.eqRefl _) (GaussianRationalConjugation.native_real _) (.eqRefl _)
      (GaussianRationalConjugation.point_represents _ a E e rep)) rep

theorem half_sum (c : PTm n) : Γ ⊢[PRAAx] qadd (halfPoint c) (point (halfPoint c)) ≐ embed c := by
  let a := native (numeratorOf c)
  let D := denominatorOf c
  let E := two*D
  have e := half_denominator_positive (Γ := Γ) c
  have half := GaussianRationalHorner.ofGaussian_represents (Γ := Γ) a E e
  have left := GaussianRationalHorner.qadd_represents _ _ a a E e half
    (represents_congr (half_conjugate c).eqSymm (GaussianRootAlgebra.equal_refl _) (.eqRefl _) half)
  have right := GaussianRationalHorner.represents_rescale (Γ := Γ) (embed c) a D two (RationalGaussianEmbedding.embed_represents c)
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (ComplexLogarithmRemainder.add a a) (ComplexLogarithmRemainder.scale two a) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ E (GaussianRationalHorner.qadd_canonical _ _) (RationalGaussianEmbedding.embed_canonical c) e
    (represents_congr (.eqRefl _) native (.eqRefl _) left)
    (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_comm D two) right)

theorem double_half_sample (c p : PTm n) : Γ ⊢[PRAAx]
    ap2 (doubleRealF constantF) p (doubleRealData (halfPoint c)) ≐ embed c := by
  let k := GaussianFastValueCut.exponent two p
  have second := (GaussianNameConjugation.sample_at (Γ := Γ) constantF k (halfPoint c)).eqTrans
    (GaussianRationalConjugation.point_congr (constant_at k (halfPoint c)))
  exact (GaussianExponentialReference.add_sample constantF (GaussianNameConjugation.nameF constantF)
    (halfPoint c) (halfPoint c) p).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr (constant_at k (halfPoint c)) second).eqTrans (half_sum c))

theorem double_half_cross (c : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (doubleRealF constantF) constantF (doubleRealData (halfPoint c)) (embed c) := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianExponentialRealPart.double_real_regular constantF _ (constant_regular _)) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,GaussianExponentialRealPart.subst_doubleRealData,subst_halfPoint,
    RationalGaussianEmbedding.subst_embed] using
    (double_half_sample (Γ := Γ.map Fm.shift) (Syn.shift c) (var 0)).eqTrans (constant_at _ _).eqSymm

theorem positive_regular (c : PTm n) : Γ ⊢[PRAAx] pointCN positiveF (positiveData c) :=
  GaussianExponentialRealPart.square_regular _ _ (GaussianRadiusExponentialName.name_regular constantF _ _
    (exponential_input constantF (halfPoint c) (constant_regular _)))

theorem sample_nonnegative (c p : PTm n) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (ap2 positiveF p (positiveData c)) :=
  GaussianExponentialRealPart.square_sample_positive _ _ _

theorem sample_canonical (c p : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 positiveF p (positiveData c)) :=
  GaussianNameArithmetic.multiply_canonical _ _ _ _ _

/-- Every raw signed rational is supported, including zero and redundant
positive/negative numerator parts. The target remains the original exp. -/
theorem original_signed_real_exponential (c : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent positiveF (GaussianRadiusExponentialName.nameF constantF) (positiveData c) (originalData c) := by
  let H := halfPoint c
  let R := halfRadius c
  let S := GaussianNameBounds.U constantF (embed c)
  have hH := exponential_input (Γ := Γ) constantF H (constant_regular H)
  have hD := GaussianExponentialRealPart.double_real_input constantF R H hH
  have hC := exponential_input (Γ := Γ) constantF (embed c) (constant_regular _)
  have square := GaussianExponentialRealPart.exponential_norm_square constantF R H hH
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper (doubleRealF constantF) constantF
    (R+R) S (doubleRealData H) (embed c) hD hC (double_half_cross c)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ square proper

theorem original_half_real_argument_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (qadd (halfPoint (var 0)) (point (halfPoint (var 0))) ≐ embed (var 0)) := closeUniv 1 (half_sum _)

theorem actual_signed_exponential_positive_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianPositiveRealArithmetic.positive (ap2 positiveF (var 1) (positiveData (var 0)))) :=
  closeUniv 2 (sample_nonnegative _ _)

theorem actual_signed_exponential_positive_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN positiveF (positiveData (var 0))) := closeUniv 1 (positive_regular _)

theorem original_signed_real_exponential_positive_representative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent positiveF (GaussianRadiusExponentialName.nameF constantF) (positiveData (var 0)) (originalData (var 0))) :=
  closeUniv 1 (original_signed_real_exponential _)

end LeanProofs.IPRA.Analysis.GaussianRealExponentialPositiveRepresentative
