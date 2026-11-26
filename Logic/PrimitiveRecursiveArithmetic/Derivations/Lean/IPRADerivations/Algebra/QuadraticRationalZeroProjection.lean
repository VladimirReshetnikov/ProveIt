import IPRADerivations.Algebra.QuadraticRationalEmbedding
import IPRADerivations.Algebra.QuadraticZeroProjection

/-!
# Actual rational zero-radicand projection

The source d=0 sign is the original signed numerator sign of the first
rational coefficient. Denominators are actual decoded positive data.
Actual normalized pair add/negative/multiply at numerical zero are
interpreted by the proved integer zero-projection branch, without a
positive-cone law at zero or an input projection/output law.
-/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalZeroProjection

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalEq left)
open QuadraticSignCertificates (first second equal negative_first negative_second)
open QuadraticConeOrder (equal_of_values equal_first equal_symm add_first add_second)
open QuadraticRationalClearing (clear denominator represents clear_represents denominator_positive)
open QuadraticPositiveScaling (scale scale_first scale_second)
open QuadraticRationalPairArithmetic (add negative multiply)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def project (x : PTm n) : PTm n := QuadraticRationalEmbedding.embed (fstT x)
def sign (x : PTm n) : PTm n := QuadraticSignCertificates.tag (numeratorOf (fstT x))
def positive (x : PTm n) : Fm PTm n := sign x ≐ one
def isZero (x : PTm n) : Fm PTm n := sign x ≐ zero
def difference (x y : PTm n) : PTm n := QuadraticRationalEqualityOrder.difference x y
def equivalent (x y : PTm n) : Fm PTm n := isZero (difference x y)
def less (x y : PTm n) : Fm PTm n := positive (difference y x)
ipra_subst project
ipra_subst sign
ipra_subst positive
ipra_subst isZero
ipra_subst difference
ipra_subst equivalent
ipra_subst less

theorem sign_project (x : PTm n) : Γ ⊢[PRAAx]
    sign x ≐ QuadraticRationalClearing.sign one (project x) :=
  (QuadraticRationalEmbedding.embedding_sign one (fstT x) (le_refl one)).eqSymm
theorem representation_sign (x A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] represents x A D) : Γ ⊢[PRAAx] sign x ≐ QuadraticZeroProjection.sign A :=
  (sign_project x).eqTrans ((QuadraticRationalClearing.representation_sign _ _ _ _ (le_refl one) hD
    (QuadraticRationalEmbedding.embedding_represents _ _ _ (.andE₁ h))).eqTrans
      (QuadraticIntegerEmbedding.integer_sign one (first A) (le_refl one)))
theorem native_sign_congr (A B : PTm n) (h : Γ ⊢[PRAAx] equal A B) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.sign A ≐ QuadraticZeroProjection.sign B :=
  QuadraticZeroProjection.sign_congr _ _ (QuadraticZeroProjection.equivalent_of_projection _ _ (ZT.derive (equal_first h)))
theorem native_scale (k A : PTm n) : Γ ⊢[PRAAx]
    equal (QuadraticZeroProjection.project (scale k A)) (scale k (QuadraticZeroProjection.project A)) := by
  apply equal_of_values <;> simp only [QuadraticZeroProjection.project,QuadraticIntegerEmbedding.integer_first,
    QuadraticIntegerEmbedding.integer_second,scale_first,scale_second] <;> ring
theorem native_scale_sign (k A : PTm n) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.sign (scale k A) ≐ QuadraticZeroProjection.sign A :=
  (QuadraticZeroProjection.sign_project _).eqTrans
    ((QuadraticConeOrder.sign_congr _ _ _ (le_refl one) (native_scale k A)).eqTrans
      ((QuadraticPositiveScaling.sign_scale one k _ (le_refl one) hk).eqTrans (QuadraticZeroProjection.sign_project _).eqSymm))
theorem native_integer_sign (a : ZT n) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.sign (QuadraticIntegerEmbedding.integer a) ≐ QuadraticSignCertificates.tag a := by
  have h : Γ ⊢[PRAAx] equal (QuadraticZeroProjection.project (QuadraticIntegerEmbedding.integer a)) (QuadraticIntegerEmbedding.integer a) := by
    apply equal_of_values <;> simp only [QuadraticZeroProjection.project,QuadraticIntegerEmbedding.integer_first,QuadraticIntegerEmbedding.integer_second]
  exact (QuadraticZeroProjection.sign_project _).eqTrans
    ((QuadraticConeOrder.sign_congr _ _ _ (le_refl one) h).eqTrans (QuadraticIntegerEmbedding.integer_sign one a (le_refl one)))

theorem add_sign (x y : PTm n) : Γ ⊢[PRAAx] sign (add x y) ≐ QuadraticZeroProjection.sign
    (QuadraticSignCertificates.add (scale (denominator y) (clear x)) (scale (denominator x) (clear y))) :=
  representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
theorem negative_sign (x : PTm n) : Γ ⊢[PRAAx] sign (negative x) ≐ QuadraticZeroProjection.sign (QuadraticSignCertificates.negative (clear x)) :=
  representation_sign _ _ _ (denominator_positive x) (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))
theorem multiply_sign (x y : PTm n) : Γ ⊢[PRAAx] sign (multiply zero x y) ≐ QuadraticZeroProjection.sign (QuadraticSignCertificates.multiply zero (clear x) (clear y)) :=
  representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y))
theorem clear_sign (x : PTm n) : Γ ⊢[PRAAx] sign x ≐ QuadraticZeroProjection.sign (clear x) :=
  representation_sign _ _ _ (denominator_positive x) (clear_represents x)
theorem positive_add (x y : PTm n) (hx : Γ ⊢[PRAAx] positive x) (hy : Γ ⊢[PRAAx] positive y) : Γ ⊢[PRAAx] positive (add x y) :=
  (add_sign _ _).eqTrans (QuadraticZeroProjection.positive_add _ _
    ((native_scale_sign _ _ (denominator_positive y)).eqTrans ((clear_sign x).eqSymm.eqTrans hx))
    ((native_scale_sign _ _ (denominator_positive x)).eqTrans ((clear_sign y).eqSymm.eqTrans hy)))
theorem positive_multiply (x y : PTm n) (hx : Γ ⊢[PRAAx] positive x) (hy : Γ ⊢[PRAAx] positive y) : Γ ⊢[PRAAx] positive (multiply zero x y) :=
  (multiply_sign _ _).eqTrans (QuadraticZeroProjection.positive_multiply _ _
    ((clear_sign x).eqSymm.eqTrans hx) ((clear_sign y).eqSymm.eqTrans hy))
theorem zero_negative (x : PTm n) (h : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] isZero (negative x) :=
  (negative_sign _).eqTrans (QuadraticZeroProjection.zero_negative _ ((clear_sign x).eqSymm.eqTrans h))
theorem zero_multiply (x y : PTm n) (h : Γ ⊢[PRAAx] isZero x) : Γ ⊢[PRAAx] isZero (multiply zero x y) :=
  (multiply_sign _ _).eqTrans (QuadraticZeroProjection.zero_multiply _ _ ((clear_sign x).eqSymm.eqTrans h))
theorem zero_add (x y : PTm n) (hx : Γ ⊢[PRAAx] isZero x) (hy : Γ ⊢[PRAAx] isZero y) : Γ ⊢[PRAAx] isZero (add x y) :=
  (add_sign _ _).eqTrans (QuadraticZeroProjection.zero_add _ _
    ((native_scale_sign _ _ (denominator_positive y)).eqTrans ((clear_sign x).eqSymm.eqTrans hx))
    ((native_scale_sign _ _ (denominator_positive x)).eqTrans ((clear_sign y).eqSymm.eqTrans hy)))
theorem zero_product_reflect (x y : PTm n) (h : Γ ⊢[PRAAx] isZero (multiply zero x y)) : Γ ⊢[PRAAx] isZero x ⋎ isZero y := by
  refine .orE (QuadraticZeroProjection.zero_product_reflect _ _ ((multiply_sign _ _).eqSymm.eqTrans h)) ?_ ?_
  · exact .orI₁ ((clear_sign x).wk.eqTrans Prf.hyp0)
  · exact .orI₂ ((clear_sign y).wk.eqTrans Prf.hyp0)

theorem cross_projection (x y : PTm n) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.equivalent (QuadraticRationalEqualityOrder.crossOf x y)
      (scale (denominatorOf (sndT x)*denominatorOf (sndT y))
        (QuadraticIntegerEmbedding.integer (QuadraticRationalEmbedding.crossNumerator (fstT x) (fstT y)))) := by
  apply QuadraticZeroProjection.equivalent_of_projection
  ipra_lc [QuadraticRationalEqualityOrder.crossOf, QuadraticRationalEqualityOrder.cross, QuadraticIntegerOrder.difference, add_first, negative_first, scale_first, QuadraticRationalClearing.clear_first, QuadraticIntegerEmbedding.integer_first, QuadraticRationalEmbedding.crossNumerator, denominator]
theorem difference_sign (x y : PTm n) : Γ ⊢[PRAAx] sign (difference x y) ≐
    QuadraticSignCertificates.tag (QuadraticRationalEmbedding.crossNumerator (fstT x) (fstT y)) :=
  (representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))).eqTrans
      ((QuadraticZeroProjection.sign_congr _ _ (cross_projection x y)).eqTrans
        ((native_scale_sign _ _ (LeanProofs.IPRA.Analysis.RationalArithmetic.product_denominator_positive (sndT x) (sndT y))).eqTrans (native_integer_sign _)))
theorem comparison_project (x y : PTm n) : Γ ⊢[PRAAx] sign (difference x y) ≐
    QuadraticRationalClearing.sign one (QuadraticRationalEqualityOrder.difference (project x) (project y)) :=
  (difference_sign _ _).eqTrans
    ((QuadraticRationalEmbedding.embedding_difference_sign one (fstT x) (fstT y) (le_refl one)).eqTrans
      (QuadraticIntegerEmbedding.integer_sign one _ (le_refl one))).eqSymm
theorem equivalent_project (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx]
    QuadraticRationalEqualityOrder.equivalent one (project x) (project y) := (comparison_project _ _).eqSymm.eqTrans h
theorem equivalent_of_project (x y : PTm n) (h : Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.equivalent one (project x) (project y)) : Γ ⊢[PRAAx]
    equivalent x y := (comparison_project _ _).eqTrans h
theorem equivalent_reflect (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] rationalEq (fstT x) (fstT y) :=
  QuadraticRationalEmbedding.embedding_equal_reflect one _ _ (le_refl one) (equivalent_project _ _ h)
theorem equivalent_of_projection (x y : PTm n) (h : Γ ⊢[PRAAx] rationalEq (fstT x) (fstT y)) : Γ ⊢[PRAAx] equivalent x y :=
  equivalent_of_project _ _ (QuadraticRationalEmbedding.embedding_equivalent one _ _ (le_refl one) h)
theorem equivalent_iff (x y : PTm n) : Γ ⊢[PRAAx] Fm.iff (equivalent x y) (rationalEq (fstT x) (fstT y)) :=
  .andI (.impI (equivalent_reflect _ _ Prf.hyp0)) (.impI (equivalent_of_projection _ _ Prf.hyp0))
theorem less_project (x y : PTm n) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx]
    QuadraticRationalEqualityOrder.less one (project x) (project y) := (comparison_project _ _).eqSymm.eqTrans h
theorem less_of_project (x y : PTm n) (h : Γ ⊢[PRAAx] QuadraticRationalEqualityOrder.less one (project x) (project y)) : Γ ⊢[PRAAx]
    less x y := (comparison_project _ _).eqTrans h
theorem equivalent_refl (x : PTm n) : Γ ⊢[PRAAx] equivalent x x :=
  equivalent_of_project _ _ (QuadraticRationalEqualityOrder.equivalent_refl one _ (le_refl one))
theorem equivalent_symm (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] equivalent y x :=
  equivalent_of_project _ _ (QuadraticRationalEqualityOrder.equivalent_symm one _ _ (le_refl one) (equivalent_project _ _ h))
theorem equivalent_trans (x y z : PTm n) (hxy : Γ ⊢[PRAAx] equivalent x y) (hyz : Γ ⊢[PRAAx] equivalent y z) : Γ ⊢[PRAAx] equivalent x z :=
  equivalent_of_project _ _ (QuadraticRationalEqualityOrder.equivalent_trans one _ _ _ (le_refl one) (equivalent_project _ _ hxy) (equivalent_project _ _ hyz))
theorem less_irrefl (x : PTm n) : Γ ⊢[PRAAx] neg (less x x) := by
  refine .impI ?_
  exact .impE (QuadraticRationalEqualityOrder.less_irrefl one _ (le_refl one)) (less_project _ _ Prf.hyp0)
theorem less_trans (x y z : PTm n) (hxy : Γ ⊢[PRAAx] less x y) (hyz : Γ ⊢[PRAAx] less y z) : Γ ⊢[PRAAx] less x z :=
  less_of_project _ _ (QuadraticRationalEqualityOrder.less_trans one _ _ _ (le_refl one) (less_project _ _ hxy) (less_project _ _ hyz))
theorem ordered_trichotomy (x y : PTm n) : Γ ⊢[PRAAx] less x y ⋎ (less y x ⋎ equivalent x y) := by
  refine .orE (QuadraticRationalEqualityOrder.ordered_trichotomy one (project x) (project y) (le_refl one)) ?_ ?_
  · exact .orI₁ (less_of_project _ _ Prf.hyp0)
  · refine .orE Prf.hyp0 ?_ ?_
    · exact .orI₂ (.orI₁ (less_of_project _ _ Prf.hyp0))
    · exact .orI₂ (.orI₂ (equivalent_of_project _ _ Prf.hyp0))

theorem native_zero_congr (A B : PTm n) (he : Γ ⊢[PRAAx] equal A B)
    (h : Γ ⊢[PRAAx] QuadraticZeroProjection.isZero A) : Γ ⊢[PRAAx] QuadraticZeroProjection.isZero B :=
  (native_sign_congr _ _ he).eqSymm.eqTrans h
theorem native_positive_congr (A B : PTm n) (he : Γ ⊢[PRAAx] equal A B)
    (h : Γ ⊢[PRAAx] QuadraticZeroProjection.positive A) : Γ ⊢[PRAAx] QuadraticZeroProjection.positive B :=
  (native_sign_congr _ _ he).eqSymm.eqTrans h
theorem zero_of_representations (x y A D B E : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E)
    (h : Γ ⊢[PRAAx] QuadraticZeroProjection.isZero (QuadraticRationalEqualityOrder.cross A D B E)) : Γ ⊢[PRAAx] equivalent x y :=
  (representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hD hE)
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hx hy)).eqTrans h
theorem less_of_representations (x y A D B E : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le one E)
    (hx : Γ ⊢[PRAAx] represents x A D) (hy : Γ ⊢[PRAAx] represents y B E)
    (h : Γ ⊢[PRAAx] QuadraticZeroProjection.positive (QuadraticRationalEqualityOrder.cross B E A D)) : Γ ⊢[PRAAx] less x y :=
  (representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product hE hD)
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ hy hx)).eqTrans h
theorem zero_cross (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.isZero (QuadraticRationalEqualityOrder.crossOf x y) :=
  (representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))).eqSymm.eqTrans h
theorem positive_cross (x y : PTm n) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx]
    QuadraticZeroProjection.positive (QuadraticRationalEqualityOrder.crossOf y x) :=
  (representation_sign _ _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive y) (denominator_positive x))
    (QuadraticRationalEqualityOrder.cross_represents _ _ _ _ _ _ (clear_represents y) (clear_represents x))).eqSymm.eqTrans h
theorem equivalent_add (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] equivalent x x') (hy : Γ ⊢[PRAAx] equivalent y y') : Γ ⊢[PRAAx]
    equivalent (add x y) (add x' y') := by
  apply zero_of_representations _ _ _ _ _ _
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x') (denominator_positive y'))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents y))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x') (clear_represents y'))
  apply native_zero_congr _ _ (equal_symm (QuadraticRationalCongruence.addition_cross _ _ _ _ _ _ _ _))
  exact QuadraticZeroProjection.zero_add _ _
    ((native_scale_sign _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive y) (denominator_positive y'))).eqTrans (zero_cross _ _ hx))
    ((native_scale_sign _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive x'))).eqTrans (zero_cross _ _ hy))
theorem equivalent_negative (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] equivalent (negative x) (negative y) := by
  apply zero_of_representations _ _ _ _ _ _ (denominator_positive x) (denominator_positive y)
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents x))
    (QuadraticRationalPairArithmetic.negative_represents _ _ _ (clear_represents y))
  exact native_zero_congr _ _ (equal_symm (QuadraticRationalCongruence.negative_cross _ _ _ _))
    (QuadraticZeroProjection.zero_negative _ (zero_cross _ _ h))
theorem equivalent_multiply (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] equivalent x x') (hy : Γ ⊢[PRAAx] equivalent y y') : Γ ⊢[PRAAx]
    equivalent (multiply zero x y) (multiply zero x' y') := by
  apply zero_of_representations _ _ _ _ _ _
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive y))
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x') (denominator_positive y'))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive x) (denominator_positive y) (clear_represents x) (clear_represents y))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive x') (denominator_positive y') (clear_represents x') (clear_represents y'))
  apply native_zero_congr _ _ (equal_symm (QuadraticRationalCongruence.multiplication_cross zero _ _ _ _ _ _ _ _))
  exact QuadraticZeroProjection.zero_add _ _ (QuadraticZeroProjection.zero_multiply _ _ (zero_cross _ _ hx))
    (native_zero_congr _ _ (QuadraticPositiveScaling.product_commute zero _ _) (QuadraticZeroProjection.zero_multiply _ _ (zero_cross _ _ hy)))
theorem less_translate (x y z : PTm n) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx] less (add x z) (add y z) := by
  apply less_of_representations _ _ _ _ _ _
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive x) (denominator_positive z))
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive y) (denominator_positive z))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents x) (clear_represents z))
    (QuadraticRationalPairArithmetic.add_represents _ _ _ _ _ _ (clear_represents y) (clear_represents z))
  apply native_positive_congr _ _ (equal_symm (QuadraticRationalCongruence.translation_cross _ _ _ _ _ _))
  exact (native_scale_sign _ _ (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive z) (denominator_positive z))).eqTrans (positive_cross _ _ h)
theorem less_multiply_positive (x y z : PTm n) (hz : Γ ⊢[PRAAx] positive z) (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx]
    less (multiply zero z x) (multiply zero z y) := by
  apply less_of_representations _ _ _ _ _ _
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive z) (denominator_positive x))
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (denominator_positive z) (denominator_positive y))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive z) (denominator_positive x) (clear_represents z) (clear_represents x))
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (denominator_positive z) (denominator_positive y) (clear_represents z) (clear_represents y))
  apply native_positive_congr _ _ (equal_symm (QuadraticRationalCongruence.positive_factor_cross zero _ _ _ _ _ _))
  exact (native_scale_sign _ _ (denominator_positive z)).eqTrans
    (QuadraticZeroProjection.positive_multiply _ _ ((clear_sign z).eqSymm.eqTrans hz) (positive_cross _ _ h))
theorem root_isZero : Γ ⊢[PRAAx] isZero (QuadraticRationalEmbedding.root : PTm n) :=
  (representation_sign _ _ _ (le_refl one) QuadraticRationalEmbedding.root_represents).eqTrans QuadraticZeroProjection.root_isZero
theorem root_equivalent_zero : Γ ⊢[PRAAx] equivalent (QuadraticRationalEmbedding.root : PTm n)
    (QuadraticRationalEmbedding.embed QuadraticRationalEmbedding.zeroScalar) :=
  equivalent_of_projection _ _ (LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq_congr
    (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (.eqRefl _))
theorem root_square : Γ ⊢[PRAAx] equivalent (multiply zero QuadraticRationalEmbedding.root QuadraticRationalEmbedding.root)
    (QuadraticRationalEmbedding.embed (QuadraticRationalPairArithmetic.scalar (zero : PTm n))) := by
  apply zero_of_representations _ _ _ _ _ _
    (LeanProofs.IPRA.Analysis.RationalAlgebra.positive_product (le_refl one) (le_refl one)) (le_refl one)
    (QuadraticRationalPairArithmetic.multiply_represents _ _ _ _ _ _ _ (le_refl one) (le_refl one)
      QuadraticRationalEmbedding.root_represents QuadraticRationalEmbedding.root_represents)
    (QuadraticRationalEmbedding.embedding_represents _ _ _ (QuadraticRationalPairArithmetic.scalar_represents zero))
  exact native_zero_congr _ _ (equal_symm (QuadraticRationalEmbedding.native_unit_cross _ _)) QuadraticZeroProjection.root_square

theorem less_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] equivalent x x') (hy : Γ ⊢[PRAAx] equivalent y y')
    (h : Γ ⊢[PRAAx] less x y) : Γ ⊢[PRAAx] less x' y' :=
  less_of_project _ _ (QuadraticRationalEqualityOrder.less_congr one _ _ _ _ (le_refl one)
    (equivalent_project _ _ hx) (equivalent_project _ _ hy) (less_project _ _ h))
theorem sign_congr (x y : PTm n) (h : Γ ⊢[PRAAx] equivalent x y) : Γ ⊢[PRAAx] sign x ≐ sign y := by
  have he : Γ ⊢[PRAAx] QuadraticRationalClearing.sameCoefficients (project x) (project y) :=
    .andI (LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (equivalent_reflect _ _ h))
      (LeanProofs.IPRA.Analysis.RationalArgmin.rationalEq_congr (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm (.eqRefl _))
  exact (sign_project x).eqTrans ((QuadraticRationalClearing.sign_congr one _ _ (le_refl one) he).eqTrans (sign_project y).eqSymm)

def output (x : PTm n) : PTm n := pairT (project x) (pairT (sign x) QuadraticRationalEmbedding.root)
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (x : PTm n) : PTm n := ap1 outputF x
ipra_subst output
ipra_subst run
theorem program_at (x : PTm n) : Γ ⊢[PRAAx] run x ≐ output x := by
  simpa [run,outputF,ap1] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![x]
theorem returned_projection (x : PTm n) : Γ ⊢[PRAAx] fstT (run x) ≐ project x :=
  (program_at _).fstE
theorem returned_sign (x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run x)) ≐ sign x :=
  (program_at _).sndE.fstE
theorem returned_root (x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run x)) ≐ QuadraticRationalEmbedding.root :=
  (program_at _).sndE.sndE

theorem zero_rational_representation_sign_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ represents (var 0) (var 1) (var 2) ⟶ sign (var 0) ≐ QuadraticZeroProjection.sign (var 1)) :=
  closeUniv 3 (.impI (.impI (representation_sign _ _ _ Prf.hyp1 Prf.hyp0)))
theorem zero_rational_equality_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (equivalent (var 0) (var 1)) (rationalEq (fstT (var 0)) (fstT (var 1)))) := closeUniv 2 (equivalent_iff _ _)
theorem zero_rational_equality_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (equivalent (var 0) (var 0) ⋏ ((equivalent (var 0) (var 1) ⟶ equivalent (var 1) (var 0)) ⋏
      (equivalent (var 0) (var 1) ⟶ equivalent (var 1) (var 2) ⟶ equivalent (var 0) (var 2)))) :=
  closeUniv 3 (.andI (equivalent_refl _) (.andI (.impI (equivalent_symm _ _ Prf.hyp0)) (.impI (.impI (equivalent_trans _ _ _ Prf.hyp1 Prf.hyp0)))))
theorem zero_rational_equality_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalent (var 0) (var 1) ⟶ equivalent (var 2) (var 3) ⟶
      (equivalent (add (var 0) (var 2)) (add (var 1) (var 3)) ⋏
        (equivalent (negative (var 0)) (negative (var 1)) ⋏
          equivalent (multiply zero (var 0) (var 2)) (multiply zero (var 1) (var 3))))) :=
  closeUniv 4 (.impI (.impI (.andI (equivalent_add _ _ _ _ Prf.hyp1 Prf.hyp0)
    (.andI (equivalent_negative _ _ Prf.hyp1) (equivalent_multiply _ _ _ _ Prf.hyp1 Prf.hyp0)))))
theorem zero_rational_positive_closure_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (positive (var 0) ⟶ positive (var 1) ⟶ (positive (add (var 0) (var 1)) ⋏ positive (multiply zero (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (.andI (positive_add _ _ Prf.hyp1 Prf.hyp0) (positive_multiply _ _ Prf.hyp1 Prf.hyp0))))
theorem zero_rational_zero_ideal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (isZero (var 0) ⟶ (isZero (negative (var 0)) ⋏ (isZero (multiply zero (var 0) (var 1)) ⋏
      (isZero (var 1) ⟶ isZero (add (var 0) (var 1)))))) :=
  closeUniv 2 (.impI (.andI (zero_negative _ Prf.hyp0) (.andI (zero_multiply _ _ Prf.hyp0) (.impI (zero_add _ _ Prf.hyp1 Prf.hyp0)))))
theorem zero_rational_domain_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (isZero (multiply zero (var 0) (var 1)) ⟶ (isZero (var 0) ⋎ isZero (var 1))) := closeUniv 2 (.impI (zero_product_reflect _ _ Prf.hyp0))
theorem zero_rational_strict_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (neg (less (var 0) (var 0)) ⋏ ((less (var 0) (var 1) ⟶ less (var 1) (var 2) ⟶ less (var 0) (var 2)) ⋏
      (less (var 0) (var 1) ⋎ (less (var 1) (var 0) ⋎ equivalent (var 0) (var 1))))) :=
  closeUniv 3 (.andI (less_irrefl _) (.andI (.impI (.impI (less_trans _ _ _ Prf.hyp1 Prf.hyp0))) (ordered_trichotomy _ _)))
theorem zero_rational_order_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (equivalent (var 0) (var 1) ⟶ equivalent (var 2) (var 3) ⟶ less (var 0) (var 2) ⟶ less (var 1) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (less_congr _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem zero_rational_order_translation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (less (var 0) (var 1) ⟶ less (add (var 0) (var 2)) (add (var 1) (var 2))) := closeUniv 3 (.impI (less_translate _ _ _ Prf.hyp0))
theorem zero_rational_positive_factor_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (positive (var 2) ⟶ less (var 0) (var 1) ⟶ less (multiply zero (var 2) (var 0)) (multiply zero (var 2) (var 1))) :=
  closeUniv 3 (.impI (.impI (less_multiply_positive _ _ _ Prf.hyp1 Prf.hyp0)))
theorem zero_rational_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    (isZero QuadraticRationalEmbedding.root ⋏
      (equivalent QuadraticRationalEmbedding.root (QuadraticRationalEmbedding.embed QuadraticRationalEmbedding.zeroScalar) ⋏
        equivalent (multiply zero QuadraticRationalEmbedding.root QuadraticRationalEmbedding.root)
          (QuadraticRationalEmbedding.embed (QuadraticRationalPairArithmetic.scalar zero)))) :=
  .andI root_isZero (.andI root_equivalent_zero root_square)
theorem actual_zero_rational_projection_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)

end LeanProofs.IPRA.Algebra.QuadraticRationalZeroProjection
