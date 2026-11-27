import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameConjugation
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.RationalArithmetic.Scaling.GaussianRationalNaturalScale
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianPositiveRealArithmetic

/-!
# The actual exponential and its real-part square identity

The normalized product of a raw Gaussian rational and its conjugate is
the embedding of its original computed squared norm. Its conjugate sum
is twice its actual real-coordinate projection. Both identities bind
the actual multiplication/addition name samples at their original clocks.
Exponential addition and conjugation then identify the squared-modulus
name of the original exponential with the exponential of this real sum.
Signed real exponential order and the sharper Euler-integrand magnitude
bound remain separate from this identity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialRealPart

open_ipra
open GaussianRationalHorner (qadd qmul represents canonical_unique represents_congr positive_product)
open GaussianRationalConjugation (point)
open GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open RationalGaussianEmbedding (embed native)
open GaussianRationalMetric (qnormSq)
open GaussianRationalNaturalScale (natScale)
open ComplexLogarithmRemainder (re im normSq add mul scale)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_scale im_scale)
open GaussianRationalReciprocal (conjugate re_conjugate im_conjugate)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def projection (q : PTm n) : PTm n := embed (fstT q)
ipra_subst projection

theorem projection_represents (q a E : PTm n) (h : Γ ⊢[PRAAx] represents q a E) : Γ ⊢[PRAAx]
    represents (projection q) (native (re a)) E :=
  RationalGaussianEmbedding.embed_from_representation _ _ _ h.andE₁

theorem native_conjugate_product (a : PTm n) : Γ ⊢[PRAAx]
    equal (mul a (conjugate a)) (native (ZT.ofNat (normSq a))) := by
  apply equal_of_values
  · simp only [re_mul,re_conjugate,im_conjugate,native,ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]
    rw [ComplexLogarithmRemainder.normSq_eval]
    ring
  · simp only [im_mul,re_conjugate,im_conjugate,native,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    ipra_simps
    ring

theorem native_conjugate_sum (a : PTm n) : Γ ⊢[PRAAx]
    equal (add a (conjugate a)) (scale two (native (re a))) := by
  apply equal_of_values <;>
    simp only [re_add,im_add,re_conjugate,im_conjugate,re_scale,im_scale,native,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;>
    ipra_simps <;> ring

/-- Literal code equality of the two actual canonical rational programs,
including arbitrary independently reduced input coordinates. -/
theorem conjugate_product (q : PTm n) : Γ ⊢[PRAAx]
    qmul q (point q) ≐ embed (qnormSq q) := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have hEE := positive_product (Γ := Γ) E E hE hE
  have lhs := GaussianRationalHorner.qmul_represents q (point q) a (conjugate a) E E hE hE
    (raw_represents q) (GaussianRationalConjugation.point_represents q a E hE (raw_represents q))
  have rhs := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (qnormSq q)
    (ZT.ofNat (normSq a)) (E*E) (GaussianRationalMetric.qnormSq_represents q a E hE (raw_represents q))
  exact canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (RationalGaussianEmbedding.embed_canonical _) hEE
    (represents_congr (.eqRefl _) (native_conjugate_product a) (.eqRefl _) lhs) rhs

theorem conjugate_sum (q : PTm n) : Γ ⊢[PRAAx]
    qadd q (point q) ≐ natScale two (projection q) := by
  let a := rawGaussian q
  let E := rawDen q
  have hE := raw_den_positive (Γ := Γ) q
  have lhs := GaussianRationalHorner.qadd_represents q (point q) a (conjugate a) E hE
    (raw_represents q) (GaussianRationalConjugation.point_represents q a E hE (raw_represents q))
  have rhs := GaussianRationalNaturalScale.natScale_represents two (projection q) (native (re a)) E hE
    (projection_represents q a E (raw_represents q))
  exact canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalNaturalScale.natScale_canonical _ _) hE
    (represents_congr (.eqRefl _) (native_conjugate_sum a) (.eqRefl _) lhs) rhs

theorem norm_square_positive (q : PTm n) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (embed (qnormSq q)) :=
  GaussianPositiveRealArithmetic.positive_embed _
    (GaussianRationalL1.nonnegative_of_representation _ _ _
      (positive_product _ _ (raw_den_positive q) (raw_den_positive q))
      (GaussianRationalMetric.qnormSq_represents q _ _ (raw_den_positive q) (raw_represents q)))

def doubleRealF (f : PR 2) : PR 2 := addF f (GaussianNameConjugation.nameF f)
def doubleRealData (x : PTm n) : PTm n := addData x x
def squareF (f : PR 2) : PR 2 := multiplyF f (GaussianNameConjugation.nameF f)
def squareData (f : PR 2) (x : PTm n) : PTm n :=
  multiplyData f (GaussianNameConjugation.nameF f) x x
def squarePrecision (f : PR 2) (p x : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus f (GaussianNameConjugation.nameF f) x x) p

ipra_subst doubleRealData
ipra_subst squareData
ipra_subst squarePrecision

theorem double_real_sample (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (doubleRealF f) p (doubleRealData x) ≐
      natScale two (projection (ap2 f (GaussianFastValueCut.exponent two p) x)) := by
  have e := (GaussianNameArithmetic.add_at (Γ := Γ) f (GaussianNameConjugation.nameF f) x x p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
      (GaussianNameConjugation.sample_at f _ x))).eqTrans
      ((GaussianNameArithmetic.recode_congr (conjugate_sum _)).eqTrans
        (GaussianExponentialReference.recode_fixed _ (GaussianRationalNaturalScale.natScale_canonical _ _))))
  exact e

theorem square_sample (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (squareF f) p (squareData f x) ≐ embed (qnormSq (ap2 f (squarePrecision f p x) x)) := by
  have e := (GaussianNameArithmetic.multiply_at (Γ := Γ) f (GaussianNameConjugation.nameF f) x x p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (GaussianNameConjugation.sample_at f _ x))).eqTrans
      ((GaussianNameArithmetic.recode_congr (conjugate_product _)).eqTrans
        (GaussianExponentialReference.recode_fixed _ (RationalGaussianEmbedding.embed_canonical _))))
  exact e

theorem square_sample_positive (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive (ap2 (squareF f) p (squareData f x)) :=
  GaussianPositiveRealArithmetic.positive_congr (square_sample f p x).eqSymm (norm_square_positive _)

theorem double_real_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (doubleRealF f) (doubleRealData x) :=
  GaussianNameArithmetic.add_fast f (GaussianNameConjugation.nameF f) x x hf (GaussianNameConjugation.regular f x hf)

theorem square_regular (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    pointCN (squareF f) (squareData f x) :=
  GaussianNameArithmetic.multiply_fast f (GaussianNameConjugation.nameF f) x x hf (GaussianNameConjugation.regular f x hf)

theorem double_real_input (f : PR 2) (R x : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (doubleRealF f) (R+R) (doubleRealData x) :=
  GaussianExponentialReference.add_input f (GaussianNameConjugation.nameF f) R x x hf
    (GaussianNameConjugation.exponential_input f R x hf)

/-- The left program's actual observations are embedded computed squared
norms by `square_sample`. The right argument's actual observations are
twice the real projection by `double_real_sample`. -/
theorem exponential_norm_square (f : PR 2) (R x : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) : Γ ⊢[PRAAx]
    crossEquivalent (squareF (GaussianRadiusExponentialName.nameF f))
      (GaussianRadiusExponentialName.nameF (doubleRealF f))
      (squareData (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.data R x))
      (GaussianRadiusExponentialName.data (R+R) (doubleRealData x)) := by
  let e := GaussianRadiusExponentialName.nameF f
  let c := GaussianNameConjugation.nameF f
  let X := GaussianRadiusExponentialName.data R x
  have he := GaussianRadiusExponentialName.name_regular f R x hf
  have hc := GaussianNameConjugation.exponential_input f R x hf
  have replace := GaussianNameArithmetic.multiply_equivalent e e (GaussianNameConjugation.nameF e)
    (GaussianRadiusExponentialName.nameF c) X X X X he he (GaussianNameConjugation.regular e X he)
    (GaussianRadiusExponentialName.name_regular c R x hc) (GaussianNameEquivalence.diagonal_refl e X)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (GaussianNameConjugation.exponential_cross f R x hf))
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent f c (doubleRealF f)
    R R (R+R) x x (doubleRealData x) hf hc (double_real_input f R x hf)
    (GaussianNameEquivalence.cross_refl _ _ (double_real_regular f x hf.andE₁))
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ replace addition

theorem actual_conjugate_square_and_real_sum_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((qmul (var 0) (point (var 0)) ≐ embed (qnormSq (var 0))) ⋏
      (qadd (var 0) (point (var 0)) ≐ natScale two (projection (var 0)))) :=
  closeUniv 1 (.andI (conjugate_product _) (conjugate_sum _))

theorem actual_twice_real_name_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (doubleRealF f) (var 0) (doubleRealData (var 1)) ≐
      natScale two (projection (ap2 f (GaussianFastValueCut.exponent two (var 0)) (var 1)))) :=
  closeUniv 2 (double_real_sample f _ _)

theorem actual_squared_modulus_name_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 (squareF f) (var 0) (squareData f (var 1)) ≐
      embed (qnormSq (ap2 f (squarePrecision f (var 0) (var 1)) (var 1)))) :=
  closeUniv 2 (square_sample f _ _)

theorem actual_real_sum_and_squared_modulus_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN f (var 0) ⟶ (pointCN (doubleRealF f) (doubleRealData (var 0)) ⋏
      pointCN (squareF f) (squareData f (var 0)))) :=
  closeUniv 1 (.impI (.andI (double_real_regular f _ Prf.hyp0) (square_regular f _ Prf.hyp0)))

theorem actual_squared_modulus_samples_nonnegative_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianPositiveRealArithmetic.positive (ap2 (squareF f) (var 0) (squareData f (var 1)))) :=
  closeUniv 2 (square_sample_positive f _ _)

theorem actual_exponential_squared_modulus_identity_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRadiusExponentialName.input f (var 0) (var 1) ⟶
      crossEquivalent (squareF (GaussianRadiusExponentialName.nameF f))
        (GaussianRadiusExponentialName.nameF (doubleRealF f))
        (squareData (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.data (var 0) (var 1)))
        (GaussianRadiusExponentialName.data (var 0+var 0) (doubleRealData (var 1)))) :=
  closeUniv 2 (.impI (exponential_norm_square f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianExponentialRealPart
