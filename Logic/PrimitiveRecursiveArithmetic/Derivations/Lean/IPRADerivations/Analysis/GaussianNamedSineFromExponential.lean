import IPRADerivations.Analysis.GaussianArctangentCayleyValues
import IPRADerivations.Analysis.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.GaussianNamedExponentialDifferenceIdentity

/-!
# Sine as a normalized combination of the original exponential names

When the input names the imaginary angle, the sine program uses the actual
named difference of its positive and negative exponentials and multiplication
by the constant Gaussian rational `-i/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSineFromExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code scale oneCode eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryPoint imaginaryCode)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNamedExponentialDifferenceIdentity (ones_equivalent)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_equivalent multiplyF multiplyData multiply_fast multiply_canonical)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_to_diagonal)
open GaussianNameRingLaws (oneF one_at one_fast negativeF negativeData negative_fast negative_equivalent
  multiply_associative multiply_commutative multiply_one multiply_one_left)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents
  qzero qmul qmul_canonical qmul_represents represents_congr)
open GaussianRationalMetric (qsub qsub_represents qnegative qnegative_represents)
open GaussianRationalReciprocal (qone qone_bounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub re_mul im_mul re_neg im_neg
  re_scale im_scale re_one im_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def multiplier : PTm n := ofGaussian (ComplexLogarithmRemainder.neg imaginaryCode) two

def differenceF (f : PR 2) : PR 2 := GaussianNamedDifference.nameF (nameF f) (nameF (negativeF f))
def differenceData (R x : PTm n) : PTm n :=
  GaussianNamedDifference.data (data R x) (data R (negativeData x))

def sineF (f : PR 2) : PR 2 := multiplyF constantF (differenceF f)
def sineData (f : PR 2) (R x : PTm n) : PTm n :=
  multiplyData constantF (differenceF f) multiplier (differenceData R x)

@[simp] theorem subst_multiplier {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (multiplier : PTm n) = multiplier := by
  simp [multiplier, ComplexLogarithmRemainder.neg, imaginaryCode]

@[simp] theorem subst_differenceData {m : ℕ} (σ : Fin n → PTm m) (R x : PTm n) :
    Syn.subst σ (differenceData R x) = differenceData (Syn.subst σ R) (Syn.subst σ x) := by
  simp [differenceData]

@[simp] theorem subst_sineData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (sineData f R x) = sineData f (Syn.subst σ R) (Syn.subst σ x) := by simp [sineData]

theorem sine_regular (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (sineF f) (sineData f R x) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianNamedDifference.name_regular _ _ _ _
    (name_regular f R x hf) (name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x hf)))

theorem sine_canonical (f : PR 2) (R x p : PTm n) :
    Γ ⊢[PRAAx] canonical (ap2 (sineF f) p (sineData f R x)) :=
  multiply_canonical _ _ _ _ _

private theorem difference_cross (f f' g g' : PR 2) (x x' y y' : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hf' : Γ ⊢[PRAAx] pointCN f' x')
    (hg : Γ ⊢[PRAAx] pointCN g y) (hg' : Γ ⊢[PRAAx] pointCN g' y')
    (he : Γ ⊢[PRAAx] crossEquivalent f f' x x') (he' : Γ ⊢[PRAAx] crossEquivalent g g' y y') :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.nameF f' g')
      (GaussianNamedDifference.data x y) (GaussianNamedDifference.data x' y') := by
  have neg := negative_equivalent g g' y y' hg hg' (cross_to_diagonal _ _ _ _ he')
  exact add_equivalent _ _ _ _ _ _ _ _ hf hf' (negative_fast _ _ hg) (negative_fast _ _ hg')
    (cross_to_diagonal _ _ _ _ he) (cross_to_diagonal _ _ _ _ neg)

private theorem constant_difference (a b : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedDifference.nameF constantF constantF) constantF
      (GaussianNamedDifference.data a b) (qsub a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _) (constant_regular _)) (constant_regular _)
  refine .allI ?_
  have raw := GaussianNamedDifference.sample_error (Γ := Γ.map Fm.shift) constantF constantF (Syn.shift a) (Syn.shift b) (var 0)
    (constant_regular _) (constant_regular _)
  have actual := distance_congr (.eqRefl _)
    ((qsub_congr (constant_at _ _) (constant_at _ _)).eqTrans (constant_at (var 0) (qsub (Syn.shift a) (Syn.shift b))).eqSymm)
    (.eqRefl _) (.eqRefl _) raw
  simpa only [GaussianNamedDifference.subst_data, GaussianRationalMetric.subst_qsub, PTm.subst_num, Syn.shift] using actual

theorem sine_exponential_cross (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (hp : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y))
    (hn : Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) (nameF (negativeF g))
      (data R (negativeData x)) (data S (negativeData y))) : Γ ⊢[PRAAx]
    crossEquivalent (sineF f) (sineF g) (sineData f R x) (sineData g S y) := by
  have fe := name_regular f R x hf
  have ge := name_regular g S y hg
  have fn := name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x hf)
  have gn := name_regular _ _ _ (GaussianExponentialInverse.negative_input g S y hg)
  have cm := constant_regular (Γ := Γ) multiplier
  exact multiply_cross _ _ _ _ _ _ _ _ cm cm
    (GaussianNamedDifference.name_regular _ _ _ _ fe fn) (GaussianNamedDifference.name_regular _ _ _ _ ge gn)
    (cross_refl _ _ cm) (difference_cross _ _ _ _ _ _ _ _ fe ge fn gn hp hn)

theorem sine_constant (f : PR 2) (R x a b : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (ha : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) a)
    (hb : Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) constantF (data R (negativeData x)) b) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) constantF (sineData f R x) (qmul multiplier (qsub a b)) := by
  have fe := name_regular f R x hf
  have fn := name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x hf)
  have d := difference_cross _ _ _ _ _ _ _ _ fe (constant_regular a) fn (constant_regular b) ha hb
  have out := cross_trans _ _ _ _ _ _ d (constant_difference a b)
  have cm := constant_regular (Γ := Γ) multiplier
  exact cross_trans _ _ _ _ _ _
    (multiply_cross _ _ _ _ _ _ _ _ cm cm (GaussianNamedDifference.name_regular _ _ _ _ fe fn)
      (constant_regular _) (cross_refl _ _ cm) out)
    (constant_product_cross multiplier (qsub a b))

private theorem one_constant (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF constantF x qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (one_fast _) (constant_regular _)
  refine .allI ?_
  simpa only [GaussianNameConjugation.pointwiseEqual, GaussianRationalReciprocal.subst_qone, Syn.shift] using
    (one_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)).eqTrans (constant_at (var 0) qone).eqSymm

private theorem inverses_cross (P Q N M : PR 2) (p q u v x y : PTm n)
    (hP : Γ ⊢[PRAAx] pointCN P p) (hQ : Γ ⊢[PRAAx] pointCN Q q)
    (hN : Γ ⊢[PRAAx] pointCN N u) (hM : Γ ⊢[PRAAx] pointCN M v)
    (he : Γ ⊢[PRAAx] crossEquivalent P Q p q)
    (hpn : Γ ⊢[PRAAx] crossEquivalent (multiplyF P N) oneF (multiplyData P N p u) x)
    (hmq : Γ ⊢[PRAAx] crossEquivalent (multiplyF M Q) oneF (multiplyData M Q v q) y) :
    Γ ⊢[PRAAx] crossEquivalent N M u v := by
  have hC := multiply_fast Q N q u hQ hN
  have m := multiply_cross P Q N N p q u u hP hQ hN hN he (cross_refl _ _ hN)
  have c := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ m)
    (cross_trans _ _ _ _ _ _ hpn (ones_equivalent x v))
  have right := cross_trans _ _ _ _ _ _
    (multiply_cross M M (multiplyF Q N) oneF v v (multiplyData Q N q u) v
      hM hM hC (one_fast v) (cross_refl _ _ hM) c)
    (multiply_one M v hM)
  have assoc := multiply_associative M Q N v q u hM hQ hN
  have left := cross_trans _ _ _ _ _ _
    (multiply_cross (multiplyF M Q) oneF N N (multiplyData M Q v q) u u u
      (multiply_fast _ _ _ _ hM hQ) (one_fast u) hN hN
      (cross_trans _ _ _ _ _ _ hmq (ones_equivalent y u)) (cross_refl _ _ hN))
    (multiply_one_left N u hN)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left) (cross_trans _ _ _ _ _ _ assoc right)

theorem negative_exponential_cross (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) (nameF (negativeF g))
      (data R (negativeData x)) (data S (negativeData y)) := by
  have hP := name_regular f R x hf
  have hQ := name_regular g S y hg
  have hN := name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x hf)
  have hM := name_regular _ _ _ (GaussianExponentialInverse.negative_input g S y hg)
  exact inverses_cross _ _ _ _ _ _ _ _ x y hP hQ hN hM he
    (GaussianExponentialInverse.exponential_inverse f R x hf)
    (cross_trans _ _ _ _ _ _ (multiply_commutative _ _ _ _ hM hQ)
      (GaussianExponentialInverse.exponential_inverse g S y hg))

/-- Invert an exact constant exponential using the original named inverse. -/
theorem negative_exponential_constant (f : PR 2) (R x a b : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) a)
    (hi : Γ ⊢[PRAAx] qmul b a ≐ qone) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (negativeF f)) constantF (data R (negativeData x)) b := by
  have product := cross_trans _ _ _ _ _ _ (constant_product_cross b a) (constant_data_cross _ _ hi)
  exact inverses_cross _ _ _ _ _ _ _ _ x x (name_regular f R x hf) (constant_regular a)
    (name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x hf)) (constant_regular b)
    he (GaussianExponentialInverse.exponential_inverse f R x hf)
    (cross_trans _ _ _ _ _ _ product (cross_symm _ _ _ _ (one_constant x)))

/-- The positive exponential already determines the value of this sine name. -/
theorem sine_cross (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y)) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) (sineF g) (sineData f R x) (sineData g S y) :=
  sine_exponential_cross f g R S x y hf hg he (negative_exponential_cross f g R S x y hf hg he)

theorem sine_proper (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) (sineF g) (sineData f R x) (sineData g S y) :=
  sine_cross f g R S x y hf hg
    (GaussianExponentialRadiusIndependence.independent_radii_proper f g R S x y hf hg he)

theorem sine_zero_of_exponential_one (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) qone) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) constantF (sineData f R x) qzero := by
  have hi : Γ ⊢[PRAAx] qmul qone qone ≐ qone :=
    GaussianReciprocalHorner.qmul_one_right _ GaussianRationalSyntheticDivision.qone_canonical
  have hn := negative_exponential_constant f R x qone qone hf he hi
  have eq : Γ ⊢[PRAAx] qmul multiplier (qsub qone qone) ≐ qzero :=
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self qone)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_zero_right _)
  exact cross_trans _ _ _ _ _ _ (sine_constant f R x _ _ hf he hn) (constant_data_cross _ _ eq)

private theorem negative_i_times_i : Γ ⊢[PRAAx] qmul (qnegative imaginaryPoint) imaginaryPoint ≐ (qone : PTm n) := by
  have hp := ofGaussian_represents (Γ := Γ) imaginaryCode one (le_refl one)
  have hn := qnegative_represents _ _ _ hp
  have hmul := qmul_represents _ _ _ _ one one (le_refl one) (le_refl one) hn hp
  have e : Γ ⊢[PRAAx] equal
      (ComplexLogarithmRemainder.mul (ComplexLogarithmRemainder.neg imaginaryCode) imaginaryCode) (scale one oneCode) := by
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode, eval_re_code, eval_im_code,
        ZT.toZ_ofNat, re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ one (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one))
    (le_refl one) (represents_congr (.eqRefl _) e (one_mul _) hmul)
    (GaussianRationalReciprocal.qone_represents_scaled one)

private theorem quarter_sine_value : Γ ⊢[PRAAx]
    qmul multiplier (qsub imaginaryPoint (qnegative imaginaryPoint)) ≐ (qone : PTm n) := by
  let i := (imaginaryCode : PTm n)
  let d : PTm n := code (ZT.ofNat zero) (ZT.ofNat two)
  let ni := ComplexLogarithmRemainder.neg i
  have hp := ofGaussian_represents (Γ := Γ) i one (le_refl one)
  have hn := qnegative_represents _ _ _ hp
  have hsub := qsub_represents _ _ _ _ _ (le_refl one) hp hn
  have eq : Γ ⊢[PRAAx] equal (GaussianRootAlgebra.sub i ni) d := by
    dsimp only [i, ni, d]
    apply equal_of_values <;>
      simp only [re_sub, im_sub, re_neg, im_neg, imaginaryCode, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;>
      ipra_simps <;> ring
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have hmul := qmul_represents multiplier _ ni d two one htwo (le_refl one)
    (ofGaussian_represents _ _ htwo) (represents_congr (.eqRefl _) eq (.eqRefl _) hsub)
  have prod : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul ni d) (scale two oneCode) := by
    dsimp only [i, ni, d]
    apply equal_of_values <;>
      simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode, eval_re_code, eval_im_code,
        ZT.toZ_ofNat, re_scale, im_scale, re_one, im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ two (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one))
    htwo (represents_congr (.eqRefl _) prod (by ipra_ring) hmul)
    (GaussianRationalReciprocal.qone_represents_scaled two)

theorem sine_one_of_exponential_i (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) imaginaryPoint) :
    Γ ⊢[PRAAx] crossEquivalent (sineF f) constantF (sineData f R x) qone := by
  have hn := negative_exponential_constant f R x imaginaryPoint (qnegative imaginaryPoint) hf he negative_i_times_i
  exact cross_trans _ _ _ _ _ _ (sine_constant f R x _ _ hf he hn) (constant_data_cross _ _ quarter_sine_value)

def integerAngleF (f : PR 2) : PR 2 := GaussianNamedNaturalScale.nameF f
def integerAngleData (E x : PTm n) : PTm n := GaussianNamedNaturalScale.data E E x
def integerAngleRadius (E R : PTm n) : PTm n := GaussianNamedNaturalScale.radius E R

theorem integer_exponential_one (f : PR 2) (E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) qone) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (integerAngleF f)) constantF
      (data (integerAngleRadius E R) (integerAngleData E x)) qone := by
  have power := GaussianBoundedIntegerExponential.integer_power_cross f E R x qone one (.andI hf (.andI he qone_bounded))
  exact cross_trans _ _ _ _ _ _ power (constant_data_cross _ _ (GaussianRationalRoundedPower.qone_power E))

theorem sine_zero_at_natural_cycles (f : PR 2) (E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) qone) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (integerAngleF f)) constantF
      (sineData (integerAngleF f) (integerAngleRadius E R) (integerAngleData E x)) qzero :=
  sine_zero_of_exponential_one _ _ _ (GaussianNamedNaturalScale.exponential_input f E E R x hf (le_refl E))
    (integer_exponential_one f E R x hf he)

theorem sine_zero_at_negative_cycles (f : PR 2) (E R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) constantF (data R x) qone) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (negativeF (integerAngleF f))) constantF
      (sineData (negativeF (integerAngleF f)) (integerAngleRadius E R)
        (negativeData (integerAngleData E x))) qzero := by
  have scaled := GaussianNamedNaturalScale.exponential_input f E E R x hf (le_refl E)
  have unitSquared : Γ ⊢[PRAAx] qmul qone qone ≐ qone :=
    GaussianReciprocalHorner.qmul_one_right _ GaussianRationalSyntheticDivision.qone_canonical
  exact sine_zero_of_exponential_one _ _ _ (GaussianExponentialInverse.negative_input _ _ _ scaled)
    (negative_exponential_constant _ _ _ _ _ scaled (integer_exponential_one f E R x hf he) unitSquared)

theorem actual_named_sine_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ pointCN (sineF f) (sineData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (sine_regular f _ _ Prf.hyp0))

theorem actual_named_sine_canonical_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (canonical (ap2 (sineF f) (var 2) (sineData f (var 0) (var 1)))) :=
  closeUniv 3 (sine_canonical f _ _ _)

theorem actual_named_sine_at_natural_cycles_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((input f (var 1) (var 2) ⋏ crossEquivalent (nameF f) constantF (data (var 1) (var 2)) qone) ⟶
      crossEquivalent (sineF (integerAngleF f)) constantF
        (sineData (integerAngleF f) (integerAngleRadius (var 0) (var 1)) (integerAngleData (var 0) (var 2))) qzero) :=
  closeUniv 3 (.impI (sine_zero_at_natural_cycles f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_named_sine_quarter_value_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((input f (var 0) (var 1) ⋏ crossEquivalent (nameF f) constantF (data (var 0) (var 1)) imaginaryPoint) ⟶
      crossEquivalent (sineF f) constantF (sineData f (var 0) (var 1)) qone) :=
  closeUniv 2 (.impI (sine_one_of_exponential_i f _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedSineFromExponential
