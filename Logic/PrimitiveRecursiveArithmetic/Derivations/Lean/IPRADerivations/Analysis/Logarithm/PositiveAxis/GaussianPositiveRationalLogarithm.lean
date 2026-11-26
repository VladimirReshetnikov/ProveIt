import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinMeshExponential

/-!
# A positive rational logarithm using the original harmonic-mesh samples

For positive numerical a,b, the actual logarithm is the sum of the old
mesh logarithm of a and its old negative-logarithm constructor at b.
The original sample programs derive regularity. Their checked positive
and negative exponential identities, with the genuine named addition
law, prove that the actual exponential is the canonical fraction a/b.
The numerical exponential radius is computed from the true zeroth sample.
This supplies a logarithm evaluator, without an assumed logarithm law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithm

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian qmul represents positive_product canonical_unique represents_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open ComplexLogarithmRemainder (oneCode scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def baseF : PR 2 := GaussianGammaFiniteApproximantName.logF
def negativeF : PR 2 := GaussianGammaFiniteApproximantName.logExponentF
def logF : PR 2 := addF baseF negativeF
def data (a b : PTm n) : PTm n := addData a (GaussianGammaEulerShift.negativeLogData b)
def source (a b : PTm n) : Fm PTm n := le one a ⋏ le one b
def fraction (a b : PTm n) : PTm n := ofGaussian (scale a oneCode) b
def radius (a b : PTm n) : PTm n := GaussianNameBounds.U logF (data a b)
def expF : PR 2 := GaussianRadiusExponentialName.nameF logF
def expData (a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius a b) (data a b)
def sample (p a b : PTm n) : PTm n := ap2 logF p (data a b)

ipra_subst data [GaussianGammaEulerShift.negativeLogData]
ipra_subst source
ipra_subst fraction
ipra_subst radius
ipra_subst expData
ipra_subst sample

theorem name_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN logF (data a b) :=
  add_fast baseF negativeF a (GaussianGammaEulerShift.negativeLogData b)
    (GaussianGammaFiniteApproximantName.log_regular a h.andE₁)
    (GaussianGammaEulerShift.negative_log_regular b h.andE₂)

theorem sample_at (p a b : PTm n) : Γ ⊢[PRAAx] sample p a b ≐
    GaussianFastValueCut.recode (GaussianRationalHorner.qadd
      (ap2 baseF (GaussianFastValueCut.exponent two p) a)
      (ap2 negativeF (GaussianFastValueCut.exponent two p) (GaussianGammaEulerShift.negativeLogData b))) :=
  GaussianNameArithmetic.add_at baseF negativeF a (GaussianGammaEulerShift.negativeLogData b) p

theorem sample_canonical (p a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample p a b) :=
  GaussianRationalHorner.canonical_congr (sample_at p a b) (GaussianFastValueCut.recode_canonical _)

theorem sample_bound (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (sample p a b) (radius a b) one :=
  GaussianNameBounds.sample_bound logF (data a b) p (name_regular a b h)

theorem exponential_input (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input logF (radius a b) (data a b) :=
  GaussianGammaFiniteApproximantName.exponential_input logF (data a b) (name_regular a b h)

theorem exponential_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN expF (expData a b) :=
  GaussianRadiusExponentialName.name_regular logF (radius a b) (data a b) (exponential_input a b h)

theorem fraction_product (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qmul (naturalPoint a) (GaussianGammaEulerShiftLimit.reciprocalPoint b) ≐ fraction a b := by
  have raw := GaussianRationalHorner.qmul_represents (naturalPoint a)
    (GaussianGammaEulerShiftLimit.reciprocalPoint b) (scale a oneCode) oneCode one b (le_refl one) hb
    (natural_point_represents a) (GaussianRationalHorner.ofGaussian_represents _ _ hb)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul (scale a oneCode) oneCode) (scale a oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ring
  exact canonical_unique _ _ _ b (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb
    (represents_congr (.eqRefl _) same (one_mul b) raw)
    (GaussianRationalHorner.ofGaussian_represents _ _ hb)

theorem exponential_fraction (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent expF constantF (expData a b) (fraction a b) := by
  let X := GaussianGammaFiniteApproximantName.exponentialInputData baseF a
  let Y := GaussianGammaEulerShift.negativeLogExpData b
  let F := GaussianRadiusExponentialName.nameF baseF
  let G := GaussianRadiusExponentialName.nameF negativeF
  let u := naturalPoint a
  let v := GaussianGammaEulerShiftLimit.reciprocalPoint b
  have hi := GaussianGammaFiniteApproximantName.exponential_input baseF a
    (GaussianGammaFiniteApproximantName.log_regular a h.andE₁)
  have hj := GaussianGammaFiniteApproximantName.exponential_input negativeF
    (GaussianGammaEulerShift.negativeLogData b) (GaussianGammaEulerShift.negative_log_regular b h.andE₂)
  have law := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent baseF negativeF logF
    _ _ _ a (GaussianGammaEulerShift.negativeLogData b) (data a b) hi hj
    (exponential_input a b h) (cross_refl logF (data a b) (name_regular a b h))
  have first := GaussianGammaAdjacentCutoff.multiply_cross F constantF G constantF X u Y v
    (GaussianRadiusExponentialName.name_regular baseF _ a hi) (constant_regular u)
    (GaussianGammaEulerShift.negative_log_exp_regular b h.andE₂) (constant_regular v)
    (GaussianRobinMeshExponential.mesh_exponential a h.andE₁)
    (GaussianRobinMeshExponential.mesh_exponential_inverse b h.andE₂)
  have product := GaussianGammaWeierstrassApproximant.constant_product_cross (Γ := Γ) u v
  have value := GaussianGammaWeierstrassApproximant.constant_data_cross (Γ := Γ) _ _ (fraction_product a b h.andE₂)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ law)
    (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ product value))


def differenceF : PR 2 := addF baseF (GaussianNameRingLaws.negativeF baseF)
def differenceData (a b : PTm n) : PTm n := addData a (GaussianNameRingLaws.negativeData b)

/-- The implemented logarithm is the actual named difference of the two
original mesh logarithms, retaining their separate normalizer clocks. -/
theorem original_logarithm_difference (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent logF differenceF (data a b) (differenceData a b) :=
  GaussianNameArithmetic.add_equivalent baseF baseF negativeF (GaussianNameRingLaws.negativeF baseF)
    a a (GaussianGammaEulerShift.negativeLogData b) (GaussianNameRingLaws.negativeData b)
    (GaussianGammaFiniteApproximantName.log_regular a h.andE₁)
    (GaussianGammaFiniteApproximantName.log_regular a h.andE₁)
    (GaussianGammaEulerShift.negative_log_regular b h.andE₂)
    (GaussianNameRingLaws.negative_fast baseF b (GaussianGammaFiniteApproximantName.log_regular b h.andE₂))
    (GaussianNameEquivalence.diagonal_refl _ _)
    (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (GaussianMeshLogSign.original_log_negation b h.andE₂))

theorem base_axis (p a : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (ap2 baseF p a) :=
  RationalGaussianNameEmbedding.sample_axis GammaMeshRobinLogBridge.meshLogF p a

theorem negative_axis (p b : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis
    (ap2 negativeF p (GaussianGammaEulerShift.negativeLogData b)) := by
  let q := GaussianFastValueCut.exponent
    (GaussianNameArithmetic.multiplyModulus baseF constantF b GaussianRationalMatrixFiniteSums.minusOne) p
  have eq := (GaussianNameArithmetic.multiply_at (Γ := Γ) baseF constantF b GaussianRationalMatrixFiniteSums.minusOne p).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
      (GaussianGammaCanonicalExponent.constant_at q GaussianRationalMatrixFiniteSums.minusOne))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))
  exact RationalGaussianEmbedding.axis_congr eq.eqSymm
    (RationalGaussianEmbedding.axis_multiply _ _ (base_axis q b)
      (RationalGaussianEmbedding.axis_negative _ RationalGaussianEmbedding.axis_one))

theorem sample_axis (p a b : PTm n) : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis (sample p a b) := by
  have eq := (sample_at (Γ := Γ) p a b).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  exact RationalGaussianEmbedding.axis_congr eq.eqSymm
    (RationalGaussianEmbedding.axis_add _ _ (base_axis _ a) (negative_axis _ b))

theorem original_positive_rational_logarithm_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ pointCN logF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))
theorem actual_positive_rational_logarithm_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (sample (var 0) (var 1) (var 2) ≐ GaussianFastValueCut.recode (GaussianRationalHorner.qadd
      (ap2 baseF (GaussianFastValueCut.exponent two (var 0)) (var 1))
      (ap2 negativeF (GaussianFastValueCut.exponent two (var 0)) (GaussianGammaEulerShift.negativeLogData (var 2))))) :=
  closeUniv 3 (sample_at _ _ _)
theorem actual_positive_rational_logarithm_real_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalHorner.canonical (sample (var 0) (var 1) (var 2)) ⋏
      RationalGaussianEmbedding.axis (sample (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (sample_canonical _ _ _) (sample_axis _ _ _))
theorem original_positive_rational_logarithm_computed_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ GaussianRationalMetric.bounded (sample (var 0) (var 1) (var 2))
      (radius (var 1) (var 2)) one) := closeUniv 3 (.impI (sample_bound _ _ _ Prf.hyp0))
theorem original_positive_rational_logarithm_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent logF differenceF (data (var 0) (var 1)) (differenceData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_logarithm_difference _ _ Prf.hyp0))
theorem original_positive_rational_logarithm_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent expF constantF (expData (var 0) (var 1)) (fraction (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_fraction _ _ Prf.hyp0))
theorem actual_positive_rational_logarithm_exponential_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ pointCN expF (expData (var 0) (var 1))) :=
  closeUniv 2 (.impI (exponential_regular _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithm
