import IPRADerivations.Analysis.Beta.GaussianBetaKernelTailDifference
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarRadiusProductBound

/-!
# One half-decay majorant for the original beta--Euler row difference

On the full beta support compare the two kernels before multiplying
by the actual original complex power observation. The one-copy kernel
reference bound transfers through an exact scalar radius. Auxiliary
reference errors are removed at one finite rational gap query; the
factorial half-decay coefficient is never doubled.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaEulerTailDifferencePointwise

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerUpperPowerCompatibility (old_source)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData sample sample_at)
open GaussianEulerCompactProductComparison (clock original_product)
open GaussianBetaKernelUpperTail (row powerBudget upperReference positiveReference power_clock_budget original_product_bound)
open GaussianBetaKernelExponential (kernel)
open GaussianBetaKernelDecayDampedError (referenceBudget referenceDenominator reference_positive reference_representation)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom reference_bottom_positive)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianRationalHorner (qmul represents positive_product)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p q R a b : PTm n) : PTm n := majorant R*referenceTop q a b*unit p+num 7*referenceBottom q a b
def denominator (p q a b : PTm n) : PTm n := referenceBottom q a b*unit p
def difference (p z B a b N : PTm n) : PTm n := qsub (row p z B a b N) (sample p z B a b)
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q R a b : PTm n) :
    Syn.subst σ (numerator p q R a b) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p q a b : PTm n) :
    Syn.subst σ (denominator p q a b) = denominator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) := by simp [denominator]
@[simp] theorem subst_difference {m : ℕ} (σ : Fin n → PTm m) (p z B a b N : PTm n) :
    Syn.subst σ (difference p z B a b N) = difference (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [difference]

theorem upper_reference_representation (s a b : PTm n) : Γ ⊢[PRAAx]
    represents (upperReference s a b) (RationalGaussianEmbedding.native (ZT.ofNat (referenceBudget s a b)))
      (referenceDenominator s a b*unit s) := by
  have extra := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat (num 3)) (unit s) (unit_positive s)
  have raw := RationalRepresentations.represents_add _ _ _ _ _ _ (reference_representation s a b) extra
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents
      (RationalArithmetic.add (fstT (positiveReference s a b)) (GaussianEuclideanDistanceName.fraction (num 3) (unit s)))
      (ZT.ofNat (referenceBudget s a b)) (referenceDenominator s a b*unit s) := by
    refine GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _) raw
    apply ZT.derive
    simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,referenceBudget]
    ipra_simps
  exact RationalGaussianEmbedding.embed_from_representation _ _ _ rep

theorem reference_product_error (p s z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (ap2 powerF (clock p z B a b) (powerData z B a b)) (positiveReference s a b))
      (ap2 productF p (productData z B a b)) (powerBudget z B a b*unit p+unit s) (unit s*unit p) := by
  let k := clock p z B a b
  let U := powerBudget z B a b
  have hs := unit_positive (Γ := Γ) s
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have old := GaussianApproximateInverseDistance.multiply_distance (ap2 powerF k (powerData z B a b))
    (positiveReference s a b) (ap2 decayF k (decayData a b)) U (unit s+unit k) (unit s*unit k)
    (positive_product _ _ hs hk)
    (GaussianNameBounds.sample_bound powerF (powerData z B a b) k (GaussianEulerIntegrandName.power_regular z B a b (old_source z R B a b h)))
    (GaussianBetaKernelUpperTail.reference_error s k a b h.andE₂.andE₁.andE₂)
  have lifted := mul_le_mul_right (unit s*unit s) (power_clock_budget (Γ := Γ) p z B a b)
  have compare : Γ ⊢[PRAAx] le ((U*(unit s+unit k))*(unit s*unit p))
      ((U*unit p+unit s)*(unit s*unit k)) :=
    le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (U*unit k*unit s*unit p) lifted)
  exact distance_congr (.eqRefl _) (original_product p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hs hk) (positive_product _ _ hs hp) compare old)

theorem original_difference_slack (p q s z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (difference p z B a b N) (numerator p q R a b) (denominator p q a b)
      (num 5*powerBudget z B a b) s := by
  let k := clock p z B a b
  let x := ap2 powerF k (powerData z B a b)
  let v := upperReference s a b
  let P := unit p
  let S := unit s
  let D := referenceBottom q a b
  let A := majorant R*referenceTop q a b
  let U := powerBudget z B a b
  let Z := D*P*S
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have hd := reference_bottom_positive (Γ := Γ) q a b
  have hz : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ hd hp) hs
  have kernelSource : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N := .andI h.andE₂.andE₁.andE₂ (.andI hN ht)
  have result := GaussianReconstructionRoots.norm_from_distance (qmul x v) (ap2 productF p (productData z B a b))
    (num 4*U*P+S) (S*P) (A*P+num 3*D) (D*P)
    (positive_product _ _ hs hp) (positive_product _ _ hd hp)
    (GaussianBetaKernelUpperTail.upper_product_error p s z R B a b h) (original_product_bound p q z R B a b h)
  have referenceBound : Γ ⊢[PRAAx] bounded (qmul x v) ((A*P+num 4*D)*S+num 4*U*D*P) Z :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hs hp) (positive_product _ _ hd hp)) hz
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) result
  have core := GaussianScalarRadiusProductBound.original_product_bound x (qsub (kernel a b N) (positiveReference s a b)) v
    (referenceBudget s a b) (referenceDenominator s a b*S) _ Z
    (positive_product _ _ (reference_positive s a b) hs) hz (upper_reference_representation s a b)
    (GaussianBetaKernelTailDifference.original_kernel_reference_distance s a b N kernelSource) referenceBound
  have left : Γ ⊢[PRAAx] distanceBounded (row p z B a b N) (qmul x (positiveReference s a b))
      ((A*P+num 4*D)*S+num 4*U*D*P) Z :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference x _ _).eqSymm (.eqRefl _) (.eqRefl _) core
  have middle := distance_radius_mono _ _ _ _ ((U*P+S)*D) Z (positive_product _ _ hs hp) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) (reference_product_error p s z R B a b h)
  have cross := GaussianNameEquivalence.cross_at productF GaussianEulerIntegrandName.nameF _ _ p p
    (GaussianEulerIntegrandName.original_power_times_decay z B a b (old_source z R B a b h))
  have right := distance_radius_mono _ _ _ _ (two*D*S) Z (positive_product _ _ hp hp) hz
    (le_of_eq_add (d := zero) (by dsimp only [Z,P]; ipra_ring))
    (distance_congr (.eqRefl _) (sample_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _) cross)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [numerator,denominator,A,D,P,S,U,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hz (distance_triangle_same _ _ _ _ _ _ hz left middle) right)

/-- One original factorial half-decay reference, with seven ordinary
row-observation errors. This holds on the entire beta support. -/
theorem original_difference_pointwise (p q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    distanceBounded (row p z B a b N) (sample p z B a b) (numerator p q R a b) (denominator p q a b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 5*powerBudget z B a b)
    (positive_product _ _ (reference_bottom_positive q a b) (unit_positive p))
    (original_difference_slack p q (GaussianRationalSlackRemoval.precision (difference p z B a b N)
      (numerator p q R a b) (denominator p q a b) (num 5*powerBudget z B a b)) z R B a b N h hN ht)

def scalarMajorant (p R a b : PTm n) : PTm n := RationalArithmetic.add
  (GaussianEulerUpperTailScalar.scalarMajorant p R a b) (GaussianEuclideanDistanceName.fraction (num 6) (unit p))
def referenceError (R : PTm n) : PTm n := num 3*majorant R+num 7
@[simp] theorem subst_scalarMajorant {m : ℕ} (σ : Fin n → PTm m) (p R a b : PTm n) :
    Syn.subst σ (scalarMajorant p R a b) = scalarMajorant (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) := by simp [scalarMajorant]
@[simp] theorem subst_referenceError {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (referenceError R) = referenceError (Syn.subst σ R) := by simp [referenceError]

theorem original_difference_cell_majorized (p z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    GaussianRationalSumMajorant.majorized (difference p z B a b N) (scalarMajorant p R a b) := by
  let U := unit p
  let A := numerator p p R a b
  let D := denominator p p a b
  have hu := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (reference_bottom_positive p a b) hu
  have old : Γ ⊢[PRAAx] RationalArithmetic.represents (GaussianEulerUpperTailScalar.scalarMajorant p R a b)
      (ZT.ofNat (GaussianEulerUpperTailPointwise.majorantTop p p R a b)) D :=
    RationalIntegerNormalization.normalize_preserves_value _ _ hd
  have extra := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat (num 6)) U hu
  have both := RationalRepresentations.represents_add _ _ _ _ _ _ old extra
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (scalarMajorant p R a b) (ZT.ofNat (A*U)) (D*U) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
      dsimp only [A,D,numerator,denominator,GaussianEulerUpperTailPointwise.majorantTop]
      ipra_simps
      ring) (.eqRefl _) both
  have den := positive_product _ _ hd hu
  exact GaussianRationalSumMajorant.from_representation _ _ _ _ den
    (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (bounded_radius_mono _ _ _ _ _ hd den (le_of_eq_add (d := zero) (by ipra_ring))
      (original_difference_pointwise p p z R B a b N h hN ht))

theorem scalar_majorant_half_reference_error (p R a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (RationalGaussianEmbedding.embed (scalarMajorant p R a b))
      (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant R) one) (GaussianEulerWeightedHalfDecay.halfSample p a b))
      (referenceError R) (unit p) := by
  let old := RationalGaussianEmbedding.embed (GaussianEulerUpperTailScalar.scalarMajorant p R a b)
  let extra := RationalGaussianEmbedding.embed (GaussianEuclideanDistanceName.fraction (num 6) (unit p))
  have hu := unit_positive (Γ := Γ) p
  have value : Γ ⊢[PRAAx] extra ≐ GaussianDominantPairAlgebra.radiusPoint (num 6) (unit p) :=
    (GaussianEulerDecayOrder.fraction_embedding _ _ hu).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hu)
  have extraBound : Γ ⊢[PRAAx] bounded extra (num 6) (unit p) :=
    bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded _ _ hu)
  have near : Γ ⊢[PRAAx] distanceBounded (RationalGaussianEmbedding.embed (scalarMajorant p R a b)) old (num 6) (unit p) :=
    bound_congr ((GaussianRationalSyntheticDivision.qsub_congr (RationalGaussianEmbedding.embed_add _ _) (.eqRefl old)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel old extra (RationalGaussianEmbedding.embed_canonical _))).eqSymm
      (.eqRefl _) (.eqRefl _) extraBound
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold referenceError GaussianEulerUpperTailScalar.budget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu near (GaussianEulerUpperTailScalar.scalar_majorant_scaled_reference_error p R a b hb))

theorem original_full_support_beta_Euler_one_half_decay_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ (le one (var 7) ⋏ le (var 5) (var 6*var 7)) ⟶
      distanceBounded (row (var 0) (var 2) (var 4) (var 5) (var 6) (var 7)) (sample (var 0) (var 2) (var 4) (var 5) (var 6))
        (numerator (var 0) (var 1) (var 3) (var 5) (var 6)) (denominator (var 0) (var 1) (var 5) (var 6))) :=
  closeUniv 8 (.impI (.impI (original_difference_pointwise _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))
theorem original_full_support_beta_Euler_difference_scalar_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ (le one (var 6) ⋏ le (var 4) (var 5*var 6)) ⟶
      GaussianRationalSumMajorant.majorized (difference (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
        (scalarMajorant (var 0) (var 2) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.impI (original_difference_cell_majorized _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))
theorem original_difference_scalar_half_decay_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (RationalGaussianEmbedding.embed (scalarMajorant (var 0) (var 1) (var 2) (var 3)))
      (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant (var 1)) one) (GaussianEulerWeightedHalfDecay.halfSample (var 0) (var 2) (var 3)))
      (referenceError (var 1)) (unit (var 0))) :=
  closeUniv 4 (.impI (scalar_majorant_half_reference_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaEulerTailDifferencePointwise
