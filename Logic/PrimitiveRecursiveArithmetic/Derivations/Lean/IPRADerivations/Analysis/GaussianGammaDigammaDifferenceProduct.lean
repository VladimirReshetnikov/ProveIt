import IPRADerivations.Analysis.GaussianGammaDigammaStep
import IPRADerivations.Analysis.GaussianRationalInverseQuadraticAlgebra

/-!
# Exact product rule for the native Gamma divided differences

At the two rational endpoints x and x+1/D, the Gamma recurrence
identifies the divided difference at x+1 with the sum of Gamma(x)
and (x+1/D) times the divided difference at x.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDifferenceProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaNative (minimumDenominator)
open GaussianGammaDigammaStep (neighborNumerator neighborDenominator neighborData stepQuotientData neighbor_source)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast multiplyModulus)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (three)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (qadd qmul canonical ofGaussian)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qsub_congr qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingGammaLogarithm (source arg gammaData gamma_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "MF" => multiplyF constantF gammaF
local notation "md" => multiplyData constantF gammaF
local notation "inv" => GaussianNamedDifferenceQuotient.inverse
local notation "cost" => GaussianNamedDifferenceQuotient.cost

def coefficient (a b D : PTm n) : PTm n := fraction (neighborNumerator a b D) (neighborDenominator b D)
def productF : PR 2 := multiplyF constantF QF
def productData (a b D : PTm n) : PTm n := multiplyData constantF QF (coefficient a b D) (stepQuotientData a b D)
def nameF : PR 2 := addF productF gammaF
def data (a b D : PTm n) : PTm n := addData (productData a b D) (gammaData a b)

def upperInputData (a b D : PTm n) : PTm n := md (coefficient a b D) (neighborData a b D)
def lowerInputData (a b : PTm n) : PTm n := md (fraction a b) (gammaData a b)

@[simp] theorem subst_neighborNumerator {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (neighborNumerator a b D) = neighborNumerator (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [neighborNumerator]

@[simp] theorem subst_neighborDenominator {m : ℕ} (σ : Fin n → PTm m) (b D : PTm n) :
    Syn.subst σ (neighborDenominator b D) = neighborDenominator (Syn.subst σ b) (Syn.subst σ D) := by
  simp [neighborDenominator]

@[simp] theorem subst_neighborData {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (neighborData a b D) = neighborData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [neighborData]

@[simp] theorem subst_stepQuotientData {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (stepQuotientData a b D) = stepQuotientData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [stepQuotientData]

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (coefficient a b D) = coefficient (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [coefficient]

@[simp] theorem subst_productData {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (productData a b D) = productData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [productData]

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (data a b D) = data (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [data]

@[simp] theorem subst_upperInputData {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (upperInputData a b D) = upperInputData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [upperInputData]

@[simp] theorem subst_lowerInputData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (lowerInputData a b) = lowerInputData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [lowerInputData]

theorem nativeInput (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input gammaF gammaF
      (neighborData a b D) (gammaData a b) oneCode D :=
  .andI (gamma_regular _ _ (neighbor_source a b D hs hD))
    (.andI (gamma_regular a b hs) (GaussianGammaUnitInverseSamples.actual_step_separated D hD))

theorem quotient_regular (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN QF (stepQuotientData a b D) :=
  GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ (nativeInput a b D hs hD)

theorem product_regular (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN productF (productData a b D) :=
  multiply_fast _ _ _ _ (constant_regular _) (quotient_regular a b D hs hD)

theorem name_regular (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN nameF (data a b D) :=
  add_fast _ _ _ _ (product_regular a b D hs hD) (gamma_regular a b hs)

theorem raw_product_rule (a b D g h : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] canonical h) :
    Γ ⊢[PRAAx] qmul (inv oneCode D)
      (qsub (qmul (coefficient a b D) g) (qmul (fraction a b) h)) ≐
      qadd (qmul (coefficient a b D) (qmul (inv oneCode D) (qsub g h))) h := by
  let u := coefficient a b D
  let v := fraction a b
  let k := inv oneCode D
  let δ := ofGaussian oneCode D
  have hd : Γ ⊢[PRAAx] qsub (qmul u g) (qmul v h) ≐ qadd (qmul u (qsub g h)) (qmul δ h) :=
    (qsub_congr (qmul_commutative u g) (qmul_commutative v h)).eqTrans
      ((GaussianRationalPowerDifference.product_difference g h u v).eqTrans
        (qadd_congr (qmul_commutative _ _) ((qmul_commutative _ _).eqTrans
          (qmul_congr (GaussianGammaDigammaStep.coefficient_difference a b D hb hD) (.eqRefl _)))))
  have first := (qmul_associative (Γ := Γ) k u (qsub g h)).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative k u) (.eqRefl _)).eqTrans (qmul_associative u k (qsub g h)))
  have second := GaussianRationalInverseQuadraticAlgebra.cancel_nested_product k δ h hh
    (GaussianNamedDifferenceQuotient.actual_inverse oneCode D (GaussianGammaUnitInverseSamples.actual_step_separated D hD))
  exact (qmul_congr (.eqRefl _) hd).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add k _ _).eqTrans (qadd_congr first second))


def finiteBudget (a b D : PTm n) : PTm n :=
  cost MF MF (upperInputData a b D) (lowerInputData a b) oneCode D+
    D*((multiplyModulus constantF gammaF (coefficient a b D) (neighborData a b D)+one)+
       (multiplyModulus constantF gammaF (fraction a b) (gammaData a b)+one))+
    (three+(multiplyModulus constantF QF (coefficient a b D) (stepQuotientData a b D)+one)+
      (a+one)*cost gammaF gammaF (neighborData a b D) (gammaData a b) oneCode D)

@[simp] theorem subst_finiteBudget {m : ℕ} (σ : Fin n → PTm m) (a b D : PTm n) :
    Syn.subst σ (finiteBudget a b D) = finiteBudget (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ D) := by
  simp [finiteBudget,three]

set_option maxHeartbeats 1000000 in
theorem finite_at (p a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianNamedDifferenceQuotient.nameF MF MF) p
        (GaussianNamedDifferenceQuotient.data MF MF (upperInputData a b D) (lowerInputData a b) oneCode D))
      (ap2 nameF p (data a b D)) (finiteBudget a b D) (unit p) := by
  let u := coefficient a b D
  let v := fraction a b
  let x := neighborData a b D
  let y := gammaData a b
  let q := stepQuotientData a b D
  have hb := unit_positive (Γ := Γ) p
  have hx := gamma_regular _ _ (neighbor_source a b D hs hD)
  have hy := gamma_regular _ _ hs
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have hq := quotient_regular a b D hs hD
  have hp := product_regular a b D hs hD
  have hux := multiply_fast _ _ _ _ hu hx
  have hvy := multiply_fast _ _ _ _ hv hy
  have sep := GaussianGammaUnitInverseSamples.actual_step_separated D hD
  have start := GaussianNamedDifferenceQuotient.sample_error MF MF p (upperInputData a b D) (lowerInputData a b) oneCode D
    (.andI hux (.andI hvy sep))
  have l := distance_congr (.eqRefl _) (qmul_congr (constant_at p u) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF gammaF u x p hu hx)
  have r := distance_congr (.eqRefl _) (qmul_congr (constant_at p v) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF gammaF v y p hv hy)
  have diff := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hb l r
  have scaled := GaussianNamedDifferenceQuotient.scale_distance (inv oneCode D) _ _ D _ _ hb
    (GaussianNamedDifferenceQuotient.inverse_bound oneCode D sep) diff
  have lhs := distance_triangle_same _ _ _ _ _ _ hb start scaled
  have finish := GaussianNameRingLaws.add_sample_error productF gammaF (productData a b D) y p hp hy
  have prod := distance_congr (.eqRefl _) (qmul_congr (constant_at p u) (.eqRefl _)) (.eqRefl _) (.eqRefl _)
    (GaussianNameRingLaws.multiply_sample_error constantF QF u q p hu hq)
  have f := distance_triangle_same _ _ _ _ _ _ hb finish (GaussianNameRingLaws.sum_left_error _ _ _ _ _ hb prod)
  have qr := GaussianNamedDifferenceQuotient.sample_error gammaF gammaF p x y oneCode D (nativeInput a b D hs hD)
  have factor := GaussianNamedDifferenceQuotient.scale_distance u _ _ (a+one) _ _ hb
    (GaussianGammaDigammaStep.neighbor_coefficient_bound a b D hs.andE₂ hD) qr
  have rhs := distance_triangle_same _ _ _ _ _ _ hb f (GaussianNameRingLaws.sum_left_error _ _ _ _ _ hb factor)
  have exactRule := raw_product_rule a b D (ap2 gammaF p x) (ap2 gammaF p y) hs.andE₂ hD
    (GaussianNameReciprocal.name_canonical GaussianGammaC7Name.nameF
      (GaussianGammaReciprocalInverse.gammaHeight (arg a) a b b) (GaussianGammaC7Name.data (arg a) a b) p)
  exact GaussianNameRingLaws.through_identity _ _ _ _ _ _ _ hb lhs rhs exactRule

set_option maxHeartbeats 800000 in
theorem finite_cross (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifferenceQuotient.nameF MF MF) nameF
      (GaussianNamedDifferenceQuotient.data MF MF (upperInputData a b D) (lowerInputData a b) oneCode D)
      (data a b D) := by
  have hx := gamma_regular _ _ (neighbor_source a b D hs hD)
  have hy := gamma_regular _ _ hs
  have hux := multiply_fast _ _ _ _ (constant_regular (Γ := Γ) (coefficient a b D)) hx
  have hvy := multiply_fast _ _ _ _ (constant_regular (Γ := Γ) (fraction a b)) hy
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (finiteBudget a b D)
    (GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _
      (.andI hux (.andI hvy (GaussianGammaUnitInverseSamples.actual_step_separated D hD))))
    (name_regular a b D hs hD) (.allI ?_)
  have h : (Γ.map Fm.shift) ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  have d : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift D) := by simpa only [Fm.shift,Syn.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hD.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,GaussianNamedDifferenceQuotient.subst_data,
    ComplexLogarithmRemainder.subst_oneCode,subst_upperInputData,subst_lowerInputData,subst_data,subst_finiteBudget] using
    finite_at (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift D) h d

private theorem neighbor_shift_data (a b D : PTm n) : Γ ⊢[PRAAx]
    gammaData (neighborNumerator a b D+neighborDenominator b D) (neighborDenominator b D) ≐
      neighborData (a+b) b D := by
  have e : Γ ⊢[PRAAx] neighborNumerator a b D+neighborDenominator b D ≐ neighborNumerator (a+b) b D := by
    unfold neighborNumerator neighborDenominator
    ipra_ring
  simpa [neighborData] using Prf.eqCongr (gammaData (var 0) (var 1) : PTm 2)
    (σ := ![neighborNumerator a b D+neighborDenominator b D,neighborDenominator b D])
    (σ' := ![neighborNumerator (a+b) b D,neighborDenominator b D])
    (fun i => by fin_cases i; exact e; exact .eqRefl _)

set_option maxHeartbeats 1500000 in
theorem step_product_rule (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent QF nameF (stepQuotientData (a+b) b D) (data a b D) := by
  let c := neighborNumerator a b D
  let d := neighborDenominator b D
  have hn := neighbor_source a b D hs hD
  have hi := GaussianStirlingGammaLogarithm.source_shift _ _ hs
  have upper := GaussianGammaRealValues.cross_right_data (neighbor_shift_data (Γ := Γ) a b D)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianStirlingGammaLogShift.gamma_increment c d hn))
  have lower := GaussianStirlingGammaLogShift.gamma_increment a b hs
  have hC := constant_regular (Γ := Γ) (coefficient a b D)
  have hv := constant_regular (Γ := Γ) (fraction a b)
  have h1 := GaussianNamedDifferenceQuotientProperness.proper gammaF MF gammaF MF
    (neighborData (a+b) b D) (upperInputData a b D) (gammaData (a+b) b) (lowerInputData a b) oneCode D
    (gamma_regular _ _ (neighbor_source (a+b) b D hi hD))
    (multiply_fast _ _ _ _ hC (gamma_regular _ _ hn))
    (gamma_regular (a+b) b hi) (multiply_fast _ _ _ _ hv (gamma_regular _ _ hs))
    (GaussianNameEquivalence.cross_symm _ _ _ _ upper) lower
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ h1 (finite_cross a b D hs hD)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDifferenceProduct
