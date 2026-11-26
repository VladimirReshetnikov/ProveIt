import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootSharpResidualSamples
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootDistanceOrderBudget
import IPRADerivations.Analysis.Names.GaussianLinearDistanceName
import IPRADerivations.Analysis.RationalArithmetic.GaussianScalarOrderCut
import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianRootAdequacy

/-!
# Sharp represented residual bound by the actual root distance

Source04 root-distance-residual, with the original M_Z and C_R. The
right side is an actual nonnegative fast scalar PR2 name for
M_Z D_t(z)+2 C_R/2^E(t). A proved distance upper cut at its prescribed
sample precision, the sharp fixed-radius residual cut, and the exact
normalization budget give the order cut between the two actual names.
No represented minimizing root, desired residual law or order is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSharpDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRootAdequacy (inputContract)
open LeanProofs.IPRA.Analysis.GaussianRootSharpResidualSamples (M c)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (roots)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rhsData (step a : PR 3) (N Z t x : PTm n) : PTm n :=
  GaussianLinearDistanceName.nameData (roots step a N t x) x (M a N Z x) (two*c a N x) (GaussianRootSharpResidualSamples.D a N t x)
def rhsNumerator (step a : PR 3) (point : PR 2) (N Z t x j : PTm n) : PTm n :=
  GaussianLinearDistanceName.rawNumerator point (roots step a N t x) x (M a N Z x) (two*c a N x) (GaussianRootSharpResidualSamples.D a N t x)
    (GaussianLinearDistanceName.exponent (M a N Z x) j)
def rhsDenominator (step a : PR 3) (point : PR 2) (N Z t x j : PTm n) : PTm n :=
  GaussianLinearDistanceName.rawDenominator point (roots step a N t x) x (GaussianRootSharpResidualSamples.D a N t x)
    (GaussianLinearDistanceName.exponent (M a N Z x) j)

@[simp] theorem subst_rhsData {m : ℕ} (σ : Fin n → PTm m) (step a : PR 3) (N Z t x : PTm n) :
    Syn.subst σ (rhsData step a N Z t x) = rhsData step a (Syn.subst σ N) (Syn.subst σ Z) (Syn.subst σ t) (Syn.subst σ x) := by
  simp [rhsData]

/-- Canonical recoding of an actual canonical Gaussian value is literal
identity; this binds the generic residual name to the original P(z) program. -/
theorem recode_identity (z : PTm n) (hz : Γ ⊢[PRAAx] GaussianRationalHorner.canonical z) : Γ ⊢[PRAAx]
    GaussianFastValueCut.recode z ≐ z :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianFastValueCut.recode_canonical z) hz
    (GaussianRationalL1.raw_den_positive z) (GaussianFastValueCut.recode_represents z) (GaussianRationalL1.raw_represents z)

theorem polynomial_name_at (a : PR 3) (point : PR 2) (N Z x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianFastValueCut.nameF (GaussianRootSharpResidualSamples.observationF a point)) k
      (GaussianFastValueCut.nameData (GaussianRootApproximationWitness.T a N (Z+one) x) (GaussianRootSharpResidualSamples.data N x)) ≐
    ap2 (GaussianPolynomialValueName.nameF a point) k (GaussianPolynomialValueName.nameData N (Z+one) x) := by
  let L := GaussianRootApproximationWitness.T a N (Z+one) x
  have raw := GaussianRootSharpResidualSamples.observation_at (Γ := Γ) a point N x (GaussianFastValueCut.exponent L k)
  have r := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianFastValueCut.recode (var 0) : PTm 1)
    (σ := ![ap2 (GaussianRootSharpResidualSamples.observationF a point) (GaussianFastValueCut.exponent L k) (GaussianRootSharpResidualSamples.data N x)])
    (σ' := ![GaussianPolynomialValueName.observation a point N x (GaussianFastValueCut.exponent L k)])
    (fun j => by fin_cases j; exact raw)
  have values : Γ ⊢[PRAAx] GaussianFastValueCut.value (GaussianRootSharpResidualSamples.observationF a point) L
      (GaussianRootSharpResidualSamples.data N x) k ≐ GaussianFastValueCut.recode (GaussianPolynomialValueName.value a point N (Z+one) x k) := by
    simpa only [GaussianFastValueCut.value,GaussianFastValueCut.subst_recode,Syn.subst_var,Matrix.cons_val_zero,
      GaussianPolynomialValueName.value,GaussianPolynomialValueName.exponent,GaussianPolynomialValueName.normalizer,
      GaussianFastValueCut.exponent,GaussianFastValueCut.normalizer,L] using r
  exact (GaussianFastValueCut.name_at _ _ _ _).eqTrans (values.eqTrans
    ((recode_identity _ (GaussianPolynomialValueName.value_canonical a point N (Z+one) x k)).eqTrans
      (GaussianPolynomialValueName.name_at a point N (Z+one) x k).eqSymm))

theorem rhs_represents (step a : PR 3) (point : PR 2) (N Z t x j : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (ap2 (GaussianLinearDistanceName.nameF point) j (rhsData step a N Z t x))
      (ZT.ofNat (rhsNumerator step a point N Z t x j)) (rhsDenominator step a point N Z t x j) := by
  have dp := GaussianRootFiniteEvaluation.denominator_positive (Γ := Γ) a N t x
  have rep := GaussianLinearDistanceName.sample_represents point (roots step a N t x) x (M a N Z x) (two*c a N x) (GaussianRootSharpResidualSamples.D a N t x) j dp
  simpa only [rhsData,rhsNumerator,rhsDenominator] using GaussianRationalHorner.scalar_congr
    (GaussianLinearDistanceName.name_at point (roots step a N t x) x (M a N Z x) (two*c a N x) (GaussianRootSharpResidualSamples.D a N t x) j).eqSymm
    (by apply ZT.derive; rfl) (.eqRefl _) rep

theorem rhs_denominator_positive (step a : PR 3) (point : PR 2) (N Z t x j : PTm n) : Γ ⊢[PRAAx]
    le one (rhsDenominator step a point N Z t x j) :=
  GaussianLinearDistanceName.raw_denominator_positive _ _ _ _ _ (GaussianRootFiniteEvaluation.denominator_positive a N t x)

theorem order_at (step a : PR 3) (point : PR 2) (N Z t x k j : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianScalarOrderCut.normLE
      (ap2 (GaussianPolynomialValueName.nameF a point) k (GaussianPolynomialValueName.nameData N (Z+one) x))
      (GaussianScalarOrderCut.slackScalar (ap2 (GaussianLinearDistanceName.nameF point) j (rhsData step a N Z t x)) k j) := by
  let S := roots step a N t x
  let slope := M a N Z x
  let constant := two*c a N x
  let B := GaussianRootSharpResidualSamples.D a N t x
  let precision := GaussianLinearDistanceName.exponent slope j
  let nu := GaussianEuclideanDistanceUpperCut.numerator point S x precision
  let den := GaussianEuclideanDistanceUpperCut.denominator point S x precision
  let p := GaussianEuclideanDistanceUpperCut.upperNumerator point S x precision
  let q := GaussianEuclideanDistanceUpperCut.upperDenominator point S x precision
  have rd := Prf.andE₁ h
  have cn := Prf.andE₁ (Prf.andE₂ h)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have rz := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  have bp : Γ ⊢[PRAAx] le one B := GaussianRootFiniteEvaluation.denominator_positive a N t x
  have dp : Γ ⊢[PRAAx] le one den := GaussianEuclideanDistanceUpperCut.denominator_positive point S x precision
  have qp : Γ ⊢[PRAAx] le one q := GaussianEuclideanDistanceUpperCut.upper_denominator_positive point S x precision
  have sp : Γ ⊢[PRAAx] le one (length S) :=
    le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hn
  have upper := GaussianEuclideanDistanceUpperCut.sample_upper_cut point S x precision (Prf.andE₁ pointData) sp
  have cut := GaussianRootSharpResidualSamples.represented_residual_cut step a point N Z t x p q rd cn hn rz
    (Prf.andE₁ pointData) (Prf.andE₂ pointData) qp upper
  have query : Γ ⊢[PRAAx] bounded
      (ap2 (GaussianFastValueCut.nameF (GaussianRootSharpResidualSamples.observationF a point)) k
        (GaussianFastValueCut.nameData (GaussianRootApproximationWitness.T a N (Z+one) x) (GaussianRootSharpResidualSamples.data N x)))
      (GaussianRootSharpResidualSamples.baseNumerator a N Z t x p q*unit k+GaussianRootSharpResidualSamples.baseDenominator a N t x q)
      (GaussianRootSharpResidualSamples.baseDenominator a N t x q*unit k) := by
    simpa [GaussianFastValueCut.radiusCut] using cut.allE k
  have sampleBudget : Γ ⊢[PRAAx] le (slope*unit j) (unit precision) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans (GaussianLinearDistanceName.exponent_unit slope j).eqSymm)
      (mul_le_mul_right (unit j) (GaussianLinearDistanceName.normalizer_budget slope))
  have compare : Γ ⊢[PRAAx] le
      ((GaussianRootSharpResidualSamples.baseNumerator a N Z t x p q*unit k+GaussianRootSharpResidualSamples.baseDenominator a N t x q)*
        (rhsDenominator step a point N Z t x j*unit k*unit j))
      ((rhsNumerator step a point N Z t x j*unit k*unit j+rhsDenominator step a point N Z t x j*(unit j+unit k))*
        (GaussianRootSharpResidualSamples.baseDenominator a N t x q*unit k)) := by
    simpa only [p,q,S,slope,constant,B,precision,nu,den,
      GaussianRootSharpResidualSamples.baseNumerator,GaussianRootSharpResidualSamples.baseDenominator,
      rhsNumerator,rhsDenominator,GaussianLinearDistanceName.rawNumerator,GaussianLinearDistanceName.rawDenominator,
      GaussianEuclideanDistanceUpperCut.upperNumerator,GaussianEuclideanDistanceUpperCut.upperDenominator,
      GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
      GaussianRootDistanceOrderBudget.radius_budget slope nu den constant B (unit k) (unit precision) (unit j) sampleBudget
  have hBound := GaussianRationalReciprocal.bound_congr (polynomial_name_at a point N Z x k) (.eqRefl _) (.eqRefl _) query
  have finalBound := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ qp bp) (unit_positive k))
    (GaussianScalarOrderCut.slack_denominator_positive _ k j (rhs_denominator_positive step a point N Z t x j)) compare hBound
  exact GaussianScalarOrderCut.slack_normLE_from_bound _ _ _ _ k j
    (rhs_denominator_positive step a point N Z t x j) (rhs_represents step a point N Z t x j) finalBound

theorem sharp_distance_residual (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianScalarOrderCut.jointCut (GaussianPolynomialValueName.nameF a point) (GaussianLinearDistanceName.nameF point)
      (GaussianPolynomialValueName.nameData N (Z+one) x) (rhsData step a N Z t x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] inputContract step a point
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift Z)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianRootAdequacy.subst_inputContract,Syn.shift] using h.shift.shift
  simpa only [Syn.shift,subst_rhsData,GaussianPolynomialValueName.subst_nameData,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    order_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift Z)) (Syn.shift (Syn.shift t))
      (Syn.shift (Syn.shift x)) (var 1) (var 0) hs

theorem rhs_name_fast (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianLinearDistanceName.scalarCN (GaussianLinearDistanceName.nameF point) (rhsData step a N Z t x) := by
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))
  exact GaussianLinearDistanceName.name_fast point _ _ _ _ _ (Prf.andE₁ pointData)
    (le_congr (.eqRefl _) (GaussianRootRadius.roots_length step a N t x).eqSymm hn)
    (GaussianRootFiniteEvaluation.denominator_positive a N t x)

theorem root_distance_residual_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 3) ⟶
      GaussianScalarOrderCut.jointCut (GaussianPolynomialValueName.nameF a point) (GaussianLinearDistanceName.nameF point)
        (GaussianPolynomialValueName.nameData (var 0) (var 1+one) (var 3)) (rhsData step a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (sharp_distance_residual _ _ _ _ _ _ _ Prf.hyp0))

theorem root_residual_rhs_name_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 3) ⟶
      GaussianLinearDistanceName.scalarCN (GaussianLinearDistanceName.nameF point) (rhsData step a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (rhs_name_fast _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRootSharpDistance
