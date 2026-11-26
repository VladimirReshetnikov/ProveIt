import IPRADerivations.Analysis.SpecialFunctions.LambertW.GaussianRobinMeshLogDecomposition
import IPRADerivations.Analysis.Names.Scaling.GaussianNaturalScaleProductName
import IPRADerivations.Analysis.Inequalities.GaussianMeshLogSign
import IPRADerivations.Analysis.Gamma.GaussianGammaFunctionalEquation
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinIntegerExponential
import IPRADerivations.Analysis.Gamma.GaussianGammaNormalization

/-!
# Exponential of the original mesh logarithm from its binary components

The original binary exponent and the original reduced argument give
exact rational exponential values. Their product is the original
positive integer. Named negation gives the reciprocal needed by C20.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinMeshExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogInterval (eb Bt one_le_Bt dt st c3)
open GaussianRobinMeshLogDecomposition (baseData reducedData integerData integerF)
open GaussianRobinOddLogarithmName (inputs)
open GaussianRobinOddExponential (oddF constantF)
open GaussianGammaCanonicalExponent (constant_regular)
open GaussianGammaCanonicalExponent (source)
open GaussianRobinLogarithmParity (native)
open GaussianMeshLogSign (positiveIdentity positiveF positiveData)
open GaussianGammaFiniteApproximantName (logF log_regular exponential_input)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents qmul qmul_canonical ofGaussian_canonical qmul_represents
    canonical_unique represents_congr positive_product)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmRemainder (oneCode scale)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scaleF : PR 2 := GaussianNamedNaturalScale.nameF oddF
def scaleData (E : PTm n) : PTm n := GaussianNamedNaturalScale.data E E baseData
def scaleRadius (E : PTm n) : PTm n := GaussianNamedNaturalScale.radius E (num 3)
def baseScaleIdentity (E : PTm n) : Fm PTm n :=
  crossEquivalent (GaussianRadiusExponentialName.nameF scaleF) constantF
    (GaussianRadiusExponentialName.data (scaleRadius E) (scaleData E)) (naturalPoint (pw two E))

private theorem original_base_input :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input oddF (num 3) (baseData : PTm n) :=
  GaussianRobinOddExponential.odd_input one c3
    (.andI (le_of_eq_add (d := two) (by ipra_ring)) (le_of_eq_add (d := one) (by ipra_ring)))

theorem integer_exponential (N : PTm n) (hScale : Γ ⊢[PRAAx] baseScaleIdentity (eb N one)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF integerF) constantF
      (GaussianGammaFiniteApproximantName.exponentialInputData integerF (integerData N))
      (naturalPoint (pw two (eb N one))) := by
  let E := eb N one
  let T := GaussianNameBounds.U integerF (integerData N)
  have hbase := original_base_input (Γ := Γ)
  have si := GaussianNamedNaturalScale.exponential_input oddF E E (num 3) baseData hbase (le_refl E)
  have ki := exponential_input integerF (integerData N) (GaussianRobinMeshLogDecomposition.integer_regular (Γ := Γ) N)
  have eq := GaussianNaturalScaleProductName.scale_product_cross oddF E E (num 3) baseData hbase (le_refl E)
  have trans := GaussianExponentialRadiusIndependence.independent_radii_proper integerF scaleF T (scaleRadius E)
    (integerData N) (scaleData E) ki si (cross_symm _ _ _ _ eq)
  exact cross_trans _ _ _ _ _ _ trans hScale

theorem binary_product (N : PTm n) : Γ ⊢[PRAAx]
    qmul (naturalPoint (pw two (eb N one))) (GaussianRobinLogRangeReduction.quotient N (Bt N one)) ≐
      naturalPoint N := by
  let A := pw two (eb N one)
  let B := Bt N one
  let D := one*B
  have hB : Γ ⊢[PRAAx] le one B := one_le_Bt (a := N) (le_refl one)
  have hD := positive_product _ _ (le_refl one) hB
  have prod := qmul_represents (naturalPoint A) (ofGaussian (native N) B)
    (scale A oneCode) (native N) one B (le_refl one) hB
    (natural_point_represents A) (ofGaussian_represents _ _ hB)
  have target := rescale_to (naturalPoint N) (native N) one B D (natural_point_represents (Γ := Γ) N) (.eqRefl _)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (ComplexLogarithmRemainder.mul (scale A oneCode) (native N)) (scale B (native N)) := by
    have id := natEq (one_mul (Γ := Γ) A)
    apply GaussianRootAlgebra.equal_of_values
    · simp only [native,GaussianRootAlgebra.re_mul,GaussianRootAlgebra.re_scale,
        GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
      have hId : Groth.ι (LeanProofs.IPRA.Q.mk Γ B) = Groth.ι (LeanProofs.IPRA.Q.mk Γ A) := id
      rw [hId]
      ring
    · simp only [native,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
      ring
  exact canonical_unique _ _ _ _ (qmul_canonical _ _) (ofGaussian_canonical _ _ (le_refl one)) hD
    (represents_congr (.eqRefl _) same (.eqRefl _) prod) target

theorem original_positive_mesh_exponential (N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hScale : Γ ⊢[PRAAx] baseScaleIdentity (eb N one)) : Γ ⊢[PRAAx] positiveIdentity N := by
  let E := eb N one
  let T := GaussianNameBounds.U integerF (integerData N)
  let S := GaussianNameBounds.U logF N
  let G := GaussianRadiusExponentialName.nameF integerF
  let H := GaussianRadiusExponentialName.nameF oddF
  let x := GaussianRadiusExponentialName.data T (integerData N)
  let y := GaussianRadiusExponentialName.data (num 3) (reducedData N)
  let a := naturalPoint (pw two E)
  let b := GaussianRobinLogRangeReduction.quotient N (Bt N one)
  have ki := exponential_input integerF (integerData N) (GaussianRobinMeshLogDecomposition.integer_regular (Γ := Γ) N)
  have ri := GaussianRobinOddExponential.odd_input (dt N one) (st N one)
    (GaussianRobinLogRangeReduction.reduced_source N one (le_refl _) hN)
  have li := exponential_input logF N (log_regular N hN)
  have law := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent integerF oddF logF
    T (num 3) S (integerData N) (reducedData N) N ki ri li
    (GaussianRobinMeshLogDecomposition.original_mesh_decomposition N hN)
  have gx : Γ ⊢[PRAAx] pointCN G x := GaussianRadiusExponentialName.name_regular _ _ _ ki
  have hy : Γ ⊢[PRAAx] pointCN H y := GaussianRadiusExponentialName.name_regular _ _ _ ri
  have rep := GaussianGammaAdjacentCutoff.multiply_cross G constantF H constantF x a y b gx (constant_regular a)
    hy (constant_regular b) (integer_exponential N hScale)
    (GaussianRobinLogRangeReduction.original_binary_component N one (le_refl _) hN)
  have final := GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (binary_product (Γ := Γ) N)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ law) (cross_trans _ _ _ _ _ _ rep
    (cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross a b) final))

theorem original_negative_mesh_exponential (N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hScale : Γ ⊢[PRAAx] baseScaleIdentity (eb N one)) :
    Γ ⊢[PRAAx] GaussianGammaEulerShiftLimit.logInverse N :=
  GaussianMeshLogSign.negative_mesh_reciprocal N hN (original_positive_mesh_exponential N hN hScale)

theorem mesh_exponential (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] positiveIdentity N :=
  original_positive_mesh_exponential N hN
    (GaussianRobinIntegerExponential.original_Robin_integer_scaled_exponential (eb N one))

theorem mesh_exponential_inverse (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] GaussianGammaEulerShiftLimit.logInverse N :=
  GaussianMeshLogSign.negative_mesh_reciprocal N hN (mesh_exponential N hN)

theorem all_mesh_exponential_inverses : Γ ⊢[PRAAx] GaussianGammaFunctionalEquation.allLogInverse :=
  .allI (.impI (mesh_exponential_inverse (var 0) Prf.hyp0))

theorem C20_shift (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] crossEquivalent GaussianGammaFunctionalEquation.leftLimitF GaussianGammaC7Name.nameF
      (GaussianGammaFunctionalEquation.leftLimitData z R B) (GaussianGammaC7Name.data z R B) :=
  GaussianGammaFunctionalEquation.original_C20_shift z R B h all_mesh_exponential_inverses

theorem C20_P_one : Γ ⊢[PRAAx] crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
    (GaussianGammaC7Name.data (oneCode : PTm n) one one) zero :=
  GaussianGammaNormalization.original_P_one all_mesh_exponential_inverses

theorem C21_Gamma_one : Γ ⊢[PRAAx] crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF
    (GaussianGammaReciprocalInverse.gammaData (oneCode : PTm n) one one one) zero :=
  GaussianGammaNormalization.original_Gamma_one all_mesh_exponential_inverses

theorem original_positive_mesh_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (le one (var 0) ⟶ positiveIdentity (var 0)) :=
  closeUniv 1 (.impI (mesh_exponential _ Prf.hyp0))

theorem original_mesh_exponential_inverse_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    GaussianGammaFunctionalEquation.allLogInverse :=
  all_mesh_exponential_inverses

theorem original_C20_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶
      crossEquivalent GaussianGammaFunctionalEquation.leftLimitF GaussianGammaC7Name.nameF
        (GaussianGammaFunctionalEquation.leftLimitData (var 0) (var 1) (var 2))
        (GaussianGammaC7Name.data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (C20_shift _ _ _ Prf.hyp0))

theorem original_C20_P_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
      (GaussianGammaC7Name.data oneCode one one) zero :=
  C20_P_one

theorem original_C21_Gamma_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF
      (GaussianGammaReciprocalInverse.gammaData oneCode one one one) zero :=
  C21_Gamma_one

end LeanProofs.IPRA.Analysis.GaussianRobinMeshExponential
