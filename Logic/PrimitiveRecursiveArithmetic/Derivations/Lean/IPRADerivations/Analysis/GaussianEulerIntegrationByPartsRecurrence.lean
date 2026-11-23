import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsCofinalGrid
import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsDomain
import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsEndpointBudget
import IPRADerivations.Analysis.GaussianEulerIntegrationByPartsNormalizedGrid

/-!
# Euler integration by parts on the original Gamma names

The unshifted and shifted Euler integrands use the same positive cutoff
and the same refined grid. The endpoint bounds and the finite telescope
control the grid residual. Readback to the two actual improper names
then gives the recurrence, and the original Euler integral identification
transfers it to the original reciprocal Gamma programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source subst_source improper_source original_Euler_integral_is_Gamma)
open GaussianEulerIntegrationByPartsDomain (productF productData gammaProductF gammaProductData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerCutoffCauchyComparison (observation)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCompactRiemannName (quadrature)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def originalGrid (p t q z R B k A : PTm n) : PTm n :=
  quadrature evaluatorF p (GaussianEulerIntegrationByPartsCofinalGrid.cells t q k A R)
    one (width k A R) (etaDen k A R) (fixedData z B)

private theorem grid_to_cutoff (p t z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A)
    (hp : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsCofinalGrid.minimumObservation t (succ t) k A R) p) :
    Γ ⊢[PRAAx] distanceBounded (originalGrid p t (succ t) z R B k A) (observation (succ t) z R B k A) one (unit t) := by
  have later : Γ ⊢[PRAAx] le (t+num 6) (succ t+num 6) := add_le_add_right _ (le_succ_self t)
  have budget := le_trans (GaussianEulerLowerCofinalQuadrature.three_slack (Γ := Γ) t)
    (GaussianExponentialReference.unit_monotone later)
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive t)
    (le_congr (.eqRefl _) (one_mul _).eqSymm budget)
    (GaussianEulerIntegrationByPartsCofinalGrid.original_refined_euler_observations p t (succ t) z R B k A
      h.andE₁.andE₂.andE₁ hp)

private theorem compare_original_integral_queries (p t z R B A k : PTm n)
    (h : Γ ⊢[PRAAx] source z R B A) (hShift : Γ ⊢[PRAAx] source (shifted z B) R B A)
    (hk : Γ ⊢[PRAAx] le t k)
    (hp : Γ ⊢[PRAAx] le (GaussianEulerIntegrationByPartsCofinalGrid.minimumObservation t (succ t) k A R) p)
    (hGrid : Γ ⊢[PRAAx] distanceBounded (qmul (ofGaussian z B) (originalGrid p t (succ t) z R B k A))
      (originalGrid p t (succ t) (shifted z B) R B k A) (num 5) (unit t)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF t (productData z R B A))
      (ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data (shifted z B) R B A))
      (num 3*R+num 8) (unit t) := by
  let U := unit t
  let c := ofGaussian z B
  let P := ap2 productF t (productData z R B A)
  let X := qmul c (observation (succ t) z R B k A)
  let Y := qmul c (originalGrid p t (succ t) z R B k A)
  let Z := originalGrid p t (succ t) (shifted z B) R B k A
  let W := observation (succ t) (shifted z B) R B k A
  let I := ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data (shifted z B) R B A)
  have hu := unit_positive (Γ := Γ) t
  have first : Γ ⊢[PRAAx] distanceBounded P X (two*R) U :=
    GaussianEulerIntegrationByPartsDomain.original_product_to_fixed_cutoff t (succ t) k z R B A h hk (le_refl _)
  have second : Γ ⊢[PRAAx] distanceBounded X Y R U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance c _ _ R one U hu
        (GaussianEulerIntegrationByPartsDomain.original_input_bound z R B A h)
        (distance_symmetric _ _ _ _ hu (grid_to_cutoff p t z R B k A h hp)))
  have fourth : Γ ⊢[PRAAx] distanceBounded Z W one U := grid_to_cutoff p t (shifted z B) R B k A hShift hp
  have last : Γ ⊢[PRAAx] distanceBounded W I two U := distance_symmetric _ _ _ _ hu
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianEulerLaterCutoffObservation.later_cutoff_observations t (succ t) t (shifted z B) R B A k
        (improper_source _ _ _ _ hShift) hk (le_refl _)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same P X I (two*R) (R+(num 5+(one+two))) U hu first
      (distance_triangle_same X Y I R (num 5+(one+two)) U hu second
        (distance_triangle_same Y Z I (num 5) (one+two) U hu hGrid
          (distance_triangle_same Z W I one two U hu fourth last))))

private def diagonalRadius (R : PTm n) : PTm n := num 3*(R+one)+num 8

theorem original_integral_diagonal_recurrence (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF t (productData z (R+one) B A))
      (ap2 GaussianEulerImproperName.nameF t (GaussianEulerImproperName.data (shifted z B) (R+one) B A))
      (diagonalRadius R) (unit t) := by
  let S := R+one
  let q := succ t
  let k := GaussianEulerIntegrationByPartsEndpointBudget.cutoff t S
  let C := width k A S
  let E := etaDen k A S
  let T := top k A S
  let N := GaussianEulerIntegrationByPartsCofinalGrid.cells t q k A S
  let P₀ := GaussianEulerIntegrationByPartsCofinalGrid.minimumObservation t q k A S
  let P₁ := GaussianEulerIntegrationByPartsEndpointBudget.minimumObservation t k A S
  let P₂ := GaussianFastValueCut.exponent (T*GaussianEulerIntegrationByPartsNormalizedGrid.cost S E T) t
  let p := P₀+P₁+P₂
  have both := GaussianEulerIntegrationByPartsDomain.common_sources z R B A h
  have hDisk := both.andE₁.andE₁.andE₂.andE₁
  have c0 : Γ ⊢[PRAAx] le P₀ p := le_trans (le_add_right _ _) (le_add_right _ _)
  have c1 : Γ ⊢[PRAAx] le P₁ p := le_trans (le_add_left _ _) (le_add_right _ _)
  have c2 : Γ ⊢[PRAAx] le P₂ p := le_add_left _ _
  have hk : Γ ⊢[PRAAx] le t k :=
    le_trans (le_succ_self t) (GaussianEulerIntegrationByPartsEndpointBudget.cutoff_later t S)
  have gridSource := GaussianEulerIntegrationByPartsCofinalGrid.original_grid_source t q z S B k A hDisk
  have hN := GaussianEulerIntegrationByPartsCofinalGrid.cells_positive (Γ := Γ) t q k A S
  have raw := GaussianEulerIntegrationByPartsCofinalGrid.original_finite_error p t q z S B k A hDisk c0
  have ends := GaussianEulerIntegrationByPartsEndpointBudget.original_affine_boundary_difference_small t p z S B k A N
    both.andE₁.andE₁ hN (le_refl _) c1
  let right := GaussianEulerIntegrationByPartsGrid.endpoint N p z B one C E N
  let left := GaussianEulerIntegrationByPartsGrid.endpoint zero p z B one C E N
  have endEq : Γ ⊢[PRAAx] left ≐ GaussianEulerIntegrationByPartsLinear.primitive p z B (one*N) (E*N) :=
    GaussianEulerIntegrationByPartsGrid.primitive_numerator_congr _ _ _ _ _ _ (by ipra_ring)
  have boundary : Γ ⊢[PRAAx] bounded (qsub right left) two (unit t) :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl right) endEq).eqSymm (.eqRefl _) (.eqRefl _) ends
  have grid := GaussianEulerIntegrationByPartsNormalizedGrid.original_product_shift_error t p N z S B one C E T
    gridSource.andE₁ hN c2 (distance_symmetric _ _ _ _ (unit_positive t) raw) boundary
  exact compare_original_integral_queries p t z S B A k both.andE₁ both.andE₂ hk c0 grid

private theorem improper_recurrence_from_diagonal (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (diag : Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal productF GaussianEulerImproperName.nameF
      (productData z (R+one) B A) (GaussianEulerImproperName.data (shifted z B) (R+one) B A) (diagonalRadius R)) :
    Γ ⊢[PRAAx] crossEquivalent productF GaussianEulerImproperName.nameF
      (productData z (R+one) B A) (GaussianEulerImproperName.data (shifted z B) (R+one) B A) := by
  let S := R+one
  let c := ofGaussian z B
  have both := GaussianEulerIntegrationByPartsDomain.common_sources z R B A h
  have hI := GaussianEulerImproperName.name_regular z S B A (improper_source z S B A both.andE₁)
  have hShift := GaussianEulerImproperName.name_regular (shifted z B) S B A
    (improper_source (shifted z B) S B A both.andE₂)
  have hP := GaussianNameArithmetic.multiply_fast GaussianGammaCanonicalExponent.constantF GaussianEulerImproperName.nameF
    c (GaussianEulerImproperName.data z S B A) (GaussianGammaCanonicalExponent.constant_regular (Γ := Γ) c) hI
  exact GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (diagonalRadius R) hP hShift diag

private theorem gamma_recurrence_from_improper (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hI : Γ ⊢[PRAAx] crossEquivalent productF GaussianEulerImproperName.nameF
      (productData z (R+one) B A) (GaussianEulerImproperName.data (shifted z B) (R+one) B A)) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaProductF
      (gammaData (shifted z B) (R+one) B A) (gammaProductData z R B A) := by
  have hShift := (GaussianEulerIntegrationByPartsDomain.common_sources z R B A h).andE₂
  have toGamma := original_Euler_integral_is_Gamma (shifted z B) (R+one) B A hShift
  have fromGamma := GaussianEulerIntegrationByPartsDomain.original_product_overlap z R B A h
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ fromGamma (cross_trans _ _ _ _ _ _ hI toGamma))

theorem original_improper_Euler_IBP_recurrence (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent productF GaussianEulerImproperName.nameF
      (productData z (R+one) B A) (GaussianEulerImproperName.data (shifted z B) (R+one) B A) := by
  apply improper_recurrence_from_diagonal z R B A h
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) := by
    simpa only [Fm.shift, Syn.shift, subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, diagonalRadius, Syn.shift,
    GaussianEulerIntegrationByPartsDomain.subst_productData, GaussianEulerImproperName.subst_data,
    GaussianGammaEulerHeadShift.subst_shifted, PTm.subst_add, PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    LeanProofs.IPRA.PTm.subst_num] using
      original_integral_diagonal_recurrence (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) hs

theorem original_Gamma_IBP_recurrence (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaProductF
      (gammaData (shifted z B) (R+one) B A) (gammaProductData z R B A) :=
  gamma_recurrence_from_improper z R B A h (original_improper_Euler_IBP_recurrence z R B A h)

theorem actual_original_improper_Euler_IBP_recurrence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶
        crossEquivalent productF GaussianEulerImproperName.nameF
          (productData (var 0) (var 1+one) (var 2) (var 3))
          (GaussianEulerImproperName.data (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_improper_Euler_IBP_recurrence _ _ _ _ Prf.hyp0))

theorem actual_original_Gamma_IBP_recurrence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶
        crossEquivalent gammaF gammaProductF
          (gammaData (shifted (var 0) (var 2)) (var 1+one) (var 2) (var 3))
          (gammaProductData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_Gamma_IBP_recurrence _ _ _ _ Prf.hyp0))

theorem actual_original_Gamma_IBP_recurrence_independent_queries_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 2) (var 3) (var 4) (var 5) ⟶
        distanceBounded
          (ap2 gammaF (var 0) (gammaData (shifted (var 2) (var 4)) (var 3+one) (var 4) (var 5)))
          (ap2 gammaProductF (var 1) (gammaProductData (var 2) (var 3) (var 4) (var 5)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (cross_at _ _ _ _ _ _ (original_Gamma_IBP_recurrence _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsRecurrence
