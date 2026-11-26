import IPRADerivations.Analysis.Euler.Integration.Parts.GaussianEulerIntegrationByPartsRecurrence
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNamedReference
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianEulerNamedShiftInput

/-!
# Euler integration by parts on regular right-half-plane names

Both named Gamma programs keep their actual computations. A matched late
pair of native fractions is used only to apply the encoded Euler recurrence.
The original product's observation clock is included in the comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerNamedIBPRecurrence

open_ipra
open GaussianNamedRightHalfPlane (source radius numerator denominator threshold)
open GaussianEulerNamedShiftInput (shiftF shiftData clock)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaHalfPlaneInputContinuity (modulus)
open GaussianNamedGamma (nameF data name_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerIntegrationByPartsDomain (gammaProductF gammaProductData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianExponentialReference (unit_monotone)
open GaussianNamedInverseRate (rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev productF (f : PR 2) : PR 2 := multiplyF f (nameF f)
def productData (f : PR 2) (x A : PTm n) : PTm n := multiplyData f (nameF f) x (data x A)

ipra_subst productData

private theorem named_to_encoded (f : PR 2) (p q t r x A R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f t r x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) (hp : Γ ⊢[PRAAx] le t p) (hq : Γ ⊢[PRAAx] le t q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x A))
      (ap2 gammaF q (GaussianEulerVerticalNamedRadius.encodedData f r x A R)) (num 3) (unit t) := by
  have up := unit_monotone hp
  have uq := unit_monotone hq
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive t)) (unit_positive t)
    (by unfold rateNumerator rateDenominator; ipra_le (𝔞(unit t)*𝔞(unit q))*sl up+(𝔞(unit t)*𝔞(unit p))*sl uq)
    (GaussianEulerVerticalNamedRadius.original_observations f p q t r x A R h hR)

private theorem observations_to_dyadic {u v : PTm n} (p q t : PTm n)
    (hp : Γ ⊢[PRAAx] le t p) (hq : Γ ⊢[PRAAx] le t q)
    (h : Γ ⊢[PRAAx] distanceBounded u v (unit p+unit q) (unit p*unit q)) :
    Γ ⊢[PRAAx] distanceBounded u v two (unit t) := by
  have up := unit_monotone hp
  have uq := unit_monotone hq
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
    (by ipra_le 𝔞(unit q)*sl up+𝔞(unit p)*sl uq) h

private theorem input_recode_dyadic (f : PR 2) (p r t x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x)
    (hp : Γ ⊢[PRAAx] le t p) (hr : Γ ⊢[PRAAx] le t r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ofGaussian (numerator f r x) (denominator f r x)) two (unit t) := by
  have hu := unit_positive (Γ := Γ) t
  have samples := observations_to_dyadic p r t hp hr (point_at f x p r h)
  have recoded := distance_symmetric _ _ _ _ (le_refl one)
    (GaussianFastValueCut.recode_distance (Γ := Γ) (ap2 f r x))
  have rec' := distance_radius_mono _ _ zero one zero (unit t) (le_refl one) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) recoded
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu samples rec')

private def productRadius (f : PR 2) (x A R : PTm n) : PTm n :=
  two*GaussianNameBounds.U (nameF f) (data x A)+R*num 3

private theorem named_product_to_encoded (f : PR 2) (t r x A R : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f t r x A)
    (hR : Γ ⊢[PRAAx] le (radius f x) R) (hr : Γ ⊢[PRAAx] le t r) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (productF f) t (productData f x A))
      (ap2 gammaProductF t (gammaProductData (numerator f r x) R (denominator f r x) (two*A)))
      (productRadius f x A R) (unit t) := by
  let z := numerator f r x
  let B := denominator f r x
  let c := ofGaussian z B
  let e := gammaData z R B (two*A)
  let y := data x A
  let s := productClock f (nameF f) x y t
  let v := productClock GaussianGammaCanonicalExponent.constantF gammaF c e t
  have hs : Γ ⊢[PRAAx] le t s := le_add_right _ _
  have hv : Γ ⊢[PRAAx] le t v := le_add_right _ _
  have encoded := GaussianEulerVerticalNamedRadius.source_enlarge _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source f t r x A h) hR
  have hc := GaussianEulerIntegrationByPartsDomain.original_input_bound z R B (two*A) encoded
  have hu := GaussianNameBounds.sample_bound (nameF f) y s (name_regular f x A h.andE₁)
  have first := input_recode_dyadic f s r t x h.andE₁.andE₁ hs hr
  have second := named_to_encoded f s v t r x A R h hR hs hv
  have lhs := product_at (Γ := Γ) f (nameF f) x y t
  have rhs := (product_at (Γ := Γ) GaussianGammaCanonicalExponent.constantF gammaF c e t).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (GaussianGammaCanonicalExponent.constant_at v c) (.eqRefl _))
  exact distance_congr lhs.eqSymm rhs.eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameArithmetic.product_distance _ _ _ _ two (num 3) (unit t) _ R (unit_positive t) first second hu hc)

private def sharedRadius (f : PR 2) (x : PTm n) : PTm n :=
  radius f x+radius (shiftF f) (shiftData x)
private def diagonalRadius (f : PR 2) (x A : PTm n) : PTm n := productRadius f x A (sharedRadius f x)+num 7

private theorem subst_diagonalRadius {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x A : PTm n) :
    Syn.subst σ (diagonalRadius f x A) = diagonalRadius f (Syn.subst σ x) (Syn.subst σ A) := by
  simp only [diagonalRadius, sharedRadius, productRadius, GaussianNamedGamma.subst_data,
    GaussianEulerNamedShiftInput.subst_shiftData, GaussianNamedRightHalfPlane.subst_radius,
    GaussianNameBounds.subst_U, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, LeanProofs.IPRA.PTm.subst_num]

theorem original_named_Gamma_diagonal (f : PR 2) (t x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (shiftF f)) t (data (shiftData x) A))
      (ap2 (productF f) t (productData f x A)) (diagonalRadius f x A) (unit t) := by
  let g := shiftF f
  let y := shiftData x
  let R := sharedRadius f x
  let S := R+one
  let D := succ (modulus t (radius f x) (two*A))
  let E := succ (modulus t (radius g y) (two*A))
  let r := t+threshold A+D+E
  let s := clock r
  let z := numerator f s x
  let B := denominator f s x
  let w := numerator g r y
  let C := denominator g r y
  let H := two*A
  let P := ap2 (nameF g) t (data y A)
  let X := ap2 gammaF t (gammaData w S C H)
  let Y := ap2 gammaF t (gammaData (shifted z B) S B H)
  let Z := ap2 gammaProductF t (gammaProductData z R B H)
  let Q := ap2 (productF f) t (productData f x A)
  have ht : Γ ⊢[PRAAx] le t r := le_trans (le_trans (le_add_right _ _) (le_add_right _ _)) (le_add_right _ _)
  have hs := GaussianEulerNamedShiftInput.clock_later (Γ := Γ) r
  have hm : Γ ⊢[PRAAx] le (threshold A) r := le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (le_add_right _ _)
  have hf : Γ ⊢[PRAAx] le D r := le_trans (le_add_left _ _) (le_add_right _ _)
  have hg : Γ ⊢[PRAAx] le E r := le_add_left _ _
  have hR : Γ ⊢[PRAAx] le (radius f x) R := le_add_right _ _
  have hS : Γ ⊢[PRAAx] le (radius g y) S := le_trans (le_add_left _ _) (le_add_right _ _)
  have old : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f t s x A :=
    .andI h (.andI (le_trans hm hs) (le_trans hf hs))
  have new : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input g t r y A :=
    .andI (GaussianEulerNamedShiftInput.original_source f x A h) (.andI hm hg)
  have before := GaussianEulerVerticalNamedRadius.source_enlarge _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source f t s x A old) hR
  have afterShift := (GaussianEulerIntegrationByPartsDomain.common_sources z R B H before).andE₂
  have afterDecode := GaussianEulerVerticalNamedRadius.source_enlarge _ _ _ _ _
    (GaussianNamedGammaLateInput.encoded_source g t r y A new) hS
  have start : Γ ⊢[PRAAx] distanceBounded P X (num 3) (unit t) :=
    named_to_encoded g t t t r y A S new hS (le_refl _) (le_refl _)
  have same : Γ ⊢[PRAAx] distanceBounded X Y two (unit t) :=
    observations_to_dyadic t t t (le_refl _) (le_refl _)
      (GaussianEulerVerticalNamedReference.equal_fraction_observations t t w (shifted z B) S C B H
        afterDecode afterShift (GaussianEulerNamedShiftInput.decoded_shift f r x))
  have middle : Γ ⊢[PRAAx] distanceBounded Y Z two (unit t) :=
    observations_to_dyadic t t t (le_refl _) (le_refl _)
      (cross_at _ _ _ _ t t (GaussianEulerIntegrationByPartsRecurrence.original_Gamma_IBP_recurrence z R B H before))
  have hu := unit_positive (Γ := Γ) t
  have last : Γ ⊢[PRAAx] distanceBounded Z Q (productRadius f x A R) (unit t) :=
    distance_symmetric _ _ _ _ hu (named_product_to_encoded f t s x A R old hR (le_trans ht hs))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalRadius; dsimp only [R]; ipra_ring) (.eqRefl _)
    (distance_triangle_same P X Q (num 3) (two+(two+productRadius f x A R)) (unit t) hu start
      (distance_triangle_same X Y Q two (two+productRadius f x A R) (unit t) hu same
        (distance_triangle_same Y Z Q two (productRadius f x A R) (unit t) hu middle last)))

theorem original_named_Gamma_IBP_recurrence (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (shiftF f)) (productF f) (data (shiftData x) A) (productData f x A) := by
  have left := name_regular _ _ _ (GaussianEulerNamedShiftInput.original_source f x A h)
  have right := GaussianNameArithmetic.multiply_fast f (nameF f) x (data x A) h.andE₁ (name_regular f x A h)
  apply GaussianNameRingLaws.equivalent_of_envelope (nameF (shiftF f)) (productF f)
    (data (shiftData x) A) (productData f x A) (diagonalRadius f x A) left right
  unfold GaussianValueNormalizerExtensionality.rawDiagonal
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) := by
    simpa only [Fm.shift, Syn.shift, GaussianNamedRightHalfPlane.subst_source] using h.shift
  simp only [Syn.shift, subst_diagonalRadius,
    GaussianNamedGamma.subst_data, subst_productData, GaussianEulerNamedShiftInput.subst_shiftData]
  exact original_named_Gamma_diagonal f (var 0) (Syn.shift x) (Syn.shift A) hs

theorem actual_original_named_Gamma_IBP_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶
        crossEquivalent (nameF (shiftF f)) (productF f) (data (shiftData (var 0)) (var 1)) (productData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_named_Gamma_IBP_recurrence f _ _ Prf.hyp0))

theorem actual_original_named_Gamma_IBP_independent_queries_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 2) (var 3) ⟶
        distanceBounded (ap2 (nameF (shiftF f)) (var 0) (data (shiftData (var 2)) (var 3)))
          (ap2 (productF f) (var 1) (productData f (var 2) (var 3)))
          (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 4 (.impI (cross_at _ _ _ _ _ _ (original_named_Gamma_IBP_recurrence f _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerNamedIBPRecurrence
