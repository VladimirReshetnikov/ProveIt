import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedMajorantExponent
import IPRADerivations.Analysis.Gamma.GaussianGammaFoldedApproximantBalance
import IPRADerivations.Analysis.Gamma.GaussianGammaCutoffIndependence
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse

/-!
# The exact C9 majorant of the original folded finite P_N

Original C8 and actual exponential inversion are used only by
multiplication, including at zeros of the polynomial head. The original
P_N name is identified with the checked exactly bounded representative
head_(2R) exp(E_(2R)-T_N). The original observations retain their normal
dyadic error; no exact disk is falsely asserted for those observations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFoldedC9Bound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFoldedMajorantExponent (input majorant majorantF majorantData correctedF correctedData)
open GaussianGammaFiniteApproximantName (pF pData p_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular exponentF exponentialF exponentData exponentialData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent diagonalEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameRingLaws (negativeF negativeData oneF one_fast one_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

@[simp] theorem subst_pData {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (pData z B N) = pData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  change Syn.subst σ (multiplyData constantF (GaussianRadiusExponentialName.nameF GaussianGammaCanonicalExponent.productF)
    (GaussianGammaCutoffName.head z B N)
    (GaussianRadiusExponentialName.data (GaussianNameBounds.U GaussianGammaCanonicalExponent.productF
      (GaussianGammaCanonicalExponent.productData z B N)) (GaussianGammaCanonicalExponent.productData z B N))) =
    multiplyData constantF (GaussianRadiusExponentialName.nameF GaussianGammaCanonicalExponent.productF)
      (GaussianGammaCutoffName.head (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N))
      (GaussianRadiusExponentialName.data (GaussianNameBounds.U GaussianGammaCanonicalExponent.productF
        (GaussianGammaCanonicalExponent.productData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N)))
        (GaussianGammaCanonicalExponent.productData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N)))
  simp only [GaussianNameArithmetic.subst_multiplyData,GaussianGammaCutoffName.subst_head,
    GaussianRadiusExponentialName.subst_data,GaussianNameBounds.subst_U,GaussianGammaCanonicalExponent.subst_productData]

theorem one_any_data (x y : PTm n) : Γ ⊢[PRAAx] crossEquivalent oneF oneF x y := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _ (one_fast x) (one_fast y) (.allI ?_)
  have e := distance_radius_mono (Γ := Γ.map Fm.shift) _ _ zero (unit (var 0)) two (unit (var 0))
    (unit_positive _) (unit_positive _) (le_of_eq_add (d := two*unit (var 0)) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero (GaussianRationalSyntheticDivision.qone : PTm (n+1))
      (unit (var 0)) (unit_positive _))
  simpa only [diagonalEquivalent,Syn.shift] using
    distance_congr (one_at (var 0) (Syn.shift x)).eqSymm (one_at (var 0) (Syn.shift y)).eqSymm
      (.eqRefl _) (.eqRefl _) e

def tailData (z R B N : PTm n) : PTm n := GaussianGammaCanonicalTailName.data z R B N
def tailRadius (z R B N : PTm n) : PTm n := GaussianNameBounds.U GaussianGammaCanonicalTailName.pointF (tailData z R B N)
def negativeExpF : PR 2 := GaussianRadiusExponentialName.nameF (negativeF GaussianGammaCanonicalTailName.pointF)
def negativeExpData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data
  (tailRadius z R B N) (negativeData (tailData z R B N))
def withdrawalF : PR 2 := multiplyF GaussianGammaC7Name.nameF negativeExpF
def withdrawalData (z R B N : PTm n) : PTm n := multiplyData GaussianGammaC7Name.nameF negativeExpF
  (GaussianGammaC7Name.data z R B) (negativeExpData z R B N)
@[simp] theorem subst_tailData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (tailData z R B N) = tailData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [tailData]
@[simp] theorem subst_tailRadius {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (tailRadius z R B N) = tailRadius (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [tailRadius]
@[simp] theorem subst_negativeExpData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (negativeExpData z R B N) = negativeExpData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [negativeExpData]
@[simp] theorem subst_withdrawalData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (withdrawalData z R B N) = withdrawalData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [withdrawalData]

theorem tail_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input GaussianGammaCanonicalTailName.pointF (tailRadius z R B N) (tailData z R B N) :=
  GaussianGammaFiniteApproximantName.exponential_input _ _
    (GaussianGammaCanonicalTailName.name_regular z R B N (GaussianGammaFoldedMajorantExponent.tail_source z R B N h))
theorem negative_exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN negativeExpF (negativeExpData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianExponentialInverse.negative_input _ _ _ (tail_input z R B N h))

/-- Original folded C8 followed by the actual inverse product, entirely
by multiplication. No cancellation by a possibly zero head occurs. -/
theorem withdrawal_is_original_P (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent withdrawalF pF (withdrawalData z R B N) (pData z B N) := by
  let T := GaussianGammaCanonicalTailName.pointF
  let X := tailData z R B N
  let R' := tailRadius z R B N
  let E := GaussianGammaFoldedApproximantBalance.tailExpF
  let Z := GaussianGammaFoldedApproximantBalance.tailExpData z R B N
  let Y := negativeExpData z R B N
  let P := pData z B N
  have hi := tail_input z R B N h
  have cnT := GaussianRadiusExponentialName.name_regular T R' X hi
  have cnNeg := negative_exponential_regular z R B N h
  have cnP := p_regular (Γ := Γ) z B N
  have cnC7 := GaussianGammaC7Name.name_regular z R B h.andE₁
  have boundC8 := cross_trans _ _ _ _ _ _
    (GaussianGammaCutoffIndependence.original_C7_cutoff_equivalent z R B N h.andE₁ h.andE₂)
    (GaussianGammaFoldedApproximantBalance.tail_factor_identity z R B N
      (GaussianGammaFoldedMajorantExponent.tail_source z R B N h))
  have first := multiply_cross GaussianGammaC7Name.nameF (multiplyF pF E) negativeExpF negativeExpF _ _ Y Y
    cnC7 (multiply_fast pF E P Z cnP cnT) cnNeg cnNeg boundC8 (cross_refl _ _ cnNeg)
  have associate := GaussianNameRingLaws.multiply_associative pF E negativeExpF P Z Y cnP cnT cnNeg
  have inverse := cross_trans _ _ _ _ _ _ (GaussianExponentialInverse.exponential_inverse T R' X hi) (one_any_data X P)
  have second := multiply_cross pF pF (GaussianExponentialInverse.productF T) oneF P P _ P
    cnP cnP (GaussianExponentialInverse.product_regular T R' X hi) (one_fast P) (cross_refl pF P cnP) inverse
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ associate
    (cross_trans _ _ _ _ _ _ second (GaussianNameRingLaws.multiply_one pF P cnP)))

/-- The same withdrawal equals the actual corrected exponent constructor
whose observations have already been proved bounded by M_R. -/
theorem withdrawal_is_bounded_representative (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent withdrawalF majorantF (withdrawalData z R B N) (majorantData z R B N) := by
  let H := GaussianGammaEulerHead.run z B (two*R)
  let X := exponentialData z R B
  let Y := negativeExpData z R B N
  let G := negativeF GaussianGammaCanonicalTailName.pointF
  let R' := tailRadius z R B N
  have old := GaussianGammaCanonicalExponent.exponential_input z R B h.andE₁
  have negInput := GaussianExponentialInverse.negative_input _ _ _ (tail_input z R B N h)
  have cnE := GaussianGammaCanonicalExponent.exponential_regular z R B h.andE₁
  have cnNeg := negative_exponential_regular z R B N h
  have cnH := constant_regular (Γ := Γ) H
  have associate := GaussianNameRingLaws.multiply_associative constantF exponentialF negativeExpF H X Y cnH cnE cnNeg
  have expProduct := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent exponentF G correctedF
    (GaussianGammaCanonicalExponent.exponentRadius z R B) R' (GaussianGammaCanonicalExponentBound.numericalRadius R)
    (exponentData z R B) (negativeData (tailData z R B N)) (correctedData z R B N)
    old negInput (GaussianGammaFoldedMajorantExponent.corrected_exponential_input z R B N h)
    (cross_symm _ _ _ _ (GaussianGammaFoldedMajorantExponent.corrected_cross z R B N h))
  have product := multiply_cross constantF constantF (multiplyF exponentialF negativeExpF)
    GaussianGammaFoldedMajorantExponent.exponentialF H H _ _ cnH cnH (multiply_fast _ _ _ _ cnE cnNeg)
    (GaussianGammaFoldedMajorantExponent.exponential_regular z R B N h) (cross_refl _ _ cnH) expProduct
  exact cross_trans _ _ _ _ _ _ associate product

/-- Exact C9 bound on an actual regular representative of the original
folded P_N, with genuine independent-precision equivalence. -/
theorem original_P_bounded_representative (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent pF majorantF (pData z B N) (majorantData z R B N) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (withdrawal_is_original_P z R B N h))
    (withdrawal_is_bounded_representative z R B N h)

theorem original_P_observation_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    bounded (ap2 pF p (pData z B N)) (majorant R*unit p+two) (unit p) := by
  have close := GaussianNameEquivalence.diagonal_at _ _ _ _ p
    (cross_to_diagonal _ _ _ _ (original_P_bounded_representative z R B N h))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ two (unit p) (majorant R) one (unit_positive p) (le_refl _)
      close (GaussianGammaFoldedMajorantExponent.majorant_point_bound p z R B N h))

theorem original_P_envelope (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    GaussianFastValueCut.rawEnvelope pF (pData z B N) (majorant R) one two := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianFastValueCut.rawEnvelope,Syn.shift,subst_pData,
    GaussianGammaFoldedMajorantExponent.subst_majorant,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (show Γ.map Fm.shift ⊢[PRAAx]
      majorant (Syn.shift R)*unit (var 0)+two ≐ majorant (Syn.shift R)*unit (var 0)+two*one by ipra_ring)
      (show Γ.map Fm.shift ⊢[PRAAx] unit (var 0) ≐ one*unit (var 0) by ipra_ring)
      (original_P_observation_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs)

theorem actual_withdrawal_original_P_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent withdrawalF pF
      (withdrawalData (var 0) (var 1) (var 2) (var 3)) (pData (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (withdrawal_is_original_P _ _ _ _ Prf.hyp0))
theorem actual_withdrawal_bounded_representative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent withdrawalF majorantF
      (withdrawalData (var 0) (var 1) (var 2) (var 3)) (majorantData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (withdrawal_is_bounded_representative _ _ _ _ Prf.hyp0))
theorem original_folded_P_C9_equivalence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent pF majorantF
      (pData (var 0) (var 2) (var 3)) (majorantData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_P_bounded_representative _ _ _ _ Prf.hyp0))
theorem original_folded_P_C9_regular_representative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶
      pointCN majorantF (majorantData (var 1) (var 2) (var 3) (var 4)) ⋏
      (crossEquivalent pF majorantF (pData (var 1) (var 3) (var 4))
        (majorantData (var 1) (var 2) (var 3) (var 4)) ⋏
       bounded (ap2 majorantF (var 0) (majorantData (var 1) (var 2) (var 3) (var 4))) (majorant (var 2)) one)) :=
  closeUniv 5 (.impI (.andI (GaussianGammaFoldedMajorantExponent.majorant_regular _ _ _ _ Prf.hyp0)
    (.andI (original_P_bounded_representative _ _ _ _ Prf.hyp0)
      (GaussianGammaFoldedMajorantExponent.majorant_point_bound _ _ _ _ _ Prf.hyp0))))
theorem original_folded_P_observation_C9_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ bounded (ap2 pF (var 0) (pData (var 1) (var 3) (var 4)))
      (majorant (var 2)*unit (var 0)+two) (unit (var 0))) :=
  closeUniv 5 (.impI (original_P_observation_bound _ _ _ _ _ Prf.hyp0))
theorem original_folded_P_C9_envelope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianFastValueCut.rawEnvelope pF (pData (var 0) (var 2) (var 3)) (majorant (var 1)) one two) :=
  closeUniv 4 (.impI (original_P_envelope _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFoldedC9Bound
