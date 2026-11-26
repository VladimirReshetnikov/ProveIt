import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFixedEulerExponentBalance
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedC9Bound

/-!
# Exact fixed-Euler factorization of the original folded Q_N

The original folded Euler name is equivalent to the SAME head_(2R)
times the exponential of the actual corrected fixed Euler exponent.
All original operation clocks, the original fixed/cofinal Euler names,
and the actual finite approximant data are retained. The bound uses the
same literal M_R as C9, preparing the same lambda lower bound without
assuming a target factorization, inverse law, or nonzero head.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFoldedQBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFoldedMajorantExponent (input majorant)
open GaussianGammaFixedEulerExponent (correctedF correctedData)
open GaussianGammaFiniteApproximantName (pF pData p_regular qF qData q_regular)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correction_fast)
open GaussianGammaFoldedApproximantBalance (correctionExpF correctionExpData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianGammaCanonicalExponentBound (numericalRadius)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF correctedF
def exponentialData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data (numericalRadius R) (correctedData z R B N)
def factoredF : PR 2 := multiplyF constantF exponentialF
def factoredData (z R B N : PTm n) : PTm n := multiplyData constantF exponentialF
  (GaussianGammaEulerHead.run z B (two*R)) (exponentialData z R B N)
@[simp] theorem subst_exponentialData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (exponentialData z R B N) = exponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialData]
@[simp] theorem subst_factoredData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (factoredData z R B N) = factoredData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [factoredData,GaussianNameArithmetic.subst_multiplyData,subst_exponentialData,
    GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  congr 1
  funext i
  fin_cases i <;> simp

/-- The cancellation is proved for the actual corrected and original
names, rather than postulated as a target exponent identity. -/
theorem corrected_exponents_balance (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNameArithmetic.addF GaussianGammaFoldedMajorantExponent.correctedF correctionF) correctedF
      (GaussianNameArithmetic.addData (GaussianGammaFoldedMajorantExponent.correctedData z R B N) (correctionData z B N))
      (correctedData z R B N) := by
  have hn := (GaussianGammaFoldedMajorantExponent.tail_source z R B N h).andE₂.andE₁
  have cnC := correction_fast z B N hn
  have first := GaussianNameArithmetic.add_equivalent GaussianGammaFoldedMajorantExponent.correctedF
    GaussianGammaFoldedMajorantExponent.combinedF correctionF correctionF _ _ _ _
    (GaussianGammaFoldedMajorantExponent.corrected_regular z R B N h)
    (GaussianGammaFoldedMajorantExponent.combined_regular z R B N h) cnC cnC
    (cross_to_diagonal _ _ _ _ (GaussianGammaFoldedMajorantExponent.corrected_cross z R B N h))
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ cnC))
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _
    (GaussianGammaFixedEulerExponentBalance.balanced_exponents z R B N h)
    (cross_symm _ _ _ _ (GaussianGammaFixedEulerExponent.corrected_cross z R B N h)))

theorem exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN exponentialF (exponentialData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianGammaFixedEulerExponent.corrected_exponential_input z R B N h)
theorem factored_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] pointCN factoredF (factoredData z R B N) :=
  multiply_fast _ _ _ _ (constant_regular _) (exponential_regular z R B N h)

theorem original_Q_factored (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent qF factoredF (qData z B N) (factoredData z R B N) := by
  let H := GaussianGammaEulerHead.run z B (two*R)
  let X := GaussianGammaFoldedMajorantExponent.exponentialData z R B N
  let Y := correctionExpData z B N
  let C := correctionData z B N
  have hn := (GaussianGammaFoldedMajorantExponent.tail_source z R B N h).andE₂.andE₁
  have ci := GaussianGammaFiniteApproximantName.exponential_input correctionF C (correction_fast z B N hn)
  have cnC := GaussianRadiusExponentialName.name_regular _ _ _ ci
  have cnOld := GaussianGammaFoldedMajorantExponent.exponential_regular z R B N h
  have first := multiply_cross pF GaussianGammaFoldedMajorantExponent.majorantF correctionExpF correctionExpF
    (pData z B N) (GaussianGammaFoldedMajorantExponent.majorantData z R B N) Y Y (p_regular z B N)
    (GaussianGammaFoldedMajorantExponent.majorant_regular z R B N h) cnC cnC
    (GaussianGammaFoldedC9Bound.original_P_bounded_representative z R B N h) (cross_refl _ _ cnC)
  have associate := GaussianNameRingLaws.multiply_associative constantF GaussianGammaFoldedMajorantExponent.exponentialF correctionExpF
    H X Y (constant_regular _) cnOld cnC
  have exp := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent
    GaussianGammaFoldedMajorantExponent.correctedF correctionF correctedF (numericalRadius R)
    (GaussianNameBounds.U correctionF C) (numericalRadius R)
    (GaussianGammaFoldedMajorantExponent.correctedData z R B N) C (correctedData z R B N)
    (GaussianGammaFoldedMajorantExponent.corrected_exponential_input z R B N h) ci
    (GaussianGammaFixedEulerExponent.corrected_exponential_input z R B N h) (corrected_exponents_balance z R B N h)
  have last := multiply_cross constantF constantF (multiplyF GaussianGammaFoldedMajorantExponent.exponentialF correctionExpF)
    exponentialF H H _ _ (constant_regular _) (constant_regular _) (multiply_fast _ _ _ _ cnOld cnC)
    (exponential_regular z R B N h) (cross_refl _ _ (constant_regular H)) exp
  exact cross_trans _ _ _ _ _ _ (GaussianGammaFoldedApproximantBalance.euler_factor_identity z B N hn)
    (cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ associate last))

theorem exponential_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 exponentialF p (exponentialData z R B N)) (pw (num 3) (numericalRadius R)) one :=
  GaussianRationalReciprocal.bound_congr (GaussianRadiusExponentialName.sample_at correctedF (numericalRadius R) p (correctedData z R B N)).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianGammaFixedEulerExponent.corrected_finite_exponential_bound (GaussianRadiusExponentialName.inputPrecision (numericalRadius R) p)
      (GaussianRadiusExponentialName.index (numericalRadius R) p) z R B N h)

theorem factored_point_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) :
    Γ ⊢[PRAAx] bounded (ap2 factoredF p (factoredData z R B N)) (majorant R) one := by
  let H := GaussianGammaEulerHead.run z B (two*R)
  let s := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF exponentialF H (exponentialData z R B N)) p
  have hb := GaussianRationalReciprocal.bound_congr (constant_at s H).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaEulerHead.returned_head_bound z R B (two*R) h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂)
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hb (exponential_point_bound s z R B N h)
  exact GaussianRationalReciprocal.bound_congr (GaussianNameArithmetic.multiply_at constantF exponentialF H (exponentialData z R B N) p).eqSymm
    (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ _ _ (le_refl one)).iffMpr
      (GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) product))

theorem original_Q_observation_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    bounded (ap2 qF p (qData z B N)) (majorant R*unit p+two) (unit p) := by
  have close := GaussianNameEquivalence.diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (original_Q_factored z R B N h))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ two (unit p) (majorant R) one (unit_positive p) (le_refl _)
      close (factored_point_bound p z R B N h))

theorem original_folded_Q_fixed_euler_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent qF factoredF (qData (var 0) (var 2) (var 3))
      (factoredData (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (.impI (original_Q_factored _ _ _ _ Prf.hyp0))
theorem original_folded_Q_fixed_euler_regular_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ pointCN factoredF (factoredData (var 1) (var 2) (var 3) (var 4)) ⋏
      (crossEquivalent qF factoredF (qData (var 1) (var 3) (var 4)) (factoredData (var 1) (var 2) (var 3) (var 4)) ⋏
        bounded (ap2 factoredF (var 0) (factoredData (var 1) (var 2) (var 3) (var 4))) (majorant (var 2)) one)) :=
  closeUniv 5 (.impI (.andI (factored_regular _ _ _ _ Prf.hyp0)
    (.andI (original_Q_factored _ _ _ _ Prf.hyp0) (factored_point_bound _ _ _ _ _ Prf.hyp0))))
theorem original_folded_Q_observation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 1) (var 2) (var 3) (var 4) ⟶ bounded (ap2 qF (var 0) (qData (var 1) (var 3) (var 4)))
      (majorant (var 2)*unit (var 0)+two) (unit (var 0))) := closeUniv 5 (.impI (original_Q_observation_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFoldedQBound
