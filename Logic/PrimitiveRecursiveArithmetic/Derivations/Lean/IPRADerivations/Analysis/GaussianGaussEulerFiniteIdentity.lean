import IPRADerivations.Analysis.GaussianGaussEulerFixedFamilyFactors
import IPRADerivations.Analysis.GaussianGaussEulerPositiveFamily
import IPRADerivations.Analysis.GaussianGaussEulerProductAlgebra
import IPRADerivations.Analysis.GaussianGaussMultiplicationM2Transport

/-!
# Exact finite Euler identity and cleared Gauss multiplication

The finite identity compares the original shifted and reference folds
at cutoff N with the scaled and unit Euler names at m(N+1)−1. Its two
exact components are the rational inverse-head grouping and the
exponential product identity. The common cofinal cutoff satisfies all
required finite guards, so the identity transfers to the Gamma names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerFiniteIdentity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerDenominatorGrouping (shiftedData)
open GaussianGammaEulerFullHeadInverse (negExpF negExpData headInverse negative_exponential_regular name_regular)
open GaussianGammaEulerInverseApproximationName (cutoff_guards)
open GaussianGammaEulerReciprocalInverse (eulerF euler_regular)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerCutoff (scaled_cutoff_later)
open GaussianGaussEulerFactorFamilies (shiftedExpData referenceExpData shifted_exp_regular reference_exp_regular)
open GaussianGaussEulerNamedHeadGrouping (shiftedNameF referenceNameF shiftedNameData referenceNameData named_head_grouping)
open GaussianGaussMultiplicationCofinalProducts (leftF rightF leftData rightData)
open GaussianGaussMultiplicationFixedFactors (power_regular scaledEulerData unitEulerData)
open GaussianGaussMultiplicationM2Transport (m2At cofinalM2 cleared_from_m2)
open GaussianGaussMultiplicationPowerRate (powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedFiniteProductFamily (family_product_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaGaussEulerHeads.cutoff
local notation "needed" => GaussianGammaEulerInverseApproximationName.cutoff
local notation "SExp" => GaussianGaussEulerFactorFamilies.shiftedF
local notation "RExp" => GaussianGaussEulerFactorFamilies.referenceF
local notation "SF" => GaussianGaussMultiplicationFixedProducts.shiftedF
local notation "RF" => GaussianGaussMultiplicationFixedProducts.referenceF
local notation "fullF" => GaussianGammaEulerFullHeadInverse.nameF
local notation "fullData" => GaussianGammaEulerFullHeadInverse.data

def finiteCutoffs (s R m a d N : PTm n) : Fm PTm n :=
  le one N ⋏ (le (GaussianGammaGaussEulerProduct.threshold s R m a d) N ⋏
    (le (GaussianGammaGaussReferenceEulerProduct.threshold s m) N ⋏
      (le (needed s one one one) (L m N) ⋏ le (needed s (scaledRadius R m) a d) (L m N))))

@[simp] theorem subst_finiteCutoffs {l : ℕ} (σ : Fin n → PTm l) (s R m a d N : PTm n) :
    (finiteCutoffs s R m a d N).subst σ =
      finiteCutoffs (Syn.subst σ s) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d)
        (Syn.subst σ N) := by
  simp [finiteCutoffs,one]

theorem finite_identity (s z R B m a d N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hn : Γ ⊢[PRAAx] finiteCutoffs s R m a d N) :
    Γ ⊢[PRAAx] m2At N z R B m d := by
  let T := L m N
  let U : PTm n := oneCode
  let Z := scale m z
  let radius := scaledRadius R m
  let SH := shiftedNameData z B m N
  let SE := shiftedExpData z B m N
  let RH := referenceNameData m N
  let RE := referenceExpData m N
  let UH := headInverse U one T
  let UE := negExpData U one T
  let ZH := headInverse Z B T
  let ZE := negExpData Z B T
  let W := rowData z R B m N
  have hm := hs.andE₁.andE₁
  have hN := hn.andE₁
  have hT := le_trans hN (scaled_cutoff_later m N hm)
  have shiftedLater := hn.andE₂.andE₁
  have referenceLater := hn.andE₂.andE₂.andE₁
  have unitLater := hn.andE₂.andE₂.andE₂.andE₁
  have scaledLater := hn.andE₂.andE₂.andE₂.andE₂
  have us : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source U one one one one T :=
    .andI GaussianGammaNormalization.unit_gamma_source (le_trans (cutoff_guards s one one one).andE₁ unitLater)
  have zs : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source Z radius B a d T :=
    .andI hs.andE₂ (le_trans (cutoff_guards s radius a d).andE₁ scaledLater)
  have hSH := GaussianGaussEulerNamedHeadGrouping.shifted_regular (Γ := Γ) z B m N
  have hRH := GaussianGaussEulerNamedHeadGrouping.reference_regular (Γ := Γ) m N
  have hSE := family_product_regular negExpF _ m (shiftedData z B m N) (shifted_exp_regular z B m N hN)
  have hRE := family_product_regular negExpF _ m (pairT m N) (reference_exp_regular m N hN)
  have hUH := constant_regular (Γ := Γ) UH
  have hZH := constant_regular (Γ := Γ) ZH
  have hUE := negative_exponential_regular U one T hT
  have hZE := negative_exponential_regular Z B T hT
  have hW := power_regular z R B m a d N hs hN
  have hSF := GaussianGaussMultiplicationFixedProducts.shifted_regular s z R B m a d N hs shiftedLater
  have hRF := GaussianGaussMultiplicationFixedProducts.reference_regular s m N referenceLater
  have hUF := euler_regular U one one one one T us
  have hZF := euler_regular Z radius B a d T zs

  have shiftFact := GaussianGaussEulerFixedFamilyFactors.shifted_factorization s z R B m a d N hs shiftedLater
  have refFact := GaussianGaussEulerFixedFamilyFactors.reference_factorization s m N referenceLater
  have unitFact := GaussianGammaEulerFullHeadInverse.original_factorization U one one one one T us
  have scaledFact := GaussianGammaEulerFullHeadInverse.original_factorization Z radius B a d T zs
  have left := multiply_cross SF (multiplyF shiftedNameF SExp) eulerF fullF
    (GaussianGaussMultiplicationFixedProducts.shiftedData z R B m d N) (multiplyData shiftedNameF SExp SH SE)
    (unitEulerData m N) (fullData U one T)
    hSF (multiply_fast _ _ _ _ hSH hSE) hUF (name_regular U one T hT) shiftFact unitFact

  have originalPower := multiply_fast powerF eulerF W (scaledEulerData z R B m d N) hW hZF
  have expandedPower := multiply_fast powerF fullF W (fullData Z B T) hW (name_regular Z B T hT)
  have powerScaled := multiply_cross powerF powerF eulerF fullF W W (scaledEulerData z R B m d N)
    (fullData Z B T) hW hW hZF (name_regular Z B T hT) (cross_refl _ _ hW) scaledFact
  have right := multiply_cross (multiplyF powerF eulerF) (multiplyF powerF fullF) RF (multiplyF referenceNameF RExp)
    (multiplyData powerF eulerF W (scaledEulerData z R B m d N)) (multiplyData powerF fullF W (fullData Z B T))
    (GaussianGaussMultiplicationFixedProducts.referenceData m N) (multiplyData referenceNameF RExp RH RE)
    originalPower expandedPower hRF (multiply_fast _ _ _ _ hRH hRE) powerScaled refFact

  have heads := named_head_grouping z R B m a d N hs
  have exponents := GaussianGaussEulerPositiveFamily.exponential_product z R B m N hm hN
    hs.andE₂.andE₁.andE₂.andE₁ hs.andE₁.andE₂
  have rearranged := GaussianGaussEulerProductAlgebra.combine_head_and_exponent
    shiftedNameF SExp constantF negExpF constantF negExpF referenceNameF RExp powerF
    SH SE UH UE ZH ZE RH RE W hSH hSE hUH hUE hZH hZE hRH hRE hW heads exponents
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ rearranged (cross_symm _ _ _ _ right))

theorem cofinal_cutoffs (s R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] finiteCutoffs s R m a d (GaussianGaussMultiplicationCofinalRows.cutoff s R m a d) :=
  .andI (GaussianGaussMultiplicationCofinalRows.cutoff_positive s R m a d hm)
    (.andI (GaussianGaussMultiplicationCofinalRows.shifted_cutoff s R m a d hm)
      (.andI (GaussianGaussMultiplicationCofinalRows.reference_cutoff s R m a d hm)
        (.andI (GaussianGaussMultiplicationCofinalRows.unit_cutoff s R m a d hm)
          (GaussianGaussMultiplicationCofinalRows.scaled_cutoff s R m a d hm))))

theorem cofinal_identity (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] cofinalM2 z R B m a d := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have h : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Fm.shift, Syn.shift, sh] using hs.shift
  simpa [cofinalM2, sh] using finite_identity (var 0) (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) _
    h (cofinal_cutoffs (var 0) (sh R) (sh m) (sh a) (sh d) h.andE₁.andE₁)

theorem cleared_Gauss_multiplication (z R B m a d : PTm n) (hs : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData z R B m d) (rightData z R B m d) :=
  cleared_from_m2 z R B m a d hs (cofinal_identity z R B m a d hs)

theorem actual_finite_Euler_Gauss_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⋏
      finiteCutoffs (var 0) (var 2) (var 4) (var 5) (var 6) (var 7)) ⟶
      m2At (var 7) (var 1) (var 2) (var 3) (var 4) (var 6)) :=
  closeUniv 8 (.impI (finite_identity _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_cleared_Gauss_multiplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent leftF rightF (leftData (var 0) (var 1) (var 2) (var 3) (var 5))
        (rightData (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (cleared_Gauss_multiplication _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerFiniteIdentity
