import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerArgumentIncrement
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.DirectionSelection.GaussianDominantPairAlgebra
import IPRADerivations.AnalyticNumberTheory.BertrandPostulate

/-!
# Reciprocal bound for the actual Euler logarithm displacement

For a nonzero native displacement, the integer floor of its norm
is a positive lower bound and its successor is a comparable upper
bound. The lower bound controls the reciprocal of the actual
Gaussian-rational step at the original common denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerStepReciprocal

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandPostulate (le_isqrt)
open ComplexLogarithmRemainder (normSq normSq_scale scale)
open GaussianDominantPairAlgebra (represents_cross)
open GaussianLogGammaEulerArgumentIncrement (step step_represents)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianRationalHorner (represents positive_product qmul)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRationalReciprocal
  (conjugate inverseNumerator norm_conjugate normNumerator qone reciprocal
    reciprocal_identity reciprocal_represents)
open GaussianRootAlgebra (normSq_equal sub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (A B neg a b sign : PTm n) : PTm n :=
  sub (native a b sign) (native A B neg)

def lower (δ : PTm n) : PTm n := isqrt (normSq δ)

def radius (δ : PTm n) : PTm n := lower δ + one

ipra_subst numerator

ipra_subst lower

ipra_subst radius

theorem lower_positive (δ : PTm n) (h : Γ ⊢[PRAAx] le one (normSq δ)) :
    Γ ⊢[PRAAx] le one (lower δ) :=
  le_isqrt (le_congr (by ipra_ring) (.eqRefl _) h)

theorem native_bounded (δ : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded δ (radius δ) :=
  le_of_lt (lt_isqrt_succ_sq (normSq δ))

theorem radius_le_twice_lower (δ : PTm n) (h : Γ ⊢[PRAAx] le one (normSq δ)) :
    Γ ⊢[PRAAx] le (radius δ) (two * lower δ) := by
  unfold radius
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (lower δ) (lower_positive δ h))

private theorem reciprocal_of_representation (q δ D E : PTm n)
    (hRep : Γ ⊢[PRAAx] represents q δ D) (hE : Γ ⊢[PRAAx] le one E)
    (hLower : Γ ⊢[PRAAx] le (E * E) (normSq δ)) : Γ ⊢[PRAAx]
    le one (normNumerator q) ⋏ bounded (reciprocal q) D E := by
  let r := rawDen q
  let v := rawGaussian q
  let M := normNumerator q
  have scaled := represents_cross q δ v D r hRep (raw_represents q)
  have norm : Γ ⊢[PRAAx] (r*r)*normSq δ ≐ (D*D)*M :=
    (normSq_scale r δ).eqSymm.eqTrans ((normSq_equal scaled).eqTrans (normSq_scale D v))
  have cleared : Γ ⊢[PRAAx] le ((E*E)*(r*r)) ((D*D)*M) :=
    le_congr (.eqRefl _) ((mul_comm _ _).eqTrans norm) (mul_le_mul_right (r*r) hLower)
  have hr := raw_den_positive (Γ := Γ) q
  have positive := le_trans (positive_product _ _ (positive_product _ _ hE hE) (positive_product _ _ hr hr)) cleared
  have hM : Γ ⊢[PRAAx] le one M := by
    refine .orE (zero_or_succ M) ?_ ?_
    · exact lt_zero_absurd _
        (le_congr (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)) positive.wk)
    · exact le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
  have inverseNorm : Γ ⊢[PRAAx] normSq (inverseNumerator q) ≐ (r*r)*M :=
    (normSq_scale r (conjugate v)).eqTrans (congrMul (.eqRefl _) (norm_conjugate v))
  exact .andI hM ((bounded_iff (reciprocal q) (inverseNumerator q) M D E hM hE
    (reciprocal_represents q hM)).iffMpr (le_congr
      ((mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) inverseNorm.eqSymm))
      (mul_assoc _ _ _) (mul_le_mul_right M cleared)))

def certificate (A B neg a b sign D : PTm n) : Fm PTm n :=
  let δ := numerator A B neg a b sign
  let q := step A B neg a b sign D
  le one (lower δ) ⋏ (ComplexLogarithmRemainder.bounded δ (radius δ) ⋏
    (le (radius δ) (two * lower δ) ⋏
      (le one (normNumerator q) ⋏ bounded (reciprocal q) D (lower δ))))

theorem certified_step (A B neg a b sign D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] le one (normSq (numerator A B neg a b sign))) :
    Γ ⊢[PRAAx] certificate A B neg a b sign D := by
  let δ := numerator A B neg a b sign
  have e := lower_positive δ h
  exact .andI e (.andI (native_bounded δ) (.andI (radius_le_twice_lower δ h)
    (reciprocal_of_representation (step A B neg a b sign D) δ D (lower δ)
      (step_represents A B neg a b sign D hD) e (isqrt_le _))))

theorem step_inverse_identity (A B neg a b sign D : PTm n)
    (h : Γ ⊢[PRAAx] certificate A B neg a b sign D) : Γ ⊢[PRAAx]
    qmul (step A B neg a b sign D) (reciprocal (step A B neg a b sign D)) ≐ qone :=
  reciprocal_identity _ h.andE₂.andE₂.andE₂.andE₁

theorem actual_Euler_logarithm_displacement_reciprocal_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (le one (var 6) ⟶
        le one (normSq (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) ⟶
        certificate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (certified_step _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerStepReciprocal
