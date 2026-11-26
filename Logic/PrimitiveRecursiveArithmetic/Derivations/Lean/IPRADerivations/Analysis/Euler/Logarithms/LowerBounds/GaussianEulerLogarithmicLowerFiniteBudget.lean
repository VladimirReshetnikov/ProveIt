import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicLowerQuadrature
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailFiniteBudget

/-!
# Quantitative lower logarithmic quadrature budget

The source-only actual finite quadrature retains the coefficient
j!(2A)^j. Clearing its actual root denominator gives the leading bound
j!(2A)^(j+1)/2^height(p,2A,R), plus an explicit fixed-interval residual
times 2^-t. Mesh and observation precisions may be independently finer.
This is a finite actual-grid result, not an improper-integral assertion.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerFiniteBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicLowerRootRows (source panelExponent panelDegree lipschitz)
open GaussianEulerLogarithmicLowerPointwise (coefficient)
open GaussianEulerLogarithmicLowerQuadrature (originalQuadrature)
open GaussianEulerLowerTailRootGrid (rootDenominator)
open GaussianEulerLowerTailFiniteBudget (oldNumerator oldDenominator nativeNumerator nativeDenominator scale residual)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianGammaIntegralCutoffs (height)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (t j p q A R : PTm n) : PTm n := coefficient j A*
  GaussianEulerLowerTailFiniteBudget.numerator t p q (panelExponent A) R (lipschitz j q A R)
def denominator (t p A R : PTm n) : PTm n :=
  GaussianEulerLowerTailFiniteBudget.denominator t p (panelExponent A) R
def residualCoefficient (j p q A R : PTm n) : PTm n :=
  coefficient j A*residual (scale p q (panelExponent A)) (lipschitz j q A R)

theorem leading_coefficient (j A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    coefficient j A*panelDegree A ≐ Products.fact j*pw (GaussianEulerLogarithmicLowerPointwise.degree A) (ConciseIPRA.PTm.succ j) :=
  (congrMul (.eqRefl _) (GaussianEulerLogarithmicLowerRootRows.degree_identity A hA).eqSymm).eqTrans
    ((by unfold coefficient; ipra_ring : Γ ⊢[PRAAx] coefficient j A*GaussianEulerLogarithmicLowerPointwise.degree A ≐
      Products.fact j*(pw (GaussianEulerLogarithmicLowerPointwise.degree A) j*GaussianEulerLogarithmicLowerPointwise.degree A)).eqTrans
      (congrMul (.eqRefl _) (pw_succ _ _).eqSymm))

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (t j p q A R : PTm n) :
    Syn.subst σ (numerator t j p q A R) = numerator (Syn.subst σ t) (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (t p A R : PTm n) :
    Syn.subst σ (denominator t p A R) = denominator (Syn.subst σ t) (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ R) := by simp [denominator]
@[simp] theorem subst_residualCoefficient {m : ℕ} (σ : Fin n → PTm m) (j p q A R : PTm n) :
    Syn.subst σ (residualCoefficient j p q A R) = residualCoefficient (Syn.subst σ j) (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ R) := by simp [residualCoefficient]

theorem original_finite_budget (s t j z R B H p q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B H p q A)
    (hMesh : Γ ⊢[PRAAx] le (unit t) H) (hPrecision : Γ ⊢[PRAAx] le (unit t) (unit s)) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s j z R B H p q A) (numerator t j p q A R) (denominator t p A R) := by
  let e := panelExponent A
  let D := rootDenominator H q (panelDegree A) R
  let S := scale p q e
  let L := lipschitz j q A R
  let C := coefficient j A
  have hND : Γ ⊢[PRAAx] le H D := GaussianEulerLowerTailFiniteBudget.root_denominator_ge H q e R
  have hD := le_trans h.andE₂.andE₁ hND
  have hpq := le_of_lt h.andE₂.andE₂
  have leading : Γ ⊢[PRAAx] le (H*S*unit (height p (panelDegree A) R)) (panelDegree A*D) :=
    le_congr (by dsimp only [S,e,panelDegree]; ipra_ring)
      (by dsimp only [D,e,panelDegree]; unfold rootDenominator; ipra_ring)
      (mul_le_mul_right H (GaussianEulerLowerTailFiniteBudget.leading_height_budget p q e R hpq))
  have square := AnalyticNumberTheory.PhiLower.le_mul_mono hND (le_trans hMesh hND)
  have observation := AnalyticNumberTheory.PhiLower.le_mul_mono hND hPrecision
  have clear := GaussianEulerLowerTailFiniteBudget.cleared_radius H D S L (unit s) (panelDegree A)
    (unit (height p (panelDegree A) R)) (unit t) leading square observation
  have old : Γ ⊢[PRAAx] bounded (originalQuadrature s j z R B H p q A)
      (C*oldNumerator H D S L (unit s)) (oldDenominator D (unit s)) :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _)
      (by dsimp only [C,D,S,L]; unfold oldNumerator scale GaussianEulerLowerBlockWeight.numerator GaussianEulerLowerTailRowBound.stepScale; ipra_ring)
      (.eqRefl _) (GaussianEulerLogarithmicLowerQuadrature.original_finite_lower_quadrature_bound s j z R B H p q A h)
  have scaledClear : Γ ⊢[PRAAx] le ((C*oldNumerator H D S L (unit s))*denominator t p A R)
      (numerator t j p q A R*oldDenominator D (unit s)) := by
    have native := mul_le_mul_right C clear
    dsimp only [numerator,denominator,GaussianEulerLowerTailFiniteBudget.numerator,GaussianEulerLowerTailFiniteBudget.denominator,
      nativeDenominator,C,D,S,L,e,panelDegree] at native ⊢
    exact le_congr (by ipra_ring) (by ipra_ring) native
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hD hD) (unit_positive s))
    (positive_product _ _ (unit_positive (height p (panelDegree A) R)) (unit_positive t)) scaledClear old

def precision (r j p q A R : PTm n) : PTm n := GaussianFastValueCut.exponent (residualCoefficient j p q A R) r

theorem original_dyadic_budget (s r j z R B H p q A : PTm n)
    (h : Γ ⊢[PRAAx] source z R B H p q A)
    (hMesh : Γ ⊢[PRAAx] le (unit (precision r j p q A R)) H)
    (hPrecision : Γ ⊢[PRAAx] le (unit (precision r j p q A R)) (unit s)) : Γ ⊢[PRAAx]
    bounded (originalQuadrature s j z R B H p q A)
      (coefficient j A*panelDegree A*unit r+unit (height p (panelDegree A) R))
      (unit (height p (panelDegree A) R)*unit r) := by
  let t := precision r j p q A R
  have old := original_finite_budget s t j z R B H p q A h hMesh hPrecision
  have query : Γ ⊢[PRAAx] le (residualCoefficient j p q A R*unit r) (unit (precision r j p q A R)) :=
    GaussianFastValueCut.query_budget (residualCoefficient j p q A R) r
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive (height p (panelDegree A) R)) (unit_positive t))
    (positive_product _ _ (unit_positive (height p (panelDegree A) R)) (unit_positive r)) _ old
  simp only [numerator,GaussianEulerLowerTailFiniteBudget.numerator,nativeNumerator]
  dsimp only [t,panelDegree] at query ⊢
  unfold residualCoefficient at query
  ipra_le (Groth.ι (Q.mk Γ (unit (height p (ConciseIPRA.PTm.succ (panelExponent A)) R))))^2*sl query

theorem original_logarithmic_lower_finite_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    ((source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏
      (le (unit (var 1)) (var 6) ⋏ le (unit (var 1)) (unit (var 0)))) ⟶
      bounded (originalQuadrature (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 1) (var 2) (var 7) (var 8) (var 9) (var 4)) (denominator (var 1) (var 7) (var 9) (var 4))) :=
  closeUniv 10 (.impI (original_finite_budget _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerFiniteBudget
