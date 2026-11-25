import IPRADerivations.Analysis.GaussianSineProductT6

/-!
# Closed finite form of the (T4) comparison

The finite premises describe the factor row and sinc prefactor. The
conclusion compares their literal product with the literal first K
factors of the sine product, with the paper's error and precision cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT4Finite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianSineProductT4Budget (halfIndex squareDenominator rate cutoff precision_bound)
open GaussianSineProductT6 (factorSize t4_finite)
open GaussianGammaEulerReflectionHead (body sineProduct)
open GaussianInverseSquareProductTail (factorBounds)
open GaussianInverseSquareProductComparison (rowErrors)
open GaussianRationalFiniteProduct (qprod)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (qone)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (f : PTm 2) (x s z R B K : PTm n) : Fm PTm n :=
  ((le one R ⋏ le one B) ⋏ le one K) ⋏
    (ComplexLogarithmRemainder.bounded z (R*B) ⋏ factorBounds f x (factorSize R) zero) ⋏
    (rowErrors f body x (pairT z B) (num 96*(R*R)) (R*R) (squareDenominator R K) K ⋏
      distanceBounded s qone (num 8*(R*R)) (squareDenominator R K))

def value (f : PTm 2) (x s R K : PTm n) : PTm n := qmul s (qprod f (halfIndex R K) x)

theorem rate_at (f : PTm 2) (x s z R B K : PTm n)
    (h : Γ ⊢[PRAAx] source f x s z R B K) :
    Γ ⊢[PRAAx] distanceBounded (value f x s R K) (sineProduct z B K) (rate R) K :=
  t4_finite f x s z R B K h.andE₁.andE₁.andE₁ h.andE₁.andE₁.andE₂ h.andE₁.andE₂
    h.andE₂.andE₁.andE₁ h.andE₂.andE₁.andE₂ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂

theorem precision_at (f : PTm 2) (x s z R B K p : PTm n)
    (h : Γ ⊢[PRAAx] source f x s z R B K) (hp : Γ ⊢[PRAAx] le (cutoff R p) K) :
    Γ ⊢[PRAAx] distanceBounded (value f x s R K) (sineProduct z B K) one (unit p) :=
  precision_bound _ _ R K p h.andE₁.andE₂ hp (rate_at f x s z R B K h)

theorem actual_finite_sine_product_T4_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f (var 5) (var 4) (var 3) (var 2) (var 1) (var 0) ⟶
        distanceBounded (value f (var 5) (var 4) (var 2) (var 0))
          (sineProduct (var 3) (var 1) (var 0)) (rate (var 2)) (var 0)) :=
  closeUniv 6 (.impI (rate_at f _ _ _ _ _ _ Prf.hyp0))

theorem actual_finite_sine_product_T4_precision_closed (f : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source f (var 6) (var 5) (var 4) (var 3) (var 2) (var 1) ⟶ le (cutoff (var 3) (var 0)) (var 1) ⟶
        distanceBounded (value f (var 6) (var 5) (var 3) (var 1))
          (sineProduct (var 4) (var 2) (var 1)) one (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (precision_at f _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductT4Finite
