import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.SignedDiscreteThirdDerivativeEstimate
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalHorner

/-!
# Fine refinement cancels out of the coarse third-difference budget

Set the derivative scale D to N*M, with M the positive fine
refinement and N the coarse mesh denominator. Cancelling M³
leaves errors T+4N² E0+2N E1+E2 against N³ times the original
coarse third difference. The refinement can therefore be chosen
after fixing the three derivative precision budgets.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open SignedDiscreteDerivativeBlock (source)
open SignedDiscreteDerivativeOperators (width divisor)
open SignedDiscreteThirdDerivativeIdentity (coarseThird)
open SignedDiscreteThirdDerivativeEstimate (window coarse_lower)
open SignedDiscreteDerivativeBounds (floorOn)
open SignedCubicTaylorGrid (combination)
open GaussianRationalHorner (positive_product)
open PolynomialBisection (zle_congr zle_scale_cancel)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stencil (b : ZB) (x i : PTm n) : ZT n :=
  let j := i+width x
  let k := j+width x
  let l := k+width x
  combination (b.val i x) (b.val j x) (b.val k x) (b.val l x)

def budget (N T E₀ E₁ E₂ : PTm n) : PTm n :=
  T+num 4*(N*N)*E₀+two*N*E₁+E₂

theorem normalized_lower (b g h j : ZB) (x i N T E₀ E₁ E₂ : PTm n)
    (hM : Γ ⊢[PRAAx] le one (width x)) (hD : Γ ⊢[PRAAx] divisor x ≐ N*width x)
    (h₀ : Γ ⊢[PRAAx] source b g x (window x i) (divisor x) E₀)
    (h₁ : Γ ⊢[PRAAx] source g h x (window x i) (divisor x) E₁)
    (h₂ : Γ ⊢[PRAAx] source h j x (window x i) (divisor x) E₂)
    (hj : Γ ⊢[PRAAx] floorOn j x (window x i) T) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (budget N T E₀ E₁ E₂)) (ZT.ofNat (N*(N*N))*stencil b x i) := by
  let C := width x*(width x*width x)
  have positive : Γ ⊢[PRAAx] le one C :=
    positive_product _ _ hM (positive_product _ _ hM hM)
  have equal := natEq hD
  simp only [Q.mk_mul,map_mul] at equal
  apply zle_scale_cancel positive
  refine zle_congr ?_ ?_ (coarse_lower b g h j x i T E₀ E₁ E₂ h₀ h₁ h₂ hj)
  · simp only [SignedDiscreteThirdDerivativeEstimate.budget,budget,C,ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat,
      Q.mk_mul,map_mul,Q.mk_add,map_add,equal]
    ring
  · change ZT.toZ Γ (ZT.ofNat (divisor x*(divisor x*divisor x))*stencil b x i) = _
    simp only [C,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul,equal]
    ring

theorem actual_refinement_independent_signed_third_bound_closed (b g h j : ZB) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (let x := var 0
       let i := var 1
       let N := var 2
       let T := var 3
       let E₀ := var 4
       let E₁ := var 5
       let E₂ := var 6
       le one (width x) ⟶ divisor x ≐ N*width x ⟶
         source b g x (window x i) (divisor x) E₀ ⟶
         source g h x (window x i) (divisor x) E₁ ⟶
         source h j x (window x i) (divisor x) E₂ ⟶
         floorOn j x (window x i) T ⟶
         zle (-ZT.ofNat (budget N T E₀ E₁ E₂)) (ZT.ofNat (N*(N*N))*stencil b x i)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI (.impI (normalized_lower b g h j _ _ _ _ _ _ _
    Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.SignedDiscreteThirdDerivativeNormalization
