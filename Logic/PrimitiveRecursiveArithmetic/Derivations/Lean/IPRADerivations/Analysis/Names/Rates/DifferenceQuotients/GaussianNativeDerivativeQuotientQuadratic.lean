import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNativeDerivativeQuotientRate

/-!
# Quotient rate from a uniform quadratic Taylor bound

For a nonzero native Gaussian displacement, use its coded L1 size
to cancel the shared denominator in a quadratic Taylor estimate.
The result retains the actual difference quotient and its original
independent observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNativeDerivativeQuotientQuadratic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianL1 (norm1)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem rate (f g D : PR 2) (x y d h B K : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hd : Γ ⊢[PRAAx] pointCN D d) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] le one (normSq h))
    (hr : Γ ⊢[PRAAx] independentRate (GaussianNamedDifference.nameF f g) (multiplyF constantF D)
      (GaussianNamedDifference.data x y) (multiplyData constantF D (ofGaussian h B) d)
      (K*norm1 h*norm1 h) (B*B)) : Γ ⊢[PRAAx]
    independentRate (GaussianNamedDifferenceQuotient.nameF f g) D
      (GaussianNamedDifferenceQuotient.data f g x y h B) d (two*K*norm1 h) B := by
  let H := norm1 h
  let F := GaussianNamedDifferenceQuotient.nameF f g
  let w := GaussianNamedDifferenceQuotient.data f g x y h B
  have hB2 := positive_product _ _ hB hB
  have hn := GaussianNativeDerivativeQuotientRate.norm1_positive h hh
  have core : Γ ⊢[PRAAx] independentRate F D w d ((two*B)*(K*H*H)) (H*(B*B)) :=
    GaussianNativeDerivativeQuotientRate.rate f g D x y d h B (K*H*H) (B*B) hf hg hd (.andI hB hh) hB2 hr
  refine GaussianNamedRateRadius.weaken F D w d _ _ (two*K*H) B (positive_product _ _ hn hB2) hB ?_ core
  exact le_of_eq_add (d := zero) (by ipra_ring)

end LeanProofs.IPRA.Analysis.GaussianNativeDerivativeQuotientQuadratic
