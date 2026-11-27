import IPRADerivations.Analysis.Stirling.AllOrders.Logarithms.GaussianStirlingAllOrderSharpRadius
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.SignedRemainder.GaussianStirlingAllOrderSignedBounds

/-!
# The strict oriented bracket with the exact positive rational endpoint

The named bound now uses the magnitude of the original first omitted
Bernoulli coefficient and the exact inverse power of the input.
The same radius controls the existing degree-based error budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpRadiusBridge

open_ipra
open GaussianStirlingAllOrderSharpRadius (absoluteCoefficient radiusNumerator radiusDenominator oriented_cap_radius)
open GaussianStirlingAllOrderLogRateTransport (upperPoint)
open GaussianStirlingAllOrderSignedBoundsTransport (orientedCap)
open GaussianStirlingAllOrderSignedLower (orientedF orientedData zeroPoint)
open GaussianStirlingAllOrderSignedBounds (oriented_cap_positive original_strict_oriented_bracket)
open GaussianStirlingAllOrderLogRateBudget (higher_inverse_power)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)
open GaussianStirlingNames (source)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (cross_refl)
open GaussianSignedNameExponentialOrder (constant_equal_cross)
open GaussianRationalHorner (qzero)
open BernoulliBounds (bden bden_pos)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem zero_point : Γ ⊢[PRAAx] (zeroPoint : PTm n) ≐ qzero :=
  (GaussianEulerDecayOrder.fraction_embedding zero one (le_refl one)).eqSymm.eqTrans RationalGaussianEmbedding.embed_zero

theorem cap_exact (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    orientedCap m A B ≐ upperPoint (radiusNumerator m B) (radiusDenominator m A) := by
  have h := oriented_cap_positive m A B x hs
  have hl := constant_equal_cross _ _ (zero_point (Γ := Γ)).eqSymm
  exact oriented_cap_radius m A B hs.andE₁
    (strict_transport _ _ _ _ _ _ _ _ hl (cross_refl constantF _ (constant_regular _)) h)

theorem exact_oriented_bracket (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx]
    strictOrder constantF orientedF qzero (orientedData m A B x) ⋏
      strictOrder orientedF constantF (orientedData m A B x)
        (upperPoint (radiusNumerator m B) (radiusDenominator m A)) := by
  have h := original_strict_oriented_bracket m A B x hs
  have h₁ := constant_equal_cross _ _ (zero_point (Γ := Γ)).eqSymm
  have h₂ := constant_equal_cross _ _ (cap_exact m A B x hs)
  have hO := cross_refl orientedF _ (GaussianStirlingAllOrderSignedLower.oriented_regular m A B x hs)
  exact .andI (strict_transport _ _ _ _ _ _ _ _ h₁ hO h.andE₁)
    (strict_transport _ _ _ _ _ _ _ _ hO h₂ h.andE₂)

theorem even_degree_budget (m : ℕ) (A B : PTm n) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] le (radiusNumerator m B*pw A (succ (num (2*m))))
      ((num (absoluteCoefficient m)*pw B (succ (num (2*m))))*radiusDenominator m A) := by
  let j := succ (num (2*m) : PTm n)
  let D : PTm n := num (bden (2*m+2))
  have d : Γ ⊢[PRAAx] le one D := Foundations.NumeralPrimes.num_le (a := 1) (bden_pos _)
  have ej : Γ ⊢[PRAAx] j+zero ≐ num (2*m+1) := by
    unfold j
    apply deriveNat
    ipra_simps
    push_cast
    ring
  have e := higher_inverse_power (num (absoluteCoefficient m)) D A B j zero d hBA
  exact le_congr (congrMul (congrMul (.eqRefl _) (congrAp2 powF ej (.eqRefl _))) (.eqRefl _))
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 powF ej (.eqRefl _)))) e

theorem odd_degree_budget (m : ℕ) (A B : PTm n) (hBA : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] le (radiusNumerator (m+1) B*pw A (succ (num (2*m+1))))
      ((num (absoluteCoefficient (m+1))*pw B (succ (num (2*m+1))))*radiusDenominator (m+1) A) := by
  let j := succ (num (2*m+1) : PTm n)
  let D : PTm n := num (bden (2*(m+1)+2))
  have d : Γ ⊢[PRAAx] le one D := Foundations.NumeralPrimes.num_le (a := 1) (bden_pos _)
  have ej : Γ ⊢[PRAAx] j+one ≐ num (2*(m+1)+1) := by
    unfold j
    apply deriveNat
    ipra_simps
    push_cast
    ring
  have e := higher_inverse_power (num (absoluteCoefficient (m+1))) D A B j one d hBA
  exact le_congr (congrMul (congrMul (.eqRefl _) (congrAp2 powF ej (.eqRefl _))) (.eqRefl _))
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 powF ej (.eqRefl _)))) e

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSharpRadiusBridge
