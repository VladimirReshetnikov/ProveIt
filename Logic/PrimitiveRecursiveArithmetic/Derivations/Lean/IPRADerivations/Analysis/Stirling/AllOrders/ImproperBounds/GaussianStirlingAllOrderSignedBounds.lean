import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedBoundsTransport
import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderImproperUpper

/-!
# The strict two-sided log-Stirling bound at every fixed order

At every positive rational argument, orient the literal truncation
error by the sign of its first omitted term. The resulting actual
name lies strictly between zero and that oriented term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedBounds

open_ipra
open GaussianGammaCanonicalExponent (constantF)
open GaussianNamedStrictOrderDifference (trans_weak)
open GaussianStirlingNames (source)
open GaussianStirlingAllOrderImproperUpper (original_improper_upper)
open GaussianStirlingAllOrderSignedBoundsTransport (orientedCap oriented_bracket_of_improper_upper)
open GaussianStirlingAllOrderSignedLower (orientedF orientedData zeroPoint)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_strict_oriented_bracket (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF orientedF zeroPoint (orientedData m A B x) ⋏
      strictOrder orientedF constantF (orientedData m A B x) (orientedCap m A B) :=
  oriented_bracket_of_improper_upper m A B x hs (original_improper_upper m A B x hs)

theorem oriented_cap_positive (m : ℕ) (A B x : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] strictOrder constantF constantF zeroPoint (orientedCap m A B) := by
  have h := original_strict_oriented_bracket m A B x hs
  exact trans_weak _ _ _ _ _ _ h.andE₁ h.andE₂.andE₁

theorem actual_all_order_oriented_log_Stirling_strict_bracket_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (source (var 0) (var 1) ⟶
      strictOrder constantF orientedF zeroPoint (orientedData m (var 0) (var 1) (var 2)) ⋏
        strictOrder orientedF constantF (orientedData m (var 0) (var 1) (var 2)) (orientedCap m (var 0) (var 1))) :=
  closeUniv 3 (.impI (original_strict_oriented_bracket m _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedBounds
