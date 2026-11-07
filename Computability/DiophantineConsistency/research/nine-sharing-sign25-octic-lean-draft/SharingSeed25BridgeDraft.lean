import DiophantineConsistency.SharingSeed25Octic
import DiophantineConsistency.SharingSeed26Sextic

/-! SOURCE-ONLY definitions and open targets; no zero-set theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSeed25BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

def lift {S : Type*} [Mul S] (v : Fin 26 → S) : Fin 27 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 17 * v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25]

def drop {S : Type*} (v : Fin 27 → S) : Fin 26 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 20, v 21, v 22, v 23, v 24, v 25, v 26]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open proposition; no zero-set theorem is asserted. -/
def ForwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 26 → V, InternalZero (SharingSeed25Octic.seed p) v →
    InternalZero (SharingSeed26Sextic.seed p) (lift v)

/-- Open proposition; reverse requires recovery of the deleted product coordinate. -/
def BackwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 27 → V, InternalZero (SharingSeed26Sextic.seed p) v →
    InternalZero (SharingSeed25Octic.seed p) (drop v)
end DiophantineConsistency.SharingSeed25BridgeDraft
