import DiophantineConsistency.SharingSeed32Sextic
import DiophantineConsistency.SharingSeed33Syntax

/-! UNCOMPILED definitions and open propositions; no zero-set bridge theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed32BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

/-- Insert the natural q² value as full coordinate 15. -/
def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 33 → S) : Fin 34 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, (beta * (v 1 + 1) + 1) ^ 2, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32]

/-- Drop the former full coordinate 15. -/
def drop {S : Type*} (v : Fin 34 → S) : Fin 33 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open proposition, not a proved theorem. -/
def ForwardTarget (p : Fin 4 → ℤ) (beta : V) : Prop :=
  ((p 0 : ℤ) : DiffRing V) = ι beta →
    ∀ v : Fin 33 → V, InternalZero (SharingSeed32Sextic.seed p) v →
      InternalZero (SharingSeed33.seed p) (lift beta v)

/-- Open proposition, not a proved theorem. -/
def BackwardTarget (p : Fin 4 → ℤ) (beta : V) : Prop :=
  ((p 0 : ℤ) : DiffRing V) = ι beta →
    ∀ v : Fin 34 → V, InternalZero (SharingSeed33.seed p) v →
      InternalZero (SharingSeed32Sextic.seed p) (drop v)
end DiophantineConsistency.SharingSeed32BridgeDraft
