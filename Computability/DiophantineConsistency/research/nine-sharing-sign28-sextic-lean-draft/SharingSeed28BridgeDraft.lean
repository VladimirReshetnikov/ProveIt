import DiophantineConsistency.SharingSeed28Sextic
import DiophantineConsistency.SharingSeed31Sextic

/-! UNCOMPILED definitions and open propositions; no zero-set bridge theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSeed28BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

def lift {S : Type*} [CommSemiring S] (beta : S) (v : Fin 29 → S) : Fin 32 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, (v 9 + 1) * (beta * (v 1 + 1) + 1), v 16, v 17, v 18, v 19, v 20, v 21, (v 18 + (v 11 + 1)) ^ 2, v 22, v 23, v 24, v 25, v 26, v 27, (v 27) ^ 2, v 28]

def drop {S : Type*} (v : Fin 32 → S) : Fin 29 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 17, v 18, v 19, v 20, v 21, v 22, v 24, v 25, v 26, v 27, v 28, v 29, v 31]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open proposition, not a proved theorem. -/
def ForwardTarget (p : Fin 4 → ℤ) (beta : V) : Prop :=
  ((p 0 : ℤ) : DiffRing V) = ι beta →
    ∀ v : Fin 29 → V, InternalZero (SharingSeed28Sextic.seed p) v →
      InternalZero (SharingSeed31Sextic.seed p) (lift beta v)

/-- Open proposition, not a proved theorem. -/
def BackwardTarget (p : Fin 4 → ℤ) (beta : V) : Prop :=
  ((p 0 : ℤ) : DiffRing V) = ι beta →
    ∀ v : Fin 32 → V, InternalZero (SharingSeed31Sextic.seed p) v →
      InternalZero (SharingSeed28Sextic.seed p) (drop v)
end DiophantineConsistency.SharingSeed28BridgeDraft
