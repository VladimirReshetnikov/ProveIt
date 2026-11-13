import DiophantineConsistency.SharingSeed31Sextic
import DiophantineConsistency.SharingSeed32Sextic

/-! UNCOMPILED definitions and open propositions; no zero-set bridge theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSeed31BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

def lift {S : Type*} [CommSemiring S] (v : Fin 32 → S) : Fin 33 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, (v 5 + 1) ^ 2, v 27, v 28, v 29, v 30, v 31]

def drop {S : Type*} (v : Fin 33 → S) : Fin 32 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 28, v 29, v 30, v 31, v 32]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open proposition, not a proved theorem. -/
def ForwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 32 → V, InternalZero (SharingSeed31Sextic.seed p) v →
    InternalZero (SharingSeed32Sextic.seed p) (lift v)

/-- Open proposition, not a proved theorem. -/
def BackwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 33 → V, InternalZero (SharingSeed32Sextic.seed p) v →
    InternalZero (SharingSeed31Sextic.seed p) (drop v)
end DiophantineConsistency.SharingSeed31BridgeDraft
