import DiophantineConsistency.SharingSeed27Sextic
import DiophantineConsistency.SharingSeed28Sextic

/-! SOURCE-ONLY definitions and open targets; no zero-set theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSeed27BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

def lift {S : Type*} [CommSemiring S] (v : Fin 28 → S) : Fin 29 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21 + 1, v 21 * (v 21 + 2), v 22, v 23, v 24, v 25, v 26, v 27]

/-- Drop is parameterized by a candidate predecessor, with no predecessor existence assumed. -/
def drop {S : Type*} (u : S) (v : Fin 29 → S) : Fin 28 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, u, v 23, v 24, v 25, v 26, v 27, v 28]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Open proposition; not a proved theorem. -/
def ForwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 28 → V, InternalZero (SharingSeed27Sextic.seed p) v →
    InternalZero (SharingSeed28Sextic.seed p) (lift v)

/-- Open proposition; predecessor and deleted coordinate are both explicit. -/
def BackwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 29 → V, InternalZero (SharingSeed28Sextic.seed p) v →
    ∃ u : V, v 21 = u + 1 ∧ v 22 = u * (u + 2) ∧
      InternalZero (SharingSeed27Sextic.seed p) (drop u v)
end DiophantineConsistency.SharingSeed27BridgeDraft
