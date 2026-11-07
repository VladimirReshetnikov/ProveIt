import DiophantineConsistency.SharingSeed26Sextic
import DiophantineConsistency.SharingSeed27Sextic

/-! SOURCE-ONLY definitions and open targets; no zero-set theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingSeed26BridgeDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

def lift {S : Type*} (gap : S) (v : Fin 27 → S) : Fin 28 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, gap, v 22, v 23, v 24, v 25, v 26]

def drop {S : Type*} (v : Fin 28 → S) : Fin 27 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 23, v 24, v 25, v 26, v 27]

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def ringGap (p : Fin 4 → ℤ) (v : Fin 27 → V) : DiffRing V :=
  let a := ((p 0 : ℤ) : DiffRing V) * (ι (v 1) + 1)
  a * (a + 1) + (ι (v 3) + 1) - a * (ι (v 2) + 1)

/-- Open proposition; representability and port assumptions are explicit. -/
def ForwardTarget (p : Fin 4 → ℤ) (beta K : V) : Prop :=
  ((p 0 : ℤ) : DiffRing V) = ι beta →
  ((p 1 : ℤ) : DiffRing V) = ι K → 1 ≤ beta →
  ∀ v : Fin 27 → V, InternalZero (SharingSeed26Sextic.seed p) v →
    ∃ gap : V, ι gap = ringGap p v ∧ InternalZero (SharingSeed27Sextic.seed p) (lift gap v)

/-- Open proposition; no zero-set theorem is asserted. -/
def BackwardTarget (p : Fin 4 → ℤ) : Prop :=
  ∀ v : Fin 28 → V, InternalZero (SharingSeed27Sextic.seed p) v →
    InternalZero (SharingSeed26Sextic.seed p) (drop v)
end DiophantineConsistency.SharingSeed26BridgeDraft
