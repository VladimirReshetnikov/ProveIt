import P64QCube72FreeBinding
import FreeMainGraphForward

/-! Unchecked draft: positive 76Y zero gives a positive 72-free-main zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube72FreeForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube76Y.graph (fun j => (p j : ℤ))).output v) :
    ∃ u : Fin 14 → V, (∀ i, 0 < u i) ∧
      InternalZero (P64QCube72Free.graph (fun j => (p j : ℤ))).output u := by
  let pp : Fin 4 → ℤ := fun j => (p j : ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  obtain ⟨h, hpos, hh⟩ := FreeMainGraphForward.exists_positive_main_gap p v hv hz
  let u := Function.update v 13 h
  have hup : ∀ i, 0 < u i := by
    intro i
    by_cases hi : i = 13
    · subst i; simpa [u] using hpos
    · simpa [u, hi] using hv i
  have hgap : (ι h : DiffRing V) = P64QCube72FreeBinding.gap pp z := by
    dsimp [P64QCube72FreeBinding.gap, pp, z]
    rw [← P64QCubeMap.lift_cast p v]
    simpa [P64QCubeMap.lift] using hh
  have hcast : (fun i => (ι (u i) : DiffRing V)) =
      P64QCube72FreeBinding.liftRing pp z := by
    funext i
    by_cases hi : i = 13
    · subst i; simpa [u, P64QCube72FreeBinding.liftRing] using hgap
    · simp [u, P64QCube72FreeBinding.liftRing, hi, z]
  refine ⟨u, hup, ?_⟩
  rw [internalZero_iff] at hz ⊢
  change (P64QCube72Free.graph pp).output.evalRing (fun i => ι (u i)) = 0
  rw [hcast, P64QCube72FreeBinding.output]
  exact hz

#print axioms P64QCube72FreeForward.exists_zero
end P64QCube72FreeForward
