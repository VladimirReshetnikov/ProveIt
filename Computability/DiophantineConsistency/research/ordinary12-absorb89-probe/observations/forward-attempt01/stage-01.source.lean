import Absorb89Graph

/-! Forward positive witness transport from the 90-row graph to the 89-row graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Absorb89Forward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)
def transform (v : Fin 12 → V) : Fin 12 → V := Function.update v 7 (v 7+v 6)

theorem lift_cast (v : Fin 12 → V) :
    (fun i => ι (transform v i)) = liftR (fun i => ι (v i)) := by
  funext i
  by_cases h : i = 7
  · subst i
    simp [transform, liftR, map_add]
  · simp [transform, liftR, h]

theorem zero_iff (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (graph (integerPorts p)).output (transform v) ↔
      InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output v := by
  let a := (graph (integerPorts p)).first
  let b := (graph (integerPorts p)).main
  let c := (graph (integerPorts p)).ordinary
  let a' := (FreeJDirectMainGraph.graph (integerPorts p)).first
  let b' := (FreeJDirectMainGraph.graph (integerPorts p)).main
  let c' := (FreeJDirectMainGraph.graph (integerPorts p)).ordinary
  have hout : (graph (integerPorts p)).output = a*a+b*b+c*c := by rfl
  have hout' : (FreeJDirectMainGraph.graph (integerPorts p)).output = a'*a'+b'*b'+c'*c' := by rfl
  rw [internalZero_iff, internalZero_iff, lift_cast, hout, hout']
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [first_eval, main_eval, ordinary_eval]

theorem transform_pos (v : Fin 12 → V) (hv : ∀j,0<v j) : ∀j,0<transform v j := by
  intro j
  by_cases h : j=7
  · subst j
    simpa [transform] using add_pos (hv 7) (hv 6)
  · simpa [transform,h] using hv j

theorem exists_absorb_of_direct (p : Fin 4 → ℕ)
    (h : ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output v) :
    ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨transform v,transform_pos v hv,(zero_iff p v).mpr hz⟩

#print axioms Absorb89Forward.zero_iff
#print axioms Absorb89Forward.transform_pos
#print axioms Absorb89Forward.exists_absorb_of_direct
end Absorb89Forward
