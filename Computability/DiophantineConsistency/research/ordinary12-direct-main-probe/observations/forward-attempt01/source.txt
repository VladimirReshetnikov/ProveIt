import DirectMainGraph

/-! Forward positive witness transport from XQ91 to the direct graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectMainForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)
def transform (v : Fin 12 → V) : Fin 12 → V := Function.update v 11 (v 11+v 5)

theorem lift_cast (v : Fin 12 → V) :
    (fun i => ι (transform v i)) = liftG (fun i => ι (v i)) := by
  funext i
  by_cases h : i = 11
  · subst i
    simp [transform, liftG, map_add]
  · simp [transform, liftG, h]

theorem zero_iff (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (graph (integerPorts p)).output (transform v) ↔
      InternalZero (FreeJXQ91.graph (integerPorts p)).output v := by
  let a := (graph (integerPorts p)).first
  let b := (graph (integerPorts p)).main
  let c := (graph (integerPorts p)).ordinary
  let a' := (FreeJXQ91.graph (integerPorts p)).first
  let b' := (FreeJXQ91.graph (integerPorts p)).main
  let c' := (FreeJXQ91.graph (integerPorts p)).ordinary
  have hout : (graph (integerPorts p)).output = a*a+b*b+c*c := by rfl
  have hout' : (FreeJXQ91.graph (integerPorts p)).output = a'*a'+b'*b'+c'*c' := by rfl
  rw [internalZero_iff, internalZero_iff, lift_cast, hout, hout']
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [first_eval, main_eval, ordinary_eval]

theorem transform_pos (v : Fin 12 → V) (hv : ∀j,0<v j) : ∀j,0<transform v j := by
  intro j
  by_cases h : j=11
  · subst j
    simpa [transform] using add_pos (hv 11) (hv 5)
  · simpa [transform,h] using hv j

theorem exists_direct_of_xq91 (p : Fin 4 → ℕ)
    (h : ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJXQ91.graph (integerPorts p)).output v) :
    ∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v := by
  obtain ⟨v,hv,hz⟩ := h
  exact ⟨transform v,transform_pos v hv,(zero_iff p v).mpr hz⟩

#print axioms DirectMainForward.zero_iff
#print axioms DirectMainForward.transform_pos
#print axioms DirectMainForward.exists_direct_of_xq91
end DirectMainForward
