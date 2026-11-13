import Direct80To90FullZero

/-! Actual output-zero wrapper for the shared positive witness. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80To90Output
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open CompactFixedBeta CompactSymbolicPorts TenPositive80Graph TenPositive80Factors
open TenPositive80To90FullZero
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_exists_zero (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ w : Fin 12 → V, (∀j,0<w j) ∧
      InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output w := by
  obtain ⟨w,hw,hfirst,hmain,hordinary⟩ := graph_factors p v hp0 hp2 hp3 hv hz
  refine ⟨w,hw,?_⟩
  apply (internalZero_iff _ _).mpr
  have hout : (FreeJDirectMainGraph.graph (integerPorts p)).output =
      (FreeJDirectMainGraph.graph (integerPorts p)).first*(FreeJDirectMainGraph.graph (integerPorts p)).first+
      (FreeJDirectMainGraph.graph (integerPorts p)).main*(FreeJDirectMainGraph.graph (integerPorts p)).main+
      (FreeJDirectMainGraph.graph (integerPorts p)).ordinary*(FreeJDirectMainGraph.graph (integerPorts p)).ordinary := by rfl
  rw [hout]
  simp only [Expr.evalRing_add,Expr.evalRing_mul,hfirst,hmain,hordinary,zero_mul,add_zero]

#print axioms TenPositive80To90Output.graph_exists_zero
end TenPositive80To90Output
