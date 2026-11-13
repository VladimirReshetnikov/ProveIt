import DiophantineConsistency.BFS943.Direct80Adjacent

/-! Signed integral quotient of the actual 80-graph carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80SignedCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80Adjacent
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_signed_carrier (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    let D := delta p v
    let U0 := U p v
    let E0 := E p v
    let a := D*U0*U0*E0
    let Q := D*(4*a*(1+a))
    ∃ tau f V0 y : V, ∃ z : DiffRing V,
      0<tau ∧ 0<f ∧ 0<V0 ∧ 0<y ∧ E0=tau*tau ∧ 1+a=f*f ∧
      (graph (integerPorts p)).v.evalRing (fun j => ι (v j))*
        (graph (integerPorts p)).v.evalRing (fun j => ι (v j))=ι (V0*V0) ∧
      (graph (integerPorts p)).z.evalRing (fun j => ι (v j))=ι (M p v)*z ∧
      (z=ι (tau*f*y) ∨ z= -ι (tau*f*y)) ∧ z≤ι (tau*f*y) ∧
      Q*(V0*V0)=1+(Q-1)*(y*y) := by
  obtain ⟨tau,f,V0,Z0,y,htau,hf,hV,hy,he,hf2,hVsq,hZsq,hZeq,haux⟩ := graph_adjacent p v hb hv hz
  let Z : DiffRing V := (graph (integerPorts p)).z.evalRing (fun j => ι (v j))
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  rcases mul_eq_zero.mp hfactor with h|h
  · have heq : Z=mz := sub_eq_zero.mp h
    refine ⟨tau,f,V0,y,ι (tau*f*y),htau,hf,hV,hy,he,hf2,hVsq,?_,Or.inl rfl,le_rfl,haux⟩
    exact heq
  · have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
    refine ⟨tau,f,V0,y,-ι (tau*f*y),htau,hf,hV,hy,he,hf2,hVsq,?_,Or.inr rfl,?_,haux⟩
    · dsimp [mz] at heq
      simpa only [mul_neg] using heq
    · exact neg_le_self (ι_nonneg _)

#print axioms TenPositive80SignedCarrier.graph_signed_carrier
end TenPositive80SignedCarrier
