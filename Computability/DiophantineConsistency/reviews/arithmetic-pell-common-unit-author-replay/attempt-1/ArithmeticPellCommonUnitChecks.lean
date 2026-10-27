import DiophantineConsistency.ArithmeticPellCommonUnit

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellCommonUnitChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCommonUnit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No standardness or positivity condition is imposed on the query index. -/
example (a b e p : V) (hA : a+2=xcoord e b) :
    xcoord p a=xcoord (e*p) b ∧
      ycoord p a*ycoord e b=ycoord (e*p) b := composition a b e hA p

/-- The zero query is retained by the same composition theorem. -/
example (a b e : V) (hA : a+2=xcoord e b) :
    xcoord 0 a=xcoord (e*0) b ∧
      ycoord 0 a*ycoord e b=ycoord (e*0) b := composition a b e hA 0

/-- One actual norm, one common unit and both internal classified indices. -/
example (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R+delta a=delta a*(f*f)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b :=
  common_unit_setup a R f hR hf hn

/-- All query indices share the actual witnesses returned from the norm. -/
example (a R f : V) (hR : 0<R) (hf : 0<f)
    (hn : R*R=delta a*(f*f-1)) :
    ∃ b e n S : V, 0<e ∧ 0<n ∧ 0<S ∧ S<a+2 ∧
      S=ycoord e b ∧ a+2=xcoord e b ∧ f=xcoord n b ∧
      delta a=delta b*S*S ∧ R=delta b*S*ycoord n b ∧
      ∀ p : V, xcoord p a=xcoord (e*p) b ∧
        ycoord p a*S=ycoord (e*p) b :=
  common_unit_tsub a R f hR hf hn

#print axioms composition
#print axioms common_unit_setup
#print axioms common_unit_composition
#print axioms common_unit_tsub
end DiophantineConsistency.ArithmeticPellCommonUnitChecks
