import DiophantineConsistency.ArithmeticPellKnownUnit

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellKnownUnitChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellKnownUnit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- One bounded minimum is chosen for all solutions, not separately per query. -/
example (D A S : V) (hD : 0<D) (hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) :
    ∃ b v : V, 0<v ∧ b+2≤A ∧ v≤S ∧
      (b+2)*(b+2)=1+D*v*v ∧
      ∀ x y : V, x*x=1+D*y*y →
        ∃ n : V, n≤y ∧ x=xcoord n b ∧ y=v*ycoord n b :=
  known_unit_classification D A S hD hA hS hseed

/-- The two known solutions use the identical base and ordinate scale. -/
example (D A S f t : V) (hD : 0<D) (hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) (hother : f*f=1+D*t*t) :
    ∃ b v e n : V, 0<v ∧ e≤S ∧ n≤t ∧
      A=xcoord e b ∧ S=v*ycoord e b ∧ f=xcoord n b ∧ t=v*ycoord n b := by
  obtain ⟨b,v,hv,_,_,_,hall⟩ := known_unit_classification D A S hD hA hS hseed
  obtain ⟨e,he,hA',hS'⟩ := hall A S hseed
  obtain ⟨n,hn,hf,ht⟩ := hall f t hother
  exact ⟨b,v,e,n,hv,he,hn,hA',hS',hf,ht⟩

/-- Zero ordinate is included and forces the bounded index to be zero. -/
example (D A S : V) (hD : 0<D) (hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) :
    ∃ b v : V, 0<v ∧ (1:V)=xcoord 0 b ∧ (0:V)=v*ycoord 0 b := by
  obtain ⟨b,v,hv,_,_,_,hall⟩ := known_unit_classification D A S hD hA hS hseed
  obtain ⟨n,hn,hx,hy⟩ := hall 1 0 (by simp)
  have hn0 : n=0 := le_antisymm hn (Arithmetic.zero_le n)
  exact ⟨b,v,hv,by simpa only [hn0] using hx,by simpa only [hn0] using hy⟩

/-- The minimality helper quantifies over solutions outside the seed box. -/
example (D A S x y : V) (hD : 0<D) (hA : 1<A) (hS : 0<S)
    (hseed : A*A=1+D*S*S) (hy : 0<y) (hn : x*x=1+D*y*y) :
    ∃ v : V, 0<v ∧ v≤S ∧ v≤y := by
  obtain ⟨F,v,_,hv,_,hvS,_,hmin⟩ := least_unit D A S hD hA hS hseed
  exact ⟨v,hv,hvS,hmin x y hy hn⟩

#print axioms least_unit
#print axioms minimal_unit_descent
#print axioms minimal_unit_classification
#print axioms known_unit_classification
end DiophantineConsistency.ArithmeticPellKnownUnitChecks
