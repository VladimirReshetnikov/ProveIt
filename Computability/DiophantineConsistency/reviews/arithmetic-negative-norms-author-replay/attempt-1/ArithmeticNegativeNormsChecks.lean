import DiophantineConsistency.ArithmeticNegativeNorms

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticNegativeNormsChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticNegativeNorms
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (x t : V) : x*x+t*t+1≠0*0*t*t := square_discriminant_ne_negative 0 x t
example (x t : V) : x*x+t*t+1≠1*1*t*t := square_discriminant_ne_negative 1 x t
example (A x : V) : x*x+0*0+1≠A*A*0*0 := square_discriminant_ne_negative A x 0

/-- The n≥2 hypothesis cannot be dropped. -/
example : (1:V)*1+1=1*(1+1)*1*1 := by ring

example (n x : V) (hn : 2≤n) : x*x+1≠n*(n+1)*0*0 := consecutive_ne_negative n x 0 hn

example (n x y : V) (hn : 2≤n) :
    (x*x+1=n*(n+1)*y*y) →
      ∃ u v : V, 0<v ∧ v<y ∧ u≤(n+1)*v ∧ u*u+1=n*(n+1)*v*v :=
  consecutive_negative_descent n x y hn

example (a d c f i S v y : V) :
    d*d+1≠((a+1)*(a+3))*c*c ∧
    f*f+1≠((a+1)*(a+3))*(i*c*c)*(i*c*c) ∧
    (S*v)*(S*v)+y*y+1≠S*S*y*y :=
  ⟨main_ne_negative a d c,strong_ne_negative a f i c,square_aux_ne_negative S v y⟩

#print axioms square_mod_four
#print axioms square_discriminant_ne_negative
#print axioms consecutive_negative_descent
#print axioms consecutive_ne_negative
#print axioms main_ne_negative
#print axioms strong_ne_negative
#print axioms square_aux_ne_negative
end DiophantineConsistency.ArithmeticNegativeNormsChecks
