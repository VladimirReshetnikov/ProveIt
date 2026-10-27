import DiophantineConsistency.ArithmeticPellIndexDivisibility

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellIndexDivisibilityChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticGcdNormalization ArithmeticPellIndexDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a : V) : Bez (ycoord 0 a) (delta a) 0 := index_certificate a 0
example (a : V) : Bez (ycoord 1 a) (delta a) 1 := index_certificate a 1
example (a j : V) :
    (∃u v : V, xcoord j a=1+delta a*u ∧ ycoord j a=(a+2)*j+delta a*v) ∨
    (∃u v : V, xcoord j a=a+2+delta a*u ∧ ycoord j a=j+delta a*v) :=
  quotient_alternatives a j

example (x y g : V) (h : Bez x y g) : Bez (0*x) y (0*g) :=
  certificate_scale_left h 0
example (x y g : V) (h : Bez x y g) : Bez x (0*y) (0*g) :=
  certificate_scale_right h 0

example (a m : V) (hm : (0:V)∣m) : ycoord 0 a∣m := by
  have hz : m=0 := by simpa using hm
  subst m
  exact ordinate_divides_index a 0 0 (dvd_zero 0) (by simp)
example (a p : V) : ycoord p a∣0 :=
  ordinate_divides_index a p 0 (dvd_zero p) (by simp)

example (a c p i f : V) (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hc : c=ycoord p a) (hn : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))
    (hb : (a+2)*delta a*delta a<c) :
    ∃m : V, 0<m ∧ f=xcoord m a ∧ p∣m ∧ c∣m ∧ i*c*c=delta a*ycoord m a :=
  relaxed_auxiliary a c p i f hp hi hf hc hn hb

example (a c p i f : V) (hp : 0<p) (hi : 0<i) (hf : 0<f)
    (hc : c=ycoord p a) (hn : (i*c*c)*(i*c*c)=delta a*(f*f-1))
    (hb : (a+2)*delta a*delta a<c) :
    ∃m : V, 0<m ∧ f=xcoord m a ∧ p∣m ∧ c∣m ∧ i*c*c=delta a*ycoord m a :=
  relaxed_auxiliary_tsub a c p i f hp hi hf hc hn hb

#print axioms quotient_alternatives
#print axioms index_certificate
#print axioms certificate_scale_left
#print axioms certificate_scale_right
#print axioms ordinate_divides_index
#print axioms relaxed_auxiliary
#print axioms relaxed_auxiliary_tsub
end DiophantineConsistency.ArithmeticPellIndexDivisibilityChecks
