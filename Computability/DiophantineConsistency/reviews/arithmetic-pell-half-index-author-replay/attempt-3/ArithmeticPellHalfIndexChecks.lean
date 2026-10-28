import DiophantineConsistency.ArithmeticPellHalfIndex

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellHalfIndexChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (b : V) : oddQuotient 0 b=1 := odd_zero b

example (a I f : V) (hI : 2≤I) (hf : 0<f)
    (hn : I*I+delta a=delta a*f*f) :
    SignMod f (oddQuotient 1 (I-2)) (ycoord 3 a) := by
  simpa only [show (2:V)*1+1=3 by ring] using quotient_mod_norm a I f 1 hI hf hn

example (I c : V) (hI : 2≤I) (hc : 0<c) (hd : c∣I) :
    SignMod c (oddQuotient 1 (I-2)) 3 := by
  simpa only [show (2:V)*1+1=3 by ring] using quotient_mod_divisor I c 1 hI hc hd

example (x : V) : absdiff x x=0 := by simp [absdiff]
example (x y : V) : absdiff x y=absdiff y x := by unfold absdiff; ring

example (a c d f i R y u : V)
    (hc : 0<c) (hi : 0<i) (hf : 0<f) (hR : 0<R) (hy : 0<y)
    (hmain : d*d=1+delta a*c*c)
    (hstrong : (i*c*c)*(i*c*c)+delta a=delta a*f*f)
    (hbig : (a+2)*delta a*delta a<c) (hhalf : 2*R<c)
    (haux : (i*c*c)*(i*c*c)*u*u+y*y=1+(i*c*c)*(i*c*c)*y*y)
    (huf : (u+c)%f=0) (huc : (u+R)%c=0) : c=ycoord R a :=
  (half_index a c d f i R y u hc hi hf hR hy hmain hstrong hbig hhalf haux
    (Or.inr huf) (Or.inr huc)).2

#print axioms odd_x_dvd
#print axioms odd_exact
#print axioms odd_rec
#print axioms quotient_mod_norm
#print axioms quotient_mod_divisor
#print axioms sign_square
#print axioms twice_index_lt_y
#print axioms half_index
#print axioms absdiff_residue
#print axioms literal_half_index
end DiophantineConsistency.ArithmeticPellHalfIndexChecks
