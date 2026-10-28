import DiophantineConsistency.ArithmeticPellFirstIndex

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellFirstIndexChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellFirstIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a b : V) (h : a≤b) : xcoord 0 a≤xcoord 0 b ∧ ycoord 0 a≤ycoord 0 b :=
  base_mono a b h 0

example (a b t : V) (h : a≤b) : ycoord t a≤ycoord t b := (base_mono a b h t).2

example : ycoord (6:V) 0=780 := by
  rw [y_six]
  unfold delta
  ring

/-- Restore the omitted positive coordinate without supplying an index. -/
example (E Y k eta N d f i R y T : V)
    (hE : 0<E) (hY : 2≤Y) (hk : 0<k) (heta : 0<eta) (hN : 0<N)
    (hf : 0<f) (hi : 0<i) (hy : 0<y) (hR8 : 8≤R) (hRE : R+2<E)
    (hfirst : (E*N+k-R)*(E*N+k-R)=1+(E*Y)*(E*Y+1)*k*k)
    (hmain : d*d=1+delta (E+Y)*(k*Y+eta)*(k*Y+eta))
    (hstrict : f*f=1+delta (E+Y)*(i*(k*Y+eta)*(k*Y+eta))*(i*(k*Y+eta)*(k*Y+eta)))
    (haux : let c:=k*Y+eta
      let I:=delta (E+Y)*i*c*c
      let u:=absdiff (f*f*c*T) (f*f*R+c)
      I*I*u*u+y*y=1+I*I*y*y) :
    ∃ h : V, 0<h ∧ k=R+1+E*h := by
  obtain ⟨_,h,_,_,_,_,_,_,_,_,_,hh,hk'⟩ :=
    first_main_indices E Y k eta N d f i R y T hE hY hk heta hN hf hi hy hR8 hRE hfirst hmain hstrict haux
  refine ⟨4*Y*h,mul_pos (mul_pos (by simp) (lt_of_lt_of_le (by simp : (0:V)<2) hY)) hh,?_⟩
  rw [hk']
  ring

/-- Port lower bounds and positivity of K are not needed for this scalar step. -/
example (q beta J F alpha z w s : V)
    (hb : 0<beta) (hJ : 0<J) (hF : 0<F) (ha : 0<alpha)
    (hz : 0<z) (hw : 0<w) (hs : 0<s) (hq : q=beta*J+1)
    (ht : w*q+q=w*(F+alpha)+F+z*(q-1)+1) :
    24≤((q-1)*(q-F)+alpha)*(q^2-1) := by
  have hMF : (0:V)<2*beta := mul_pos (by simp) hb
  have h:=scalar_window q beta 0 0 0 J F alpha z w s hb hJ hF ha hz hw hs hb hMF hq
    (by simpa only [zero_add] using ht)
  simpa only [mul_zero,zero_add,add_zero] using h.2.1

#print axioms base_mono
#print axioms y_six
#print axioms first_main_indices
#print axioms scalar_window
#print axioms maintained_first_indices
end DiophantineConsistency.ArithmeticPellFirstIndexChecks
