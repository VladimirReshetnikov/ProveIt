import DiophantineConsistency.ArithmeticPellAuxiliarySeed

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticPellAuxiliarySeedChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellAuxiliarySeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (a I f t : V) (hI : 2≤I) (hf : 0<f)
    (hn : I*I+delta a=delta a*f*f) :
    (oddQuotient (2*t+1) (I-2)+ycoord (2*(2*t+1)+1) a)%(f*f)=0 :=
  (quotient_square_pair a I f t hI hf hn).2

example (I c t : V) (hI : 2≤I) (hc : 0<c) (hd : c∣I) :
    (oddQuotient (2*t+1) (I-2)+(4*t+3))%c=0 :=
  (quotient_divisor_pair I c t hI hc hd).2

example (R : V) (hphase : R%4=3) :
    R=2*((R-1)/2)+1 ∧ (R-1)/2=2*(R/4)+1 :=
  (phase_indices R hphase).2

-- Only the actual phase is supplied: both norms and the T identity are outputs.
example (a R : V) (hphase : R%4=3) :
    let c:=ycoord R a
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      f=xcoord (R*c) a ∧ ycoord (R*c) a=i*c*c ∧
      f*f=1+delta a*(i*c*c)*(i*c*c) ∧
      let I:=delta a*i*c*c
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      u=oddQuotient ((R-1)/2) (I-2) ∧
      (u+c)%(f*f)=0 ∧ (u+R)%c=0 ∧
      f*f*c*T=u+c+f*f*R ∧ u=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*u*u+y*y=1+I*I*y*y := auxiliary_seed a R hphase

-- Offset zero is legal; no positive-base-offset or large-ordinate hypothesis.
example (R : V) (hphase : R%4=3) :
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      let c:=ycoord R 0
      let I:=delta (0:V)*i*c*c
      f*f*c*T=u+c+f*f*R ∧ I*I*u*u+y*y=1+I*I*y*y := by
  obtain ⟨f,i,T,u,y,hf,hi,hT,hu,hy,_,_,_,_,_,_,_,_,hTdef,_,hn⟩ :=
    auxiliary_seed (0:V) R hphase
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hTdef,hn⟩

-- No numerical Pell expansion: the smallest admitted rank remains internal.
example : ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y := by
  have hp : (3:V)%4=3 := mod_eq_self_of_lt (by
    simpa only [show (3:V)+1=4 by ring] using lt_add_one (3:V))
  obtain ⟨f,i,T,u,y,hf,hi,hT,hu,hy,_⟩ := auxiliary_seed (0:V) 3 hp
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy⟩

#print axioms quotient_square_pair
#print axioms quotient_divisor_pair
#print axioms phase_indices
#print axioms positive_quotient
#print axioms auxiliary_seed
end DiophantineConsistency.ArithmeticPellAuxiliarySeedChecks
