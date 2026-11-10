import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! Phase-three auxiliary seed at an arbitrary supplied strong Pell root. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveGeneralAuxiliarySeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellHalfIndex ArithmeticPellAuxiliarySeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem auxiliary_of_strong (a c R f I H : V)
    (hphase : R%4=3) (hc : 0<c) (hc_eq : c=ycoord R a) (hI : 2≤I) (hf : 0<f)
    (hnorm : I*I+ArithmeticPellRecurrence.delta a=ArithmeticPellRecurrence.delta a*f*f)
    (hIc : c∣I) (hfc : f*f=1+c*H) :
    ∃ T u y : V, 0<T ∧ 0<u ∧ 0<y ∧
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      f*f*c*T=u+c+f*f*R ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  obtain ⟨hR,hodd,hhalf⟩ := phase_indices R hphase
  have hb : I-2+2=I := tsub_add_cancel_of_le hI
  let u:=oddQuotient ((R-1)/2) (I-2)
  let y:=ycoord R (I-2)
  have hux : xcoord R (I-2)=I*u := by
    simpa only [u,←hodd,hb] using odd_exact ((R-1)/2) (I-2)
  have hu : 0<u := by
    apply pos_of_mul_pos_right (a:=I) _ (by simp)
    rw [←hux]
    exact lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x R (I-2))
  have hy : 0<y := lt_of_lt_of_le hR (time_le_y R (I-2))
  have hphaseindex : 2*(2*(R/4)+1)+1=R := by
    calc
      2*(2*(R/4)+1)+1=2*((R-1)/2)+1 := by rw [hhalf]
      _=R := hodd.symm
  have huf : (u+c)%(f*f)=0 := by
    simpa only [u,hhalf,hphaseindex,←hc_eq] using (quotient_square_pair a I f (R/4) hI hf hnorm).2
  have huc : (u+R)%c=0 := by
    have hh := (quotient_divisor_pair I c (R/4) hI hc hIc).2
    have hfour : 4*(R/4)+3=R := by simpa only [hphase] using div_add_mod R 4
    simpa only [u,hhalf,hfour] using hh
  obtain ⟨T,hT,hliteral,_habs⟩ := positive_quotient c f R u H hc hu hfc huf huc
  have hdelta : ArithmeticPellRecurrence.delta (I-2)+1=I*I := by
    calc
      ArithmeticPellRecurrence.delta (I-2)+1=(I-2+2)*(I-2+2) := by unfold ArithmeticPellRecurrence.delta; ring
      _=I*I := by rw [hb]
  have haux : I*I*u*u+y*y=1+I*I*y*y := by
    have hh := norm R (I-2)
    rw [hux] at hh
    change (I*u)*(I*u)=1+ArithmeticPellRecurrence.delta (I-2)*y*y at hh
    have he := congrArg (fun z : V => z+y*y) hh
    calc
      I*I*u*u+y*y=(I*u)*(I*u)+y*y := by ring
      _=1+ArithmeticPellRecurrence.delta (I-2)*y*y+y*y := he
      _=1+(ArithmeticPellRecurrence.delta (I-2)+1)*y*y := by ring
      _=1+I*I*y*y := by rw [hdelta]
  exact ⟨T,u,y,hT,hu,hy,rfl,hux,hliteral,haux⟩

#print axioms TenPositiveGeneralAuxiliarySeed.auxiliary_of_strong
end TenPositiveGeneralAuxiliarySeed
