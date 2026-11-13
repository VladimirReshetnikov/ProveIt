import DiophantineConsistency.ModelBSeed
import DiophantineConsistency.ArithmeticPellAuxiliarySeed

/-! A draft model-level auxiliary Pell seed with an extra multiplier. This is
not the signed carrier construction, 69-operation converse or iPRA theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBAuxiliary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellHalfIndex
open DiophantineConsistency.ArithmeticPellAuxiliarySeed
open ModelBSeed
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] xcoord ycoord oddQuotient

/-- Draft: strong and auxiliary Pell seeds at a rank in phase 3 mod 4,
including an arbitrary extra positive factor in the strong ordinate. -/
theorem auxiliary_seed_with_multiplier (a R b : V) (hb : 0<b) (hphase : R%4=3) :
    let c := ycoord R a
    ∃ f i T u y : V, 0<f ∧ 0<i ∧ 0<T ∧ 0<u ∧ 0<y ∧
      f*f=1+delta a*(b*i*c*c)*(b*i*c*c) ∧
      let I:=delta a*(b*i*c*c)
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      u=oddQuotient ((R-1)/2) (I-2) ∧
      (u+c)%(f*f)=0 ∧ (u+R)%c=0 ∧
      f*f*c*T=u+c+f*f*R ∧ u=absdiff (f*f*c*T) (f*f*R+c) ∧
      I*I*u*u+y*y=1+I*I*y*y := by
  let c := ycoord R a
  obtain ⟨hR,hodd,hhalf⟩ := phase_indices R hphase
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
  obtain ⟨t,f,i,ht,hf,hi,hfx,hyic,hn⟩ := strong_seed_with_multiplier a b c hb hc
  change f*f=1+delta a*(b*i*c*c)*(b*i*c*c) at hn
  let I:=delta a*(b*i*c*c)
  have hd : 2≤delta a := by
    unfold delta
    calc
      (2:V)≤a+3 := le_trans (le_of_lt (by
        simpa only [show (2:V)+1=3 by ring] using lt_add_one (2:V))) (by simp)
      _≤(a+1)*(a+3) := le_mul_of_one_le_left (by simp) (by simp)
  have hi1 : 1≤b*i*c*c := one_le_mul (one_le_mul (one_le_mul
    (pos_iff_one_le.mp hb) (pos_iff_one_le.mp hi))
    (pos_iff_one_le.mp hc)) (pos_iff_one_le.mp hc)
  have hI : 2≤I := le_trans hd (by
    simpa only [I,mul_assoc] using le_mul_of_one_le_right (by simp : (0:V)≤delta a) hi1)
  have hbI : I-2+2=I := tsub_add_cancel_of_le hI
  have hnorm : I*I+delta a=delta a*f*f := by
    calc
      I*I+delta a=delta a*(1+delta a*(b*i*c*c)*(b*i*c*c)) := by dsimp [I]; ring
      _=delta a*f*f := by rw [←hn]; ring
  have hIc : c∣I := ⟨delta a*b*i*c,by dsimp [I]; ring⟩
  let u:=oddQuotient ((R-1)/2) (I-2)
  let y:=ycoord R (I-2)
  have hux : xcoord R (I-2)=I*u := by
    simpa only [u, ←hodd,hbI] using odd_exact ((R-1)/2) (I-2)
  have hu : 0<u := by
    apply pos_of_mul_pos_right (a := I) _ (by simp)
    rw [←hux]
    exact lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x R (I-2))
  have hy : 0<y := lt_of_lt_of_le hR (time_le_y R (I-2))
  have hphaseindex : 2*(2*(R/4)+1)+1=R := by
    calc
      2*(2*(R/4)+1)+1=2*((R-1)/2)+1 := by rw [hhalf]
      _=R := hodd.symm
  have huf : (u+c)%(f*f)=0 := by
    simpa only [u,hhalf,hphaseindex] using (quotient_square_pair a I f (R/4) hI hf hnorm).2
  have huc : (u+R)%c=0 := by
    have hh := (quotient_divisor_pair I c (R/4) hI hc hIc).2
    have hfour : 4*(R/4)+3=R := by simpa only [hphase] using div_add_mod R 4
    simpa only [u,hhalf,hfour] using hh
  have hfc : f*f=1+c*(delta a*b*b*i*i*c*c*c) := by rw [hn]; ring
  obtain ⟨T,hT,hliteral,habsolute⟩ := positive_quotient c f R u _ hc hu hfc huf huc
  have hdelta : delta (I-2)+1=I*I := by
    calc
      delta (I-2)+1=(I-2+2)*(I-2+2) := by unfold delta; ring
      _=I*I := by rw [hbI]
  have haux : I*I*u*u+y*y=1+I*I*y*y := by
    have hh := norm R (I-2)
    change xcoord R (I-2)*xcoord R (I-2)=1+delta (I-2)*y*y at hh
    calc
      I*I*u*u+y*y=(I*u)*(I*u)+y*y := by ring
      _=1+(delta (I-2)+1)*y*y := by rw [←hux,hh]; ring
      _=1+I*I*y*y := by rw [hdelta]
  exact ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hn,rfl,hux,rfl,huf,huc,hliteral,habsolute,haux⟩
end ModelBAuxiliary
#print axioms ModelBAuxiliary.auxiliary_seed_with_multiplier
