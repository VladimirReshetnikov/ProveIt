import DiophantineConsistency.ModelBAuxiliary
import DiophantineConsistency.ModelBNegativeResidue
import DiophantineConsistency.ModelBPositiveCarrier

/-! Draft assembly of the multiplied strong seed, signed ordinate residue,
and positive auxiliary carrier. This is not a graph or iPRA theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBFreshPrivate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ModelDifferenceRing
open ModelBAuxiliary ModelBNegativeResidue ModelBPositiveCarrier
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Candidate fresh private model witnesses at rank phase three, conditional
on an already positive retained transport G with b dividing G. -/
theorem fresh_private (a R b G : V) (hb : 0<b) (hphase : R%4=3)
    (hG : 0<G) (hGdiv : b∣G) :
    let c:=ycoord R a
    ∃ f i T u y m : V, 0 < f ∧ 0 < i ∧ 0 < T ∧ 0 < u ∧ 0 < y ∧ 0 < m ∧
      f*f=1+delta a*(b*i*c*c)*(b*i*c*c) ∧
      let I:=delta a*(b*i*c*c)
      y=ycoord R (I-2) ∧ xcoord R (I-2)=I*u ∧
      (u+c)%(f*f)=0 ∧ (u+R)%c=0 ∧
      f*f*c*T=u+c+f*f*R ∧
      I*I*u*u+y*y=1+I*I*y*y ∧
      -(ι y : DiffRing V)=1+4*(ι b*(ι m-(ι u)^2*ι G)-ι G) := by
  let c:=ycoord R a
  obtain ⟨f,i,T,u,y,hf,hi,hT,hu,hy,hn,hyy,hxu,huq,huf,huc,hliteral,habs,haux⟩ :=
    auxiliary_seed_with_multiplier a R b hb hphase
  let I:=delta a*(b*i*c*c)
  have hR : 0<R := by
    have he : R=4*(R/4)+3 := by simpa only [hphase] using (div_add_mod R 4).symm
    rw [he]
    simp
  have hc : 0<c := lt_of_lt_of_le hR (time_le_y R a)
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
  have hbI : b∣I := ⟨delta a*i*c*c, by dsimp [I]; ring⟩
  obtain ⟨h,hh⟩ := ordinate_plus_one_dvd I R b hI hbI hphase
  have hydiv : 4*b∣y+1 := ⟨h, by rw [hyy]; exact hh⟩
  obtain ⟨m,hm,hym⟩ := positive_carrier I u y b G hI hu hy hb hG hGdiv hydiv haux
  exact ⟨f,i,T,u,y,m,hf,hi,hT,hu,hy,hm,hn,hyy,hxu,huf,huc,hliteral,haux,hym⟩
end ModelBFreshPrivate
#print axioms ModelBFreshPrivate.fresh_private
