import DiophantineConsistency.ArithmeticSaturation
import DiophantineConsistency.ArithmeticRankForcing

/-! UNCHECKED DRAFT. Conditional use of existing saturation and carry bounds.
None of the premises is derived from a 74 zero here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74ConditionalSaturationGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryPopulation ArithmeticBinaryCarry
open ArithmeticSaturation ArithmeticRankForcing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard_of_block_and_population (u q C F MC J H R : V)
    (hq : q=Exp.exp u) (hC : 0<C)
    (hA : C-1<q) (hF : F<q) (hM : MC*J+1<q) (hFle : F≤MC*J)
    (hblock : R = (C-1)+(MC*J+1)+q*(F+H)+
      q^2*(q-1-(C-1))+q^3*(q-1-F))
    (hpopulation : population (MC*J+1)+population H≤u+2)
    (hrank : 3*u+2≤population R) :
    NoCarry (C-1) (MC*J+1) ∧ NoCarry F H ∧ F+C<q := by
  have hA' : C-1<Exp.exp u := by simpa only [hq] using hA
  have hF' : F<Exp.exp u := by simpa only [hq] using hF
  have hM' : MC*J+1<Exp.exp u := by simpa only [hq] using hM
  have hblock' : R=(C-1)+(MC*J+1)+Exp.exp u*(F+H)+
      Exp.exp u^2*(Exp.exp u-1-(C-1))+Exp.exp u^3*(Exp.exp u-1-F) := by
    simpa only [hq] using hblock
  obtain ⟨hAM,hFH⟩ := saturation u (C-1) F (MC*J+1) H R hA' hF' hblock' hpopulation hrank
  have hsum := noCarry_add_lt u (C-1) hA' (MC*J+1) hM' hAM
  have hpred : C-1+1=C := tsub_add_cancel_of_le (pos_iff_one_le.mp hC)
  have heq : (C-1)+(MC*J+1)=C+MC*J := by
    calc
      (C-1)+(MC*J+1)=((C-1)+1)+MC*J := by ring
      _=C+MC*J := by rw [hpred]
  rw [heq,←hq] at hsum
  exact ⟨hAM,hFH,lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hFle C) hsum⟩

#print axioms Trace74ConditionalSaturationGuard.guard_of_block_and_population
end Trace74ConditionalSaturationGuard
