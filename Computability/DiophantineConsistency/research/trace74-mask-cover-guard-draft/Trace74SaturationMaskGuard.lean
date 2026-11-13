import Trace74MaskCoverGuard
import DiophantineConsistency.ArithmeticSaturation

/-! UNCHECKED DRAFT. Conditional saturation plus a cover inequality forces
F+C<q. All natural block, population and mask hypotheses remain explicit;
no trace74 graph-zero or fixed-port theorem is claimed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74SaturationMaskGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticBinaryPopulation ArithmeticBinaryCarry
open ArithmeticSaturation ArithmeticRankForcing Trace74MaskCoverGuard
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem guard_from_saturation_and_cover (u q beta MC HP J F C R : V)
    (hq : q=Exp.exp u) (hqdef : q=beta*J+1)
    (hJ : 0<J) (hHPJ : 1≤HP*J) (hcover : beta+1≤MC+HP) (hHP : HP≤beta)
    (hC : 0<C) (hA : C-1<q) (hF : F<q) (hM : MC*J+1<q)
    (hblock : R=(C-1)+(MC*J+1)+q*(F+(HP*J-1))+
      q^2*(q-1-(C-1))+q^3*(q-1-F))
    (hpopulation : population (MC*J+1)+population (HP*J-1)≤u+2)
    (hrank : 3*u+2≤population R) :
    NoCarry (C-1) (MC*J+1) ∧ NoCarry F (HP*J-1) ∧ F+C<q := by
  have hA' : C-1<Exp.exp u := by simpa only [hq] using hA
  have hF' : F<Exp.exp u := by simpa only [hq] using hF
  have hM' : MC*J+1<Exp.exp u := by simpa only [hq] using hM
  have hblock' : R=(C-1)+(MC*J+1)+Exp.exp u*(F+(HP*J-1))+
      Exp.exp u^2*(Exp.exp u-1-(C-1))+Exp.exp u^3*(Exp.exp u-1-F) := by
    simpa only [hq] using hblock
  obtain ⟨hAM,hFH⟩ := saturation u (C-1) F (MC*J+1) (HP*J-1) R
    hA' hF' hblock' hpopulation hrank
  have hFle : F≤MC*J := compare_from_mask_bounds u q beta MC HP J F
    hq hqdef hJ hHPJ hcover hHP hF hFH
  have hsum := noCarry_add_lt u (C-1) hA' (MC*J+1) hM' hAM
  have hpred : C-1+1=C := tsub_add_cancel_of_le (pos_iff_one_le.mp hC)
  have heq : (C-1)+(MC*J+1)=C+MC*J := by
    calc
      (C-1)+(MC*J+1)=((C-1)+1)+MC*J := by ring
      _=C+MC*J := by rw [hpred]
  rw [heq,←hq] at hsum
  exact ⟨hAM,hFH,lt_of_le_of_lt (by simpa [add_comm] using add_le_add_left hFle C) hsum⟩

#print axioms Trace74SaturationMaskGuard.guard_from_saturation_and_cover
end Trace74SaturationMaskGuard
