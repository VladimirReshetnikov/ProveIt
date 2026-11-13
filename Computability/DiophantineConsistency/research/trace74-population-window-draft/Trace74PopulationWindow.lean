import DiophantineConsistency.ArithmeticHalfBinomialCompat

/-! Source draft: the half-binomial population argument with the lower rank
    window as an explicit premise. No old-chart alpha or sum guard is used.
    Power, alignment and ordinate hypotheses are not derived from a 74 zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74PopulationWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem population_of_window (q X Y u v h R j : V)
    (hq : q=Exp.exp h) (hwindow : 3*q<R)
    (hY : ∃ s, Y=q^3*s) (hX : X=Exp.exp R)
    (hYpos : 0<Y) (hupos : 0<u) (hvpos : 0<v)
    (hj13 : 13≤j) (hjR : 2*j=R+1)
    (hjy : 2*ycoord j (2*((X*Y)*Y-1)+1)=u+v)
    (hRy : ycoord R (X*Y+Y)=u+Y*(u+v)) :
    3*h+2≤population R := by
  have hj5 : 5≤j := le_trans (by norm_num) hj13
  obtain ⟨r,hrplus,hr4,hRodd⟩ := ArithmeticHalfBinomialCompat.half_index_of_ge_five j R hj5 hjR
  have hXe : X=Exp.exp (2*r+1) := by rw [←hRodd]; exact hX
  have hY1 : 1≤Y := pos_iff_one_le.mp hYpos
  have hck : ycoord (2*r+1) (Y*(X+1))=
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)*Y+u := by
    have ha : Y*(X+1)=X*Y+Y := by ring
    rw [ha,←hRodd,hRy,hrplus,hjy]
    ring
  obtain ⟨w,hw⟩ := half_binomial X Y r u v hr4 hXe hY1 hck
    (by rw [hrplus,hjy]) hupos hvpos
  obtain ⟨s,hs⟩ := hY
  have hYq : Exp.exp (3*h)∣Y := by
    refine ⟨s,?_⟩
    rw [hs,hq,show 3*h=h+h+h by ring,exp_add,exp_add]
    ring
  have hhq : h<q := by rw [hq]; exact lt_exp h
  have h3 : 3*h+1≤R := lt_iff_succ_le.mp
    (lt_trans (mul_lt_mul_of_pos_left hhq (by norm_num : (0:V)<3)) hwindow)
  rw [hRodd] at h3 ⊢
  exact population_lower X Y r w h hXe hw hYq h3

#print axioms Trace74PopulationWindow.population_of_window
end Trace74PopulationWindow
