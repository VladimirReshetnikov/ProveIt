import DiophantineConsistency.ArithmeticAdaptivePopulation2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPopulationFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticBinaryPopulation ArithmeticHalfBinomial
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Population consequence of the explicit ordinary-index, power, and
radix facts. This is independent of a graph or any particular port tuple. -/
theorem population_of_ordinary_facts (q F alpha J MC MF X Y u v h R j : V)
    (hq16 : 16 ≤ q) (halpha : 0 < alpha) (hq : q = Exp.exp h)
    (hR : R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J)
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
  have h3 : 3*h+1≤R := by
    rw [hR]
    exact ArithmeticHalfBinomialCompat.rank_lower_of_radix q F alpha J MC MF h hq16 halpha hq
  rw [hRodd] at h3 ⊢
  exact population_lower X Y r w h hXe hw hYq h3
end FreeJPopulationFacts
#print axioms FreeJPopulationFacts.population_of_ordinary_facts
