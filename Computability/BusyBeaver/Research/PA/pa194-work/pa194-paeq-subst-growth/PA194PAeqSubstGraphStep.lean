import PA194PAeqSubstAtomicGrowth
import PA196PASubstitutionConstructorGrowth

/-! A one-node output bound for the actual substitution graph. The common
bound on all proper child outputs is an explicit hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqSubstGraphStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PA194PAeqSubstAtomicGrowth
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_step (w p y B : V)
    (hg : (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w p y)
    (hB : w+3*p+1 ≤ B)
    (hchildren : ∀ w' p' y', (w' = w ∨ w' = qVec PA194PAeq.language w) → p'+2 ≤ p →
      (Substs.construction (V := V) PA194PAeq.language).Graph PA194PAeq.language w' p' y' → y' ≤ B) :
    y ≤ tau (B+8) (22*B+22) := by
  obtain ⟨_,hcase⟩ := UformulaRec1.Construction.Graph.case_iff.mp hg
  rcases hcase with ⟨k,r,v,_,_⟩ | ⟨k,r,v,_,_⟩ | ⟨_,_⟩ | ⟨_,_⟩ |
      ⟨a,b,ya,yb,ha,hb,he,hy⟩ | ⟨a,b,ya,yb,ha,hb,he,hy⟩ |
      ⟨a,ya,ha,he,hy⟩ | ⟨a,ya,ha,he,hy⟩
  · exact graph_atomic_step w p y B hg (Or.inl ⟨k,r,v,by assumption⟩) hB
  · exact graph_atomic_step w p y B hg (Or.inr (Or.inl ⟨k,r,v,by assumption⟩)) hB
  · exact graph_atomic_step w p y B hg (Or.inr (Or.inr (Or.inl (by assumption)))) hB
  · exact graph_atomic_step w p y B hg (Or.inr (Or.inr (Or.inr (by assumption)))) hB
  · have hpa : a+2 ≤ p := by simpa [he] using add_two_le_and_left a b
    have hpb : b+2 ≤ p := by simpa [he] using add_two_le_and_right a b
    have hya := hchildren w a ya (Or.inl rfl) hpa ha
    have hyb := hchildren w b yb (Or.inl rfl) hpb hb
    simpa [Substs.construction] using hy ▸ PA196PASubstitutionConstructorGrowth.and_le B ya yb hya hyb
  · have hpa : a+2 ≤ p := by simpa [he] using add_two_le_or_left a b
    have hpb : b+2 ≤ p := by simpa [he] using add_two_le_or_right a b
    have hya := hchildren w a ya (Or.inl rfl) hpa ha
    have hyb := hchildren w b yb (Or.inl rfl) hpb hb
    simpa [Substs.construction] using hy ▸ PA196PASubstitutionConstructorGrowth.or_le B ya yb hya hyb
  · have hpa : a+2 ≤ p := by simpa [he] using add_two_le_all a
    have hya := hchildren (qVec PA194PAeq.language w) a ya (Or.inr rfl) hpa (by
      simpa [Substs.construction] using ha)
    simpa [Substs.construction] using hy ▸ PA196PASubstitutionConstructorGrowth.all_le B ya hya
  · have hpa : a+2 ≤ p := by simpa [he] using add_two_le_exs a
    have hya := hchildren (qVec PA194PAeq.language w) a ya (Or.inr rfl) hpa (by
      simpa [Substs.construction] using ha)
    simpa [Substs.construction] using hy ▸ PA196PASubstitutionConstructorGrowth.exs_le B ya hya

#print axioms graph_step
end PA194PAeqSubstGraphStep
