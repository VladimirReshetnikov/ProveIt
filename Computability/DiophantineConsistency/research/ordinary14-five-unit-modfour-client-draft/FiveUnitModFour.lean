import FiveUnitFacts

/-! Source-only factor client: the three residue shape equations and the
signed-pair product identity are explicit; no graph evaluation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FiveUnitModFourDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFactorUnits2011 FiveUnitFactsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Exact residue shapes exclude negative units, so the first pair and the
other four pairs are all positive units at product one. The fourth pair s is
an unrestricted guard. -/
theorem five_of_modfour_shapes (m x k : V) (hm : 2≤m)
    (q r s t : Pair V) (u a c d f i v y : ZMod 4)
    (hp : Equivalent (product5 (x*x,(m*k)*(m*k+k)) q r s t) (natural (1:V)))
    (hq : pairResidue q=1+d^2-u^2*(1+(a^2+4*a+3)*c^2))
    (hr : pairResidue r=(a^2+4*a+3)*(f^2-1)*v^2+
      (1-(a^2+4*a+3)*(f^2-1))*y^2)
    (ht : pairResidue t=1+i^2-(a^2+4*a+3)*(f^2-1)) :
    x*x=(m*k)*(m*k+k)+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧
      s.1=s.2+1 ∧ t.1=t.2+1 := by
  apply five_positive_of_direct_first m x k hm q r s t hp
  · rw [hq]; exact main_bad u a c d
  · rw [hr]; exact aux_bad a f v y
  · rw [ht]; exact strong_bad a f i

end DiophantineConsistency.FiveUnitModFourDraft

#print axioms DiophantineConsistency.FiveUnitModFourDraft.five_of_modfour_shapes
