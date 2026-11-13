import DiophantineConsistency.ArithmeticNegativeNorms
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! Source-only signed-pair facts for the 75 finalizer. The first parameter
bound, product representation and three modulo-four exclusions are explicit
hypotheses; no literal graph zero or endpoint is assumed or established. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FiveUnitFactsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ArithmeticAdaptiveFactorUnits2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The direct first factor excludes -1 by internal consecutive Pell descent.
This uses no positivity premise on the root or k. -/
theorem first_ne_negative (m x k : V) (hm : 2≤m) :
    x*x+1 ≠ (m*k)*(m*k+k) := by
  intro h
  apply ArithmeticNegativeNorms.consecutive_ne_negative m x k hm
  calc
    x*x+1=(m*k)*(m*k+k) := h
    _=m*(m+1)*k*k := by ring

/-- The first pair and three mod-four-excluded pairs force five positive
units; the fourth pair is the unrestricted guard. -/
theorem five_positive_of_direct_first (m x k : V) (hm : 2≤m)
    (q r s t : Pair V)
    (hp : Equivalent (product5 (x*x,(m*k)*(m*k+k)) q r s t) (natural (1:V)))
    (hq : pairResidue q ≠ -1) (hr : pairResidue r ≠ -1)
    (ht : pairResidue t ≠ -1) :
    x*x=(m*k)*(m*k+k)+1 ∧ q.1=q.2+1 ∧ r.1=r.2+1 ∧
      s.1=s.2+1 ∧ t.1=t.2+1 := by
  apply product5_positive hp (first_ne_negative m x k hm)
  · intro h; exact hq (negative_residue h)
  · intro h; exact hr (negative_residue h)
  · intro h; exact ht (negative_residue h)

end DiophantineConsistency.FiveUnitFactsDraft

#print axioms DiophantineConsistency.FiveUnitFactsDraft.first_ne_negative
#print axioms DiophantineConsistency.FiveUnitFactsDraft.five_positive_of_direct_first
