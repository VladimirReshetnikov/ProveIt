import PA194SuccEqualShift
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ Δ : List Form}

def SuccComponents.weaken {x z pred : Nat} (h : SuccComponents Γ x z pred)
    (hincl : ∀ p, p ∈ Γ → p ∈ Δ) : SuccComponents Δ x z pred :=
  ⟨ND.weaken h.outputDomain hincl,ND.weaken h.predValue hincl,ND.weaken h.successor hincl⟩

def SuccComponents.shift {x z pred : Nat} (h : SuccComponents Γ x z pred) :
    SuccComponents (ND.shifted Γ) (x+1) (z+1) (pred+1) := by
  refine ⟨Ordinal.domainShift z h.outputDomain,?_,Ordinal.successorShift pred z h.successor⟩
  have hh := ND.shiftProof h.predValue
  convert hh using 1
  change _ = Semiformula.rewAux Rew.shift _
  simp [Semiformula.rewAux,domain_rew,eq,Rew.shift,Rew.map]
#print axioms SuccComponents.shift
end PA194SuccInjective
