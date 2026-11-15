import PA194EqualElimination
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194InverseEqual
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ Δ : List Form}

def EqualComponents.weaken {a b x y : Nat} (h : EqualComponents Γ a b x y)
    (hincl : ∀ p, p ∈ Γ → p ∈ Δ) : EqualComponents Δ a b x y :=
  ⟨ND.weaken h.left hincl, ND.weaken h.right hincl, ND.weaken h.iso hincl⟩

def EqualComponents.shift {a b x y : Nat} (h : EqualComponents Γ a b x y) :
    EqualComponents (ND.shifted Γ) (a+1) (b+1) (x+1) (y+1) := by
  refine ⟨?_,?_,?_⟩
  · have hh := ND.shiftProof h.left
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [Semiformula.rewAux,domain_rew,eq,Rew.shift,Rew.map]
  · have hh := ND.shiftProof h.right
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [Semiformula.rewAux,domain_rew,eq,Rew.shift,Rew.map]
  · have hh := ND.shiftProof h.iso
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [orderIso_rew,Rew.shift,Rew.map]
#print axioms EqualComponents.weaken
#print axioms EqualComponents.shift
end PA194InverseEqual
