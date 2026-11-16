import PA194SuccEqualElimination
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ Δ : List Form}

theorem succValue_shift (x z : Nat) : (succValue x z).shift = succValue (x+1) (z+1) := by
  rw [←succValueTerm_fvar x z,←succValueTerm_fvar (x+1) (z+1)]
  change Semiformula.rewAux Rew.shift _ = _
  simp [succValueTerm_rew,Rew.shift,Rew.map]

def SuccEqualComponents.weaken {a b x y : Nat} (h : SuccEqualComponents Γ a b x y)
    (hincl : ∀ p, p ∈ Γ → p ∈ Δ) : SuccEqualComponents Δ a b x y :=
  ⟨ND.weaken h.left hincl,ND.weaken h.right hincl,ND.weaken h.iso hincl⟩

def SuccEqualComponents.shift {a b x y : Nat} (h : SuccEqualComponents Γ a b x y) :
    SuccEqualComponents (ND.shifted Γ) (a+1) (b+1) (x+1) (y+1) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [succValue_shift] using ND.shiftProof h.left
  · simpa only [succValue_shift] using ND.shiftProof h.right
  · have hh := ND.shiftProof h.iso
    convert hh using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [orderIso_rew,Rew.shift,Rew.map]
#print axioms succValue_shift
#print axioms SuccEqualComponents.shift
end PA194SuccInjective
