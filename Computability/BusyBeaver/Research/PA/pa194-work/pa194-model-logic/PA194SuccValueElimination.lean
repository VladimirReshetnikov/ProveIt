import PA194CancelInputs
import PA194OrdinalTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def succValue (x z : Nat) : Form := Ordinal.domain (.fvar z) ⋏
  (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏
    Ordinal.successor (.bvar 0) (.fvar z)))

structure SuccComponents (Γ : List Form) (x z pred : Nat) where
  outputDomain : ND.Proof Γ (Ordinal.domain (.fvar z))
  predValue : ND.Proof Γ (Ordinal.domain (.fvar pred) ⋏ eq (.fvar pred) (.fvar x))
  successor : ND.Proof Γ (Ordinal.successor (.fvar pred) (.fvar z))

def succValueEliminate (x z : Nat) (q : Form) (h : ND.Proof Γ (succValue x z))
    (k : ∀ {Δ : List Form}, (∀ p, p ∈ ND.shifted Γ → p ∈ Δ) →
      SuccComponents Δ (x+1) (z+1) 0 → ND.Proof Δ q.shift) : ND.Proof Γ q := by
  apply ND.exsElim (ND.andRight h)
  let P : Ordinal.Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏
    Ordinal.successor (.bvar 0) (.fvar z)
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ ((Ordinal.domain (.fvar 0) ⋏ eq (.fvar 0) (.fvar (x+1))) ⋏
      Ordinal.successor (.fvar 0) (.fvar (z+1))) := by
    have hh : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    convert hh using 1
    simp [P,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,successor_rew,eq,Rew.free,Rew.q]
  have ho : ND.Proof Δ (Ordinal.domain (.fvar (z+1))) := ND.up (Ordinal.domainShift z (ND.andLeft h)) P.free
  exact k (Δ := Δ) (fun _ hx => List.mem_cons_of_mem P.free hx) ⟨ho,ND.andLeft hp,ND.andRight hp⟩
#print axioms succValueEliminate
end PA194SuccInjective
