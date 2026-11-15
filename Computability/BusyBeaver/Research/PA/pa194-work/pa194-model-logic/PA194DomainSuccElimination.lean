import PA194SuccExtensionInputs
import PA194OrdinalTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccExtensionInputs
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def domainSuccessorEliminate (a : Nat) (q : Form) (h : ND.Proof Γ (Ordinal.domainSuccessorExists (.fvar a)))
    (k : ∀ {Δ : List Form}, (∀ p, p ∈ ND.shifted Γ → p ∈ Δ) →
      ND.Proof Δ (Ordinal.domain (.fvar 0)) → ND.Proof Δ (Ordinal.successor (.fvar (a+1)) (.fvar 0)) →
      ND.Proof Δ q.shift) : ND.Proof Γ q := by
  apply ND.exsElim h
  let P : Ordinal.Formula 1 := Ordinal.domain (.bvar 0) ⋏ Ordinal.successor (.fvar a) (.bvar 0)
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ (Ordinal.domain (.fvar 0) ⋏ Ordinal.successor (.fvar (a+1)) (.fvar 0)) := by
    have hh : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    convert hh using 1
    simp [P,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,successor_rew,Rew.free,Rew.q]
  exact k (Δ := Δ) (fun _ hx => List.mem_cons_of_mem P.free hx) (ND.andLeft hp) (ND.andRight hp)
#print axioms domainSuccessorEliminate
end PA194SuccExtensionInputs
