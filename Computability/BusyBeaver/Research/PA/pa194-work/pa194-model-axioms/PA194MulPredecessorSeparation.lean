import PA194MulPredecessorRestriction
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix mulResult

def predecessorFromSeparation {Γ : List Form} (E : FormulaEquality Γ) (t u base z g out : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar out)))
    (hsep : ND.Proof Γ (separationFormula (domainEntryProperty (.fvar t)))) :
    ND.Proof Γ (predecessorResult (.fvar t) (.fvar base) (.fvar out)) := by
  apply ND.exsElim (graphRestrictionWitness E.core E.transitive t g hsep)
  let σ : Ordinal.Formula 1 := graphRestriction (.fvar t) (.fvar g) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have hr : ND.Proof C (graphRestriction (.fvar (t+1)) (.fvar (g+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> inclusiveRestrictionSyntax)
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have outp := predecessorFromRestriction (E.shifted.weaken inc) (t+1) (u+1) (base+1) (z+1) (g+1) 0 (out+1)
    (ND.weaken (PairGraph.domainShift t ht) inc) (ND.weaken (Ordinal.successorShift t u hs) inc)
    (ND.weaken (Ordinal.zeroShift z hz) inc) (ND.weaken (prefixShift u base z g hp) inc)
    (ND.weaken (edgeShift g u out he) inc) hr
  convert outp using 1 <;> (dsimp [C,σ,predecessorResult] <;>
    simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,addResult_rew,Rew.shift,Rew.q,Rew.func])
#print axioms predecessorFromSeparation
end PA194MulRecurrenceNew
