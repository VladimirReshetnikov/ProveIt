import PA194MulAdditionWitness
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix

def additionSupply (base : Nat) : Form :=
  ∀⁰ (Ordinal.domain (.bvar 0) 🡒 addOutput (.bvar 0) (.fvar base))

def supplyShift {Γ : List Form} (base : Nat) (h : ND.Proof Γ (additionSupply base)) :
    ND.Proof (ND.shifted Γ) (additionSupply (base+1)) := by
  convert ND.shiftProof h using 1 <;>
    (simp [additionSupply,addOutput,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Ordinal.domain_rew,addResult_rew,
      Rew.shift,Rew.q,Rew.func] <;> finishSourceSyntax)

def supplyAt {Γ : List Form} (base c : Nat)
    (h : ND.Proof Γ (additionSupply base)) (hc : ND.Proof Γ (Ordinal.domain (.fvar c))) :
    ND.Proof Γ (addOutput (.fvar c) (.fvar base)) := by
  have hi : ND.Proof Γ (Ordinal.domain (.fvar c) 🡒 addOutput (.fvar c) (.fvar base)) := by
    convert ND.allElim _ (.fvar c) h using 1 <;>
      (simp [additionSupply,addOutput,Semiformula.rewAux,Ordinal.domain_rew,addResult_rew,Rew.subst,Rew.q,Rew.func] <;> finishSourceSyntax)
  exact ND.mp hc hi

def stepWitness {Γ : List Form} (E : FormulaEquality Γ) (top u base z g : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (hadd : ND.Proof Γ (additionSupply base)) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  have hpParts := hp
  unfold mulPrefix at hpParts
  have hd := graphDomainAt top g top (ND.andLeft hpParts)
  have ho := ND.mp (ND.orRight (E.reflexive (.fvar top))) (ND.andRight hd)
  apply ND.exsElim ho
  let σ : Ordinal.Formula 1 := edge (.fvar g) (.fvar top) (.bvar 0)
  let C := σ.free :: ND.shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (top+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> simp [Semiformula.free,Rewriting.free,Semiformula.rewAux,edge_rew,Rew.free,Rew.q,Rew.func])
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have hprefix := ND.weaken (prefixShift top base z g hp) inc
  have hprefixParts := hprefix
  unfold mulPrefix at hprefixParts
  have hc := graphRangeAt (g+1) (top+1) 0 (ND.andLeft (ND.andRight (ND.andRight hprefixParts))) he
  have ha := supplyAt (base+1) 0 (ND.weaken (supplyShift base hadd) inc) hc
  have out := fromEndpoint (E.shifted.weaken inc) (top+1) (u+1) (base+1) (z+1) (g+1) 0
    (ND.weaken (emptyClosedShift hempty) inc) (ND.weaken (adjunctionClosedShift hadj) inc)
    (ND.weaken (PairGraph.domainShift top htop) inc) (ND.weaken (PairGraph.domainShift u hu) inc)
    (ND.weaken (Ordinal.successorShift top u hs) inc) hprefix he ha
  convert out using 1 <;> (dsimp [C,σ,prefixGraphExists] <;> simp [Semiformula.shift,Rewriting.shift,Semiformula.rewAux,mulPrefix_rew,Rew.shift,Rew.q,Rew.func])
#print axioms supplyAt
#print axioms stepWitness
end PA194MulRecurrenceNew
