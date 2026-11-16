import PA194MulPrefixExtension
import PA194FoundationAdditionStepExistence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] addResult mulPrefix

def prefixGraphExists {n : Nat} (top base z : Term n) : Formula n :=
  ∃⁰ mulPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift z) (.bvar 0)

def prefixShift {Γ : List Form} (top base z g : Nat)
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g))) :
    ND.Proof (ND.shifted Γ) (mulPrefix (.fvar (top+1)) (.fvar (base+1)) (.fvar (z+1)) (.fvar (g+1))) := by
  convert ND.shiftProof hp using 1
  simp [Semiformula.shift,mulPrefix_rew,Rew.shift,Rew.map]

def fromOutputs {Γ : List Form} (E : FormulaEquality Γ) (top u base z g c v : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (htop : ND.Proof Γ (Ordinal.domain (.fvar top)))
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hv : ND.Proof Γ (Ordinal.domain (.fvar v)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (ha : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v))) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply ND.exsElim (exactWitness E.core E.transitive g u v hempty hadj)
  let σ : Ordinal.Formula 1 := exactExtension (.fvar g) (.bvar 0) (.fvar u) (.fvar v)
  let C := σ.free :: ND.shifted Γ
  have hx : ND.Proof C (exactExtension (.fvar (g+1)) (.fvar 0) (.fvar (u+1)) (.fvar (v+1))) := by
    have h0 : ND.Proof C σ.free := ND.assumption (by simp [C])
    convert h0 using 1 <;> (dsimp [σ] <;> prefixSyntax)
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ C := fun p hp => List.mem_cons_of_mem σ.free hp
  have out := prefixExtension (E.shifted.weaken inc) (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) (v+1) 0
    (ND.weaken (domainShift top htop) inc) (ND.weaken (domainShift u hu) inc) (ND.weaken (domainShift v hv) inc)
    (ND.weaken (Ordinal.successorShift top u hs) inc) (ND.weaken (prefixShift top base z g hp) inc)
    (ND.weaken (edgeShift g top c he) inc) (ND.weaken (additionShift c base v ha) inc) hx
  apply ND.exsIntro _ (.fvar 0)
  convert out using 1 <;> (dsimp [C,σ,prefixGraphExists] <;> simp [Semiformula.rewAux,mulPrefix_rew,Rew.subst,Rew.q,Rew.func])
#print axioms prefixShift
#print axioms fromOutputs
end PA194MulRecurrenceNew
