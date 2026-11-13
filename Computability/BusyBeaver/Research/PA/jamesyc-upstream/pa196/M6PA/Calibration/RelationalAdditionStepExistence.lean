module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionFrame
@[expose] public section

/-! Constructive graph-extension assembly for the addition induction step.
The endpoint, its successor, and the extended graph are all explicitly built. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def prefixGraphExists (top base z : Term n) : Formula n :=
  ∃¹ addPrefix (Rew.bShift top) (Rew.bShift base) (Rew.bShift z) (.bvar 0)

macro "prefixSyntax" : tactic => `(tactic|
  (simp only [prefixGraphExists,exactExtension,classified,addPrevious,addPrefixExists,addPrefix,addRecurrence,addResult,Ordinal.successor,graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def extensionFromOutputs {Γ : List Form} (top u base z g c v : Nat)
    (I : AdditionFrame Γ top u base z g)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar c) (.fvar v))) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply exsElim (exactWitness I.sets.equality.core I.sets.equality.transitive g u v
    I.sets.empty I.sets.adjunction)
  let σ : Formula 1 := exactExtension (.fvar g) (.bvar 0) (.fvar u) (.fvar v)
  let C := σ.free :: shifted Γ
  have hx : ND.Proof C (exactExtension (.fvar (g+1)) (.fvar 0) (.fvar (u+1)) (.fvar (v+1))) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ]; prefixSyntax
  have hp := extendPrefix (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) (v+1) 0
    (I.shift.up σ.free) (up (edgeShift g top c he) σ.free)
    (up (Ordinal.successorShift c v hs) σ.free) hx
  apply exsIntro _ (.fvar 0)
  convert hp using 1 <;> (dsimp [C,σ] <;> prefixSyntax)

def extensionFromEndpoint {Γ : List Form} (top u base z g c : Nat)
    (I : AdditionFrame Γ top u base z g)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c))) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  apply exsElim (Ordinal.rawSuccessor (.fvar c) I.sets.adjunction)
  let σ : Formula 1 := Ordinal.successor (.fvar c) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hs : ND.Proof C (Ordinal.successor (.fvar (c+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ]; prefixSyntax
  have out := extensionFromOutputs (top+1) (u+1) (base+1) (z+1) (g+1) (c+1) 0
    (I.shift.up σ.free) (up (edgeShift g top c he) σ.free) hs
  convert out using 1 <;> (dsimp [C,σ] <;> prefixSyntax)

def prefixStepWitness {Γ : List Form} (top u base z g : Nat)
    (I : AdditionFrame Γ top u base z g) :
    ND.Proof Γ (prefixGraphExists (.fvar u) (.fvar base) (.fvar z)) := by
  have hd := graphDomainAt top g top (andLeft I.trace)
  have ho := mp (ND.orRight (I.sets.equality.reflexive (.fvar top))) (andRight hd)
  apply exsElim ho
  let σ : Formula 1 := edge (.fvar g) (.fvar top) (.bvar 0)
  let C := σ.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (top+1)) (.fvar 0)) := by
    have h0 : ND.Proof C σ.free := assumption (by simp [C])
    convert h0 using 1 ; dsimp [σ]; prefixSyntax
  have out := extensionFromEndpoint (top+1) (u+1) (base+1) (z+1) (g+1) 0 (I.shift.up σ.free) he
  convert out using 1 <;> (dsimp [C,σ] <;> prefixSyntax)

#print axioms extensionFromOutputs
#print axioms extensionFromEndpoint
#print axioms prefixStepWitness
end M6.PA.RelationalSource.PairGraph
