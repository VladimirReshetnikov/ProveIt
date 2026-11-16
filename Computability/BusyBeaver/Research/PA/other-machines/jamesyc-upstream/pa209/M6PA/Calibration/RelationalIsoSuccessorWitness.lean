module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorFrame
@[expose] public section

/-! Real Kuratowski and raw Adjunction witnesses for successor isomorphism. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def isoSuccessorFromObject {Γ : List Form} (g a b c d p : Nat) (I : IsoSuccessorFrame Γ g a b c d)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar c) (.fvar d)) := by
  apply exsElim (adjunctionWitness g p I.adjunction)
  let σ : Formula 1 := adjunction (.fvar g) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have II := I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have hg := successorOrderBijection II.equality (g+1) (p+1) 0 (a+1) (b+1) (c+1) (d+1)
    II.graph II.leftDomain II.rightDomain II.leftSuccessor II.rightSuccessor ha
    (up (kuratowskiShift p a b hp) σ.free)
  have out : ND.Proof C (orderIso (.fvar (c+1)) (.fvar (d+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hg using 1 <;> isoSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

def isoSuccessorWitness {Γ : List Form} (g a b c d : Nat) (I : IsoSuccessorFrame Γ g a b c d) :
    ND.Proof Γ (orderIso (.fvar c) (.fvar d)) := by
  apply exsElim (kuratowskiWitness a b I.empty I.adjunction)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := isoSuccessorFromObject (g+1) (a+1) (b+1) (c+1) (d+1) 0
    (I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)) hp
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

#print axioms isoSuccessorFromObject
#print axioms isoSuccessorWitness
end M6.PA.RelationalSource.PairGraph
