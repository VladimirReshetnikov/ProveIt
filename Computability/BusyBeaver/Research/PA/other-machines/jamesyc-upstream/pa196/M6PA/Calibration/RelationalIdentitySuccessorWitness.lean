module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityFrame
@[expose] public section

/-! Construct the new identity graph from a real Kuratowski object and actual
raw Adjunction. The objectwise entries clause is retained throughout. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def identityFromObject {Γ : List Form} (g a b p : Nat) (I : IdentityFrame Γ g a b)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a))) :
    ND.Proof Γ (identityExists (.fvar b)) := by
  apply exsElim (adjunctionWitness g p I.adjunction)
  let σ : Formula 1 := adjunction (.fvar g) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (g+1)) (.fvar (p+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have II := I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have hg := successorIdentityGraph II.equality (g+1) (p+1) 0 (a+1) (b+1)
    II.graph II.successor ha (up (kuratowskiShift p a a hp) σ.free)
  have out : ND.Proof C (identityExists (.fvar (b+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hg using 1 <;> isoSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

def identityStepWitness {Γ : List Form} (g a b : Nat) (I : IdentityFrame Γ g a b) :
    ND.Proof Γ (identityExists (.fvar b)) := by
  apply exsElim (kuratowskiWitness a a I.empty I.adjunction)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar a) (.fvar a)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (a+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> isoSyntax)
  have out := identityFromObject (g+1) (a+1) (b+1) 0
    (I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)) hp
  convert out using 1 <;> (dsimp [C,σ] <;> isoSyntax)

#print axioms identityFromObject
#print axioms identityStepWitness
end M6.PA.RelationalSource.PairGraph
