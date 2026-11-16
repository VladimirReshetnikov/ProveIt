module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseFrame
@[expose] public section

/-! A real reverse Kuratowski object followed by raw Adjunction constructs
an inverse prefix; no image set or canonical pair is assumed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseFromObject {Γ : List Form} (g n s h v p : Nat) (I : InverseFrame Γ g n s h v)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n))) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar s)) := by
  apply exsElim (adjunctionWitness h p I.adjunction)
  let σ : Formula 1 := adjunction (.fvar h) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (h+1)) (.fvar (p+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have II := I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have hg := successorInversePrefix II.equality (g+1) (n+1) (s+1) (h+1) (v+1) (p+1) 0
    II.graph II.successor II.forward ha (up (kuratowskiShift p v n hp) σ.free)
  have out : ND.Proof C (inversePrefixExists (.fvar (g+1)) (.fvar (s+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hg using 1 <;> inverseSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def inverseStepWitness {Γ : List Form} (g n s h v : Nat) (I : InverseFrame Γ g n s h v) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar s)) := by
  apply exsElim (kuratowskiWitness v n I.empty I.adjunction)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar v) (.fvar n)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (v+1)) (.fvar (n+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have out := inverseFromObject (g+1) (n+1) (s+1) (h+1) (v+1) 0
    (I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)) hp
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

#print axioms inverseFromObject
#print axioms inverseStepWitness
end M6.PA.RelationalSource.PairGraph
