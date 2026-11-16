module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionFrame
@[expose] public section

/-! Real Kuratowski(n,z) and raw Adjunction construct the next composition
prefix. Neither an image object nor canonical pair representatives are assumed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionFromObject {Γ : List Form} (g h n s k y z p : Nat)
    (I : CompositionFrame Γ g h n s k y z)
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply exsElim (adjunctionWitness k p I.adjunction)
  let σ : Formula 1 := adjunction (.fvar k) (.fvar p) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ha : ND.Proof C (adjunction (.fvar (k+1)) (.fvar (p+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have II := I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)
  have hk := successorCompositionPrefix II.equality (g+1) (h+1) (n+1) (s+1) (k+1) (y+1) (z+1) (p+1) 0
    II.graph II.successor II.leftEdge II.rightEdge ha (up (kuratowskiShift p n z hp) σ.free)
  have out : ND.Proof C (compositionPrefixExists (.fvar (g+1)) (.fvar (h+1)) (.fvar (s+1))) := by
    apply exsIntro _ (.fvar 0)
    convert hk using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def compositionStepWitness {Γ : List Form} (g h n s k y z : Nat)
    (I : CompositionFrame Γ g h n s k y z) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar s)) := by
  apply exsElim (kuratowskiWitness n z I.empty I.adjunction)
  let σ : Formula 1 := kuratowski (.bvar 0) (.fvar n) (.fvar z)
  let C := σ.free :: shifted Γ
  have hp : ND.Proof C (kuratowski (.fvar 0) (.fvar (n+1)) (.fvar (z+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have out := compositionFromObject (g+1) (h+1) (n+1) (s+1) (k+1) (y+1) (z+1) 0
    (I.shift.weaken (fun q hq => List.mem_cons_of_mem σ.free hq)) hp
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

#print axioms compositionFromObject
#print axioms compositionStepWitness
end M6.PA.RelationalSource.PairGraph
