module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorCutFrame
@[expose] public section

/-! The cut graph is a real Separation witness satisfying all seven clauses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def predecessorCutIso {Γ : List Form} (g a b p q : Nat)
    (I : PredecessorCutFrame Γ g a b p q) :
    ND.Proof Γ (orderIso (.fvar p) (.fvar q)) := by
  apply exsElim (strictCutFromClosedSeparation p g I.separation)
  let body : Formula 1 := strictGraphCut (.fvar p) (.fvar g) (.bvar 0)
  let C := body.free :: shifted Γ
  have cut : ND.Proof C (strictGraphCut (.fvar (p+1)) (.fvar (g+1)) (.fvar 0)) := by
    have h : ND.Proof C body.free := assumption (by simp [C])
    convert h using 1 <;> (dsimp [body] <;> restrictionSyntax)
  let II := I.shift.weaken (fun r hr => List.mem_cons_of_mem body.free hr)
  have entries := strictCutEntries (p+1) (g+1) 0 (a+1) (b+1) cut (andLeft (andRight II.graph))
  have restricted := strictCutEdges II.equality.core II.equality.transitive (p+1) (g+1) 0 cut
  have bijection := predecessorOrderBijection (g+1) (a+1) (b+1) (p+1) (q+1) 0
    II.graph II.leftSuccessor II.rightSuccessor II.endpoint entries restricted
  have out : ND.Proof C (orderIso (.fvar (p+1)) (.fvar (q+1))) := by
    apply exsIntro _ (.fvar 0)
    convert bijection using 1 <;> isoSyntax
  convert out using 1 <;> (dsimp [C,body] <;> restrictionSyntax)

#print axioms predecessorCutIso
end M6.PA.RelationalSource.PairGraph
