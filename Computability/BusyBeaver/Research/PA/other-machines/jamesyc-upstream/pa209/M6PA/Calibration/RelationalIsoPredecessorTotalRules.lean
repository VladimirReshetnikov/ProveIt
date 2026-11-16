module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorTyped
public import M6PA.Calibration.RelationalIsoSuccessorTotalRules
@[expose] public section

/-! Actual totality witnesses for the strict predecessor cut. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)

def predecessorLeftAt {Γ : List Form} (g h a p x : Nat)
    (hl : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar p) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar h) (.fvar x)) := by
  apply exsElim (orderLeftAt g a x hl (Ordinal.successorOld p a x hs hm))
  let body : Formula 1 := edge (.fvar g) (.fvar x) (.bvar 0)
  let C := body.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> isoSyntax)
  have mm : ND.Proof C (mem (.fvar (p+1)) (.fvar (x+1))) := by
    have hh := up (shiftProof hm) body.free
    convert hh using 1 <;> isoSyntax
  have heNew := strictCutIntro (p+1) (g+1) (h+1) (x+1) 0
    (up (strictRestrictionShift p g h hr) body.free) he mm
  have out := outputIntro (h+1) (x+1) 0 heNew
  convert out using 1 <;> (dsimp [C,body,hasOutput] <;> isoSyntax)

def predecessorRightAt {Γ : List Form} (g h b p q y : Nat)
    (ht : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (hr : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h)))
    (hpq : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (hm : ND.Proof Γ (mem (.fvar q) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar h) (.bvar 0) (.fvar y)) := by
  apply exsElim (orderRightAt g b y ht (Ordinal.successorOld q b y hs hm))
  let body : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let C := body.free :: shifted Γ
  have he : ND.Proof C (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> isoSyntax)
  have mm : ND.Proof C (mem (.fvar (q+1)) (.fvar (y+1))) := by
    have hh := up (shiftProof hm) body.free
    convert hh using 1 <;> isoSyntax
  have ee : ND.Proof C (edge (.fvar (g+1)) (.fvar (p+1)) (.fvar (q+1))) := by
    have hh := up (shiftProof hpq) body.free
    convert hh using 1 <;> isoSyntax
  have order := orderOrderAt (g+1) (p+1) 0 (q+1) (y+1)
    (up (orderOrderShift g ho) body.free) ee he
  have heNew := strictCutIntro (p+1) (g+1) (h+1) 0 (y+1)
    (up (strictRestrictionShift p g h hr) body.free) he (mp mm (andRight order))
  have out := inputIntro (h+1) 0 (y+1) heNew
  convert out using 1 <;> (dsimp [C,body] <;> isoSyntax)

#print axioms predecessorLeftAt
#print axioms predecessorRightAt
end M6.PA.RelationalSource.PairGraph
