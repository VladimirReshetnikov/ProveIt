module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestriction
public import M6PA.Calibration.RelationalIsoEntriesExtension
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (EqualityProofs equalityTransShift memElement)

def strictEntryDecoded {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top p x y : Nat)
    (hs : ND.Proof Γ (strictEntry (.fvar top) (.fvar p)))
    (hk : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar top) (.fvar x)) := by
  apply strictEntryEliminate top p _ hs
  intro Δ incl hc hm
  let ee := equalityWeaken e.shift.shift incl
  have ett := ND.weaken (equalityTransShift (equalityTransShift et)) incl
  have kk := ND.weaken (kuratowskiShift (p+1) (x+1) (y+1) (kuratowskiShift p x y hk)) incl
  have he := andLeft (kuratowskiDecode ee ett (p+1+1) 1 0 (x+1+1) (y+1+1) hc kk)
  have out := memElement ee (top+1+1) 1 (x+1+1) he hm
  convert out using 1 <;> restrictionSyntax

def strictCutEdgeForward {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top g h x y : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) ⋏ mem (.fvar top) (.fvar x)) := by
  apply exsElim he
  let σ : Ordinal.Formula 1 := mem (.fvar h) (.bvar 0) ⋏
    kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mem (.fvar (h+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]<;> restrictionSyntax)
  have hf := strictCutAt (top+1) (g+1) (h+1) 0 (up (strictCutShift top g h hc) σ.free)
  have filtered := mp (andLeft hh) (andLeft hf)
  have old := edgeFromEntry (g+1) (x+1) (y+1) 0 (andLeft filtered) (andRight hh)
  have inside := strictEntryDecoded (e.shift.up σ.free) (up (equalityTransShift et) σ.free)
    (top+1) 0 (x+1) (y+1) (andRight filtered) (andRight hh)
  convert andIntro old inside using 1 <;> (dsimp [C,σ]<;> restrictionSyntax)

def strictCutEdgeBackward {Γ : List Form} (top g h x y : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hm : ND.Proof Γ (mem (.fvar top) (.fvar x))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) := by
  apply exsElim he
  let σ : Ordinal.Formula 1 := mem (.fvar g) (.bvar 0) ⋏
    kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mem (.fvar (g+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]<;> restrictionSyntax)
  have inside : ND.Proof C (mem (.fvar (top+1)) (.fvar (x+1))) := by
    convert up (shiftProof hm) σ.free using 1 <;> restrictionSyntax
  have hs := strictEntryIntro (top+1) 0 (x+1) (y+1) (andRight hh) inside
  have hf := strictCutAt (top+1) (g+1) (h+1) 0 (up (strictCutShift top g h hc) σ.free)
  have retained := mp (andIntro (andLeft hh) hs) (andRight hf)
  have out := edgeFromEntry (h+1) (x+1) (y+1) 0 retained (andRight hh)
  convert out using 1 <;> (dsimp [C,σ]<;> restrictionSyntax)

def strictCutEdges {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top g h : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (strictGraphRestriction (.fvar top) (.fvar g) (.fvar h)) := by
  apply allIntro
  apply allIntro
  have cc := strictCutShift (top+1) (g+1) (h+1) (strictCutShift top g h hc)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceIff (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0))
        (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏ mem (.fvar (top+1+1)) (.fvar 1))) := by
    apply andIntro
    · apply impIntro
      exact strictCutEdgeForward (e.shift.shift.up _)
        (up (equalityTransShift (equalityTransShift et)) _)
        (top+1+1) (g+1+1) (h+1+1) 1 0 (up cc _) (assumption (by simp))
    · apply impIntro
      have hh := assumption (p := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏ mem (.fvar (top+1+1)) (.fvar 1)) (Γ := (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏
        mem (.fvar (top+1+1)) (.fvar 1)) :: shifted (shifted Γ)) (by simp)
      exact strictCutEdgeBackward (top+1+1) (g+1+1) (h+1+1) 1 0
        (up cc _) (andLeft hh) (andRight hh)
  convert result using 1 <;> restrictionSyntax

def strictCutEntry {Γ : List Form} (top g h a b p : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar h) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar top) (.fvar b) (.fvar p)) := by
  have hf := mp hm (andLeft (strictCutAt top g h p hc))
  apply strictEntryEliminate top p _ (andRight hf)
  intro Δ incl hk hi
  have mm : ND.Proof Δ (mem (.fvar (g+1+1)) (.fvar (p+1+1))) := by
    convert ND.weaken (shiftProof (shiftProof (andLeft hf))) incl using 1 <;> restrictionSyntax
  have tt := ND.weaken (orderTypedShift (g+1) (a+1) (b+1) (orderTypedShift g a b ht)) incl
  have old := edgeFromEntry (g+1+1) 1 0 (p+1+1) mm hk
  have typed := orderTypedAt (g+1+1) (a+1+1) (b+1+1) 1 0 tt old
  have out := entryIntro (top+1+1) (b+1+1) (p+1+1) 1 0 ⟨hi,andRight typed,hk⟩
  convert out using 1 <;> restrictionSyntax

def strictCutEntries {Γ : List Form} (top g h a b : Nat)
    (hc : ND.Proof Γ (strictGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphEntries (.fvar h) (.fvar top) (.fvar b)) := by
  apply allIntro
  let premise : Form := mem (.fvar (h+1)) (.fvar 0)
  have out := strictCutEntry (top+1) (g+1) (h+1) (a+1) (b+1) 0
    (up (strictCutShift top g h hc) premise)
    (up (orderTypedShift g a b ht) premise)
    (assumption (Γ := premise :: shifted Γ) (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise]<;> restrictionSyntax)

#print axioms strictEntryDecoded
#print axioms strictCutEdgeForward
#print axioms strictCutEdgeBackward
#print axioms strictCutEdges
#print axioms strictCutEntry
#print axioms strictCutEntries
end M6.PA.RelationalSource.PairGraph
