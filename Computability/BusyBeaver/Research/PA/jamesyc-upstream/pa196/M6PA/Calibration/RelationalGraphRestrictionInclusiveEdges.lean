module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphRestrictionInclusive
@[expose] public section

namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (EqualityProofs equalityTransShift memElement)

def inclusiveDomainTransport {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top x y : Nat)
    (he : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x))) :
    ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar y)) := by
  apply orElim hi
  · exact ND.orLeft (memElement (e.up _) top x y (up he _) (assumption (by simp)))
  · exact ND.orRight (Ordinal.eqTrans (up et _) y x top
      (Ordinal.eqSymm (e.up _) x y (up he _)) (assumption (by simp)))

def domainEntryDecoded {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top p x y : Nat)
    (hs : ND.Proof Γ (domainEntry (.fvar top) (.fvar p)))
    (hk : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar y))) :
    ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x)) := by
  apply domainEntryEliminate top p _ hs
  intro Δ incl hc hm
  let ee := equalityWeaken e.shift.shift incl
  have ett := ND.weaken (equalityTransShift (equalityTransShift et)) incl
  have kk := ND.weaken (kuratowskiShift (p+1) (x+1) (y+1) (kuratowskiShift p x y hk)) incl
  have he := andLeft (kuratowskiDecode ee ett (p+1+1) 1 0 (x+1+1) (y+1+1) hc kk)
  have out := inclusiveDomainTransport ee ett (top+1+1) 1 (x+1+1) he hm
  convert out using 1 <;> inclusiveRestrictionSyntax

def inclusiveCutEdgeForward {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top g h x y : Nat)
    (hc : ND.Proof Γ (inclusiveGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) ⋏ inclusiveDomain (.fvar top) (.fvar x)) := by
  apply exsElim he
  let σ : Ordinal.Formula 1 := mem (.fvar h) (.bvar 0) ⋏
    kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mem (.fvar (h+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]<;> inclusiveRestrictionSyntax)
  have hf := inclusiveCutAt (top+1) (g+1) (h+1) 0 (up (inclusiveCutShift top g h hc) σ.free)
  have filtered := mp (andLeft hh) (andLeft hf)
  have old := edgeFromEntry (g+1) (x+1) (y+1) 0 (andLeft filtered) (andRight hh)
  have inside := domainEntryDecoded (e.shift.up σ.free) (up (equalityTransShift et) σ.free)
    (top+1) 0 (x+1) (y+1) (andRight filtered) (andRight hh)
  convert andIntro old inside using 1 <;> (dsimp [C,σ]<;> inclusiveRestrictionSyntax)

def inclusiveCutEdgeBackward {Γ : List Form} (top g h x y : Nat)
    (hc : ND.Proof Γ (inclusiveGraphCut (.fvar top) (.fvar g) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (hm : ND.Proof Γ (inclusiveDomain (.fvar top) (.fvar x))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y)) := by
  apply exsElim he
  let σ : Ordinal.Formula 1 := mem (.fvar g) (.bvar 0) ⋏
    kuratowski (.bvar 0) (.fvar x) (.fvar y)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (mem (.fvar (g+1)) (.fvar 0) ⋏
      kuratowski (.fvar 0) (.fvar (x+1)) (.fvar (y+1))) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]<;> inclusiveRestrictionSyntax)
  have inside : ND.Proof C (inclusiveDomain (.fvar (top+1)) (.fvar (x+1))) := by
    convert up (shiftProof hm) σ.free using 1 <;> inclusiveRestrictionSyntax
  have hs := domainEntryIntro (top+1) 0 (x+1) (y+1) (andRight hh) inside
  have hf := inclusiveCutAt (top+1) (g+1) (h+1) 0 (up (inclusiveCutShift top g h hc) σ.free)
  have retained := mp (andIntro (andLeft hh) hs) (andRight hf)
  have out := edgeFromEntry (h+1) (x+1) (y+1) 0 retained (andRight hh)
  convert out using 1 <;> (dsimp [C,σ]<;> inclusiveRestrictionSyntax)

def inclusiveCutEdges {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (top g h : Nat)
    (hc : ND.Proof Γ (inclusiveGraphCut (.fvar top) (.fvar g) (.fvar h))) :
    ND.Proof Γ (graphRestriction (.fvar top) (.fvar g) (.fvar h)) := by
  apply allIntro
  apply allIntro
  have cc := inclusiveCutShift (top+1) (g+1) (h+1) (inclusiveCutShift top g h hc)
  have result : ND.Proof (shifted (shifted Γ))
      (sourceIff (edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0))
        (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏ inclusiveDomain (.fvar (top+1+1)) (.fvar 1))) := by
    apply andIntro
    · apply impIntro
      exact inclusiveCutEdgeForward (e.shift.shift.up _)
        (up (equalityTransShift (equalityTransShift et)) _)
        (top+1+1) (g+1+1) (h+1+1) 1 0 (up cc _) (assumption (by simp))
    · apply impIntro
      have hh := assumption (p := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏ inclusiveDomain (.fvar (top+1+1)) (.fvar 1)) (Γ := (edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0) ⋏
        inclusiveDomain (.fvar (top+1+1)) (.fvar 1)) :: shifted (shifted Γ)) (by simp)
      exact inclusiveCutEdgeBackward (top+1+1) (g+1+1) (h+1+1) 1 0
        (up cc _) (andLeft hh) (andRight hh)
  convert result using 1 <;> inclusiveRestrictionSyntax

#print axioms inclusiveDomainTransport
#print axioms domainEntryDecoded
#print axioms inclusiveCutEdgeForward
#print axioms inclusiveCutEdgeBackward
#print axioms inclusiveCutEdges
end M6.PA.RelationalSource.PairGraph
