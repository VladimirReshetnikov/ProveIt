module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionCorrectExtension
public import M6PA.Calibration.RelationalIsoCompositionEntriesExtension
@[expose] public section

/-! Existential coverage and full actual composition-prefix successor closure. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionOldCoverage {Γ : List Form} (g h n k p l x : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hx : ND.Proof Γ (mem (.fvar n) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar l) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0))) := by
  apply exsElim (compositionCoverageAt g h n k x hc hx)
  let σ : Formula 1 := edge (.fvar k) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (k+1)) (.fvar (x+1)) (.fvar 0) ⋏
      compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> compositionSyntax)
  have hl := adjunctionPreservesEdge (k+1) (p+1) (l+1) (x+1) 0
    (up (adjunctionShift k p l ha) σ.free) (andLeft hh)
  have out : ND.Proof C (∃¹ (edge (.fvar (l+1)) (.fvar (x+1)) (.bvar 0) ⋏
      compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar (x+1)) (.bvar 0))) := by
    apply exsIntro _ (.fvar 0)
    convert andIntro hl (andRight hh) using 1 <;> compositionSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> compositionSyntax)

def successorCompositionCoverageAt {Γ : List Form} (E : FormulaEquality Γ)
    (g h n s k y z p l x : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z)))
    (hx : ND.Proof Γ (mem (.fvar s) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar l) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0))) := by
  apply orElim (mp hx (andLeft (Ordinal.successorAt n s x hs)))
  · let d : Form := mem (.fvar n) (.fvar x)
    exact compositionOldCoverage g h n k p l x (up hc d) (up ha d) (assumption (by simp [d]))
  · let d : Form := eq (.fvar x) (.fvar n)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    have hl := classifiedEdge ee.core ee.transitive k p l n z x z (up ha d) (up hp d)
      (ND.orRight (andIntro hd (Ordinal.eqRefl ee.core z)))
    have hnz := compositionEdgeIntro g h n y z (up hg d) (up hh d)
    have hxz := compositionEdgeInputTransport ee g h n z x (ee.symmetryOf hd) hnz
    apply exsIntro _ (.fvar z)
    convert andIntro hl hxz using 1 <;> compositionSyntax

def successorCompositionCoverage {Γ : List Form} (E : FormulaEquality Γ)
    (g h n s k y z p l : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z))) :
    ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar s) (.fvar l)) := by
  apply allIntro
  let d : Form := mem (.fvar (s+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have gg : ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (y+1))) := by
    convert shiftProof hg using 1 <;> compositionSyntax
  have hh' : ND.Proof (shifted Γ) (edge (.fvar (h+1)) (.fvar (y+1)) (.fvar (z+1))) := by
    convert shiftProof hh using 1 <;> compositionSyntax
  have out := successorCompositionCoverageAt (E.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq))
    (g+1) (h+1) (n+1) (s+1) (k+1) (y+1) (z+1) (p+1) (l+1) 0
    (up (compositionCoverageShift g h n k hc) d) (up (Ordinal.successorShift n s hs) d)
    (up gg d) (up hh' d) (up (adjunctionShift k p l ha) d) (up (kuratowskiShift p n z hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def successorCompositionPrefix {Γ : List Form} (E : FormulaEquality Γ)
    (g h n s k y z p l : Nat)
    (hc : ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z))) :
    ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar s) (.fvar l)) :=
  andIntro (successorCompositionEntries E.core g h n s k y z p l (andLeft hc) hs hg hh ha hp)
    (andIntro (successorCompositionCorrect E g h n s k y z p l (andLeft (andRight hc)) hs hg hh ha hp)
      (successorCompositionCoverage E g h n s k y z p l (andRight (andRight hc)) hs hg hh ha hp))

#print axioms compositionOldCoverage
#print axioms successorCompositionCoverageAt
#print axioms successorCompositionCoverage
#print axioms successorCompositionPrefix
end M6.PA.RelationalSource.PairGraph
