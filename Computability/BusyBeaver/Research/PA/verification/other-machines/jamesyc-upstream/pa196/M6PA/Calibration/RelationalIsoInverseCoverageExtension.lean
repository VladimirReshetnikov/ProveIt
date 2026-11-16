module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseCorrectExtension
@[expose] public section

/-! Existential coverage of every old or newly added prefix coordinate. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseOldCoverage {Γ : List Form} (g n h p j x : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar h)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hx : ND.Proof Γ (mem (.fvar n) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar j) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0))) := by
  apply exsElim (inverseCoverageAt g n h x hc hx)
  let σ : Formula 1 := edge (.fvar h) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hh : ND.Proof C (edge (.fvar (h+1)) (.fvar 0) (.fvar (x+1)) ⋏
      edge (.fvar (g+1)) (.fvar (x+1)) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ] <;> inverseSyntax)
  have hj := adjunctionPreservesEdge (h+1) (p+1) (j+1) 0 (x+1)
    (up (adjunctionShift h p j ha) σ.free) (andLeft hh)
  have out : ND.Proof C (∃¹ (edge (.fvar (j+1)) (.bvar 0) (.fvar (x+1)) ⋏
      edge (.fvar (g+1)) (.fvar (x+1)) (.bvar 0))) := by
    apply exsIntro _ (.fvar 0)
    convert andIntro hj (andRight hh) using 1 <;> inverseSyntax
  convert out using 1 <;> (dsimp [C,σ] <;> inverseSyntax)

def successorInverseCoverageAt {Γ : List Form} (E : FormulaEquality Γ) (g n s h v p j x : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n)))
    (hx : ND.Proof Γ (mem (.fvar s) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar j) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0))) := by
  apply orElim (mp hx (andLeft (Ordinal.successorAt n s x hs)))
  · let d : Form := mem (.fvar n) (.fvar x)
    exact inverseOldCoverage g n h p j x (up hc d) (up ha d) (assumption (by simp [d]))
  · let d : Form := eq (.fvar x) (.fvar n)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    have hj := classifiedEdge ee.core ee.transitive h p j v n v x (up ha d) (up hp d)
      (ND.orRight (andIntro (Ordinal.eqRefl ee.core v) hd))
    have hg := edgeInputTransport ee g n x v (ee.symmetryOf hd) (up hv d)
    apply exsIntro _ (.fvar v)
    convert andIntro hj hg using 1 <;> inverseSyntax

def successorInverseCoverage {Γ : List Form} (E : FormulaEquality Γ) (g n s h v p j : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n))) :
    ND.Proof Γ (inverseCoverage (.fvar g) (.fvar s) (.fvar j)) := by
  apply allIntro
  let d : Form := mem (.fvar (s+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have vv : ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (v+1))) := by
    convert shiftProof hv using 1 <;> inverseSyntax
  have out := successorInverseCoverageAt (E.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq))
    (g+1) (n+1) (s+1) (h+1) (v+1) (p+1) (j+1) 0
    (up (inverseCoverageShift g n h hc) d) (up (Ordinal.successorShift n s hs) d) (up vv d)
    (up (adjunctionShift h p j ha) d) (up (kuratowskiShift p v n hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def successorInversePrefix {Γ : List Form} (E : FormulaEquality Γ) (g n s h v p j : Nat)
    (hc : ND.Proof Γ (inversePrefix (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n))) :
    ND.Proof Γ (inversePrefix (.fvar g) (.fvar s) (.fvar j)) :=
  andIntro (successorInverseEntries E.core g n s h v p j (andLeft hc) hs hv ha hp)
    (andIntro (successorInverseCorrect E g n s h v p j (andLeft (andRight hc)) hs hv ha hp)
      (successorInverseCoverage E g n s h v p j (andRight (andRight hc)) hs hv ha hp))

#print axioms inverseOldCoverage
#print axioms successorInverseCoverageAt
#print axioms successorInverseCoverage
#print axioms successorInversePrefix
end M6.PA.RelationalSource.PairGraph
