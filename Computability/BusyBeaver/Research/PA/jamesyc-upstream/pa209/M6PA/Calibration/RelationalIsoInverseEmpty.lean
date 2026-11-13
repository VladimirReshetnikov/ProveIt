module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInversePrefix
@[expose] public section

/-! An empty object is itself an inverse-prefix witness for every graph.
No equality, extensionality, or additional existence premise is used. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def emptyInverseEntries {Γ : List Form} (g n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (inverseEntries (.fvar g) (.fvar n) (.fvar n)) := by
  apply allIntro
  let d : Form := mem (.fvar (n+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (n+1) 0 (up (Ordinal.zeroShift n hz) d))
  have out : ND.Proof (d :: shifted Γ)
      (inverseEntryWitness (.fvar (g+1)) (.fvar (n+1)) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def emptyInverseCorrect {Γ : List Form} (g n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (inverseCorrect (.fvar g) (.fvar n) (.fvar n)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (n+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have bot := emptyNoEdge (n+1+1) 1 0 (up (Ordinal.zeroShift (n+1) (Ordinal.zeroShift n hz)) d) hd
  have out : ND.Proof (d :: shifted (shifted Γ))
      (mem (.fvar (n+1+1)) (.fvar 0) ⋏ edge (.fvar (g+1+1)) (.fvar 0) (.fvar 1)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def emptyInverseCoverage {Γ : List Form} (g n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar n)) := by
  apply allIntro
  let d : Form := mem (.fvar (n+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (n+1) 0 (up (Ordinal.zeroShift n hz) d))
  have out : ND.Proof (d :: shifted Γ)
      (∃¹ (edge (.fvar (n+1)) (.bvar 0) (.fvar 0) ⋏
        edge (.fvar (g+1)) (.fvar 0) (.bvar 0))) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

def emptyInversePrefix {Γ : List Form} (g n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (inversePrefix (.fvar g) (.fvar n) (.fvar n)) :=
  andIntro (emptyInverseEntries g n hz)
    (andIntro (emptyInverseCorrect g n hz) (emptyInverseCoverage g n hz))

def emptyInversePrefixExists {Γ : List Form} (g n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar n)) := by
  apply exsIntro _ (.fvar n)
  convert emptyInversePrefix g n hz using 1 <;> inverseSyntax

#print axioms emptyInverseEntries
#print axioms emptyInverseCorrect
#print axioms emptyInverseCoverage
#print axioms emptyInversePrefix
#print axioms emptyInversePrefixExists
end M6.PA.RelationalSource.PairGraph
