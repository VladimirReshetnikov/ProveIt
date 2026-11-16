module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionPrefix
@[expose] public section

/-! The displayed empty object is an actual composition-prefix witness. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def emptyCompositionEntries {Γ : List Form} (g h n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar n) (.fvar n)) := by
  apply allIntro
  let d : Form := mem (.fvar (n+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (n+1) 0 (up (Ordinal.zeroShift n hz) d))
  have out : ND.Proof (d :: shifted Γ)
      (compositionEntryWitness (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def emptyCompositionCorrect {Γ : List Form} (g h n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar n) (.fvar n)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (n+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have bot := emptyNoEdge (n+1+1) 1 0 (up (Ordinal.zeroShift (n+1) (Ordinal.zeroShift n hz)) d) hd
  have out : ND.Proof (d :: shifted (shifted Γ))
      (mem (.fvar (n+1+1)) (.fvar 1) ⋏
        compositionEdge (.fvar (g+1+1)) (.fvar (h+1+1)) (.fvar 1) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def emptyCompositionCoverage {Γ : List Form} (g h n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar n)) := by
  apply allIntro
  let d : Form := mem (.fvar (n+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (n+1) 0 (up (Ordinal.zeroShift n hz) d))
  have out : ND.Proof (d :: shifted Γ)
      (∃¹ (edge (.fvar (n+1)) (.fvar 0) (.bvar 0) ⋏
        compositionEdge (.fvar (g+1)) (.fvar (h+1)) (.fvar 0) (.bvar 0))) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

def emptyCompositionPrefix {Γ : List Form} (g h n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (compositionPrefix (.fvar g) (.fvar h) (.fvar n) (.fvar n)) :=
  andIntro (emptyCompositionEntries g h n hz)
    (andIntro (emptyCompositionCorrect g h n hz) (emptyCompositionCoverage g h n hz))

def emptyCompositionPrefixExists {Γ : List Form} (g h n : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar n))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar n)) := by
  apply exsIntro _ (.fvar n)
  convert emptyCompositionPrefix g h n hz using 1 <;> compositionSyntax

#print axioms emptyCompositionEntries
#print axioms emptyCompositionCorrect
#print axioms emptyCompositionCoverage
#print axioms emptyCompositionPrefix
#print axioms emptyCompositionPrefixExists
end M6.PA.RelationalSource.PairGraph
