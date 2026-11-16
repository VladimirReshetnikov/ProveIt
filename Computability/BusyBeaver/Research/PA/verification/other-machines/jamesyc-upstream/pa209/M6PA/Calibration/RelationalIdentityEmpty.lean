module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIso
@[expose] public section

/-! The displayed empty object itself is an actual empty identity graph. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def emptyGraphEntries {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar g))) :
    ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (g+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (g+1) 0 (up (Ordinal.zeroShift g hz) d))
  have out : ND.Proof (d :: shifted Γ) (entryWitness (.fvar (a+1)) (.fvar (b+1)) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyIdentityDiagonal {Γ : List Form} (a : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (identityDiagonal (.fvar a) (.fvar a)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (a+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have bot := emptyNoEdge (a+1+1) 1 0 (up (Ordinal.zeroShift (a+1) (Ordinal.zeroShift a hz)) d) hd
  have out : ND.Proof (d :: shifted (shifted Γ))
      (mem (.fvar (a+1+1)) (.fvar 1) ⋏ eq (.fvar 1) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyIdentityTotal {Γ : List Form} (a : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (identityTotal (.fvar a) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (a+1) 0 (up (Ordinal.zeroShift a hz) d))
  have out : ND.Proof (d :: shifted Γ) (edge (.fvar (a+1)) (.fvar 0) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyIdentityGraph {Γ : List Form} (a : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (identityGraph (.fvar a) (.fvar a)) :=
  andIntro (emptyGraphEntries a a a hz) (andIntro (emptyIdentityDiagonal a hz) (emptyIdentityTotal a hz))

def emptyIdentityExists {Γ : List Form} (a : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (identityExists (.fvar a)) := by
  apply exsIntro _ (.fvar a)
  convert emptyIdentityGraph a hz using 1 <;> isoSyntax

#print axioms emptyGraphEntries
#print axioms emptyIdentityDiagonal
#print axioms emptyIdentityTotal
#print axioms emptyIdentityGraph
#print axioms emptyIdentityExists
end M6.PA.RelationalSource.PairGraph
