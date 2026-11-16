import PA194FoundationIdentityEmpty
import PA194FoundationIdentityBijectionOrder
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def emptyGraphTyped {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar g))) :
    ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have bot := emptyNoEdge (g+1+1) 1 0 (up (Ordinal.zeroShift (g+1) (Ordinal.zeroShift g hz)) d) hd
  have out : ND.Proof (d :: shifted (shifted Γ))
      (mem (.fvar (a+1+1)) (.fvar 1) ⋏ mem (.fvar (b+1+1)) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyGraphRightTotal {Γ : List Form} (g b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar b))) :
    ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (b+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (b+1) 0 (up (Ordinal.zeroShift b hz) d))
  have out : ND.Proof (d :: shifted Γ) (∃⁰ edge (.fvar (g+1)) (.bvar 0) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyOrderIso {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (ha : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.zero (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar b)) := by
  have h := identityBijection E a a (emptyIdentityGraph a ha)
  have ht := emptyGraphTyped a a b ha
  have he := emptyGraphEntries a a b ha
  have hr := emptyGraphRightTotal a b hb
  have hl := andLeft (andRight (andRight h))
  have rest := andRight (andRight (andRight (andRight h)))
  have bij : ND.Proof Γ (orderBijection (.fvar a) (.fvar a) (.fvar b)) :=
    andIntro he (andIntro ht (andIntro hl (andIntro hr rest)))
  apply exsIntro _ (.fvar a)
  convert bij using 1 <;> isoSyntax
#print axioms emptyGraphTyped
#print axioms emptyGraphRightTotal
#print axioms emptyOrderIso
end M6.PA.RelationalSource.PairGraph
