module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoReflexivity
@[expose] public section

/-! Distinct empty representatives are related by an actual empty graph.
Ordinary equality premises used by the existing diagonal rules remain explicit;
no raw equality between the two empty representatives is inferred. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def emptyGraphTyped {Γ : List Form} (g a b : Nat)
    (hg : ND.Proof Γ (Ordinal.zero (.fvar g))) :
    ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (g+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have bot := emptyNoEdge (g+1+1) 1 0 (up (Ordinal.zeroShift (g+1) (Ordinal.zeroShift g hg)) d) hd
  have out : ND.Proof (d :: shifted (shifted Γ))
      (mem (.fvar (a+1+1)) (.fvar 1) ⋏ mem (.fvar (b+1+1)) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyGraphLeftTotal {Γ : List Form} (g a : Nat)
    (ha : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (a+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (a+1) 0 (up (Ordinal.zeroShift a ha) d))
  have out : ND.Proof (d :: shifted Γ) (∃¹ edge (.fvar (g+1)) (.fvar 0) (.bvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyGraphRightTotal {Γ : List Form} (g b : Nat)
    (hb : ND.Proof Γ (Ordinal.zero (.fvar b))) :
    ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (b+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have bot := contradiction hd (Ordinal.zeroNotMem (b+1) 0 (up (Ordinal.zeroShift b hb) d))
  have out : ND.Proof (d :: shifted Γ) (∃¹ edge (.fvar (g+1)) (.bvar 0) (.fvar 0)) := botElim bot
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def emptyBijection {Γ : List Form} (E : FormulaEquality Γ) (g a b : Nat)
    (hg : ND.Proof Γ (Ordinal.zero (.fvar g)))
    (ha : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.zero (.fvar b))) :
    ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)) :=
  andIntro (emptyGraphEntries g a b hg)
    (andIntro (emptyGraphTyped g a b hg)
      (andIntro (emptyGraphLeftTotal g a ha)
        (andIntro (emptyGraphRightTotal g b hb)
          (andIntro (identityFunctional E g g (emptyIdentityDiagonal g hg))
            (andIntro (identityInjective E g g (emptyIdentityDiagonal g hg))
              (identityOrder E g g (emptyIdentityDiagonal g hg)))))))

def zeroOrderIso {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (ha : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.zero (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar b)) := by
  apply exsIntro _ (.fvar a)
  convert emptyBijection E a a b ha ha hb using 1 <;> isoSyntax

#print axioms emptyGraphTyped
#print axioms emptyGraphLeftTotal
#print axioms emptyGraphRightTotal
#print axioms emptyBijection
#print axioms zeroOrderIso
end M6.PA.RelationalSource.PairGraph
