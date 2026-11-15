import PA194FoundationOrderIso
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def typedEdgeLeft {Γ : List Form} (g a b x y : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x)) := by
  have h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) 🡒
      (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) ht) using 1 <;> isoSyntax
  exact andLeft (mp he h)

def rightTotalAt {Γ : List Form} (g b y : Nat)
    (ht : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hy : ND.Proof Γ (mem (.fvar b) (.fvar y))) :
    ND.Proof Γ (∃⁰ edge (.fvar g) (.bvar 0) (.fvar y)) := by
  have h : ND.Proof Γ (mem (.fvar b) (.fvar y) 🡒 ∃⁰ edge (.fvar g) (.bvar 0) (.fvar y)) := by
    convert allElim _ (.fvar y) ht using 1 <;> isoSyntax
  exact mp hy h

def zeroAt {Γ : List Form} (a x : Nat) (hz : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (∼mem (.fvar a) (.fvar x)) := by
  convert allElim _ (.fvar x) hz using 1 <;> isoSyntax

def noMemberOfIsoTarget {Γ : List Form} (g a b y : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hr : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b))) :
    ND.Proof Γ (∼mem (.fvar b) (.fvar y)) := by
  apply byContradiction
  let C := ∼∼mem (.fvar b) (.fvar y) :: Γ
  have hy : ND.Proof C (mem (.fvar b) (.fvar y)) := by
    simpa [C] using (assumption (p := ∼∼mem (.fvar b) (.fvar y)) (by simp [C]))
  let hex := rightTotalAt g b y (up hr _) hy
  apply exsElim hex
  let φ : Formula 1 := edge (.fvar g) (.bvar 0) (.fvar y)
  let D := φ.free :: shifted C
  have he : ND.Proof D (edge (.fvar (g+1)) (.fvar 0) (.fvar (y+1))) := by
    have hd : ND.Proof D φ.free := assumption (by simp [D])
    convert hd using 1 <;> (dsimp [φ] <;> isoSyntax)
  have ht' : ND.Proof D (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    have hd := up (shiftProof (up ht (∼∼mem (.fvar b) (.fvar y)))) φ.free
    convert hd using 1 <;> isoSyntax
  have hz' : ND.Proof D (Ordinal.zero (.fvar (a+1))) := by
    have hd := up (shiftProof (up hz (∼∼mem (.fvar b) (.fvar y)))) φ.free
    convert hd using 1 <;> isoSyntax
  have ha := typedEdgeLeft (g+1) (a+1) (b+1) 0 (y+1) ht' he
  have hn := zeroAt (a+1) 0 hz'
  convert contradiction ha hn using 1 <;> isoSyntax

def zeroFromBijection {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar b)) := by
  have ht := andLeft (andRight hb)
  have hr := andLeft (andRight (andRight (andRight hb)))
  have hz' : ND.Proof (shifted Γ) (Ordinal.zero (.fvar (a+1))) := by
    convert shiftProof hz using 1 <;> isoSyntax
  have ht' : ND.Proof (shifted Γ) (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
    convert shiftProof ht using 1 <;> isoSyntax
  have hr' : ND.Proof (shifted Γ) (graphRightTotal (.fvar (g+1)) (.fvar (b+1))) := by
    convert shiftProof hr using 1 <;> isoSyntax
  have hm := noMemberOfIsoTarget (g+1) (a+1) (b+1) 0 hz' ht' hr'
  apply allIntro
  convert hm using 1 <;> isoSyntax

def zeroFromIso {Γ : List Form} (a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (Ordinal.zero (.fvar b)) := by
  apply exsElim hi
  let φ : Formula 1 := orderBijection (.bvar 0) (.fvar a) (.fvar b)
  let D := φ.free :: shifted Γ
  have hb : ND.Proof D (orderBijection (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
    have hd : ND.Proof D φ.free := assumption (by simp [D])
    convert hd using 1 <;> (dsimp [φ] <;> isoSyntax)
  have hz' : ND.Proof D (Ordinal.zero (.fvar (a+1))) := by
    have hd := up (shiftProof hz) φ.free
    convert hd using 1 <;> isoSyntax
  have out := zeroFromBijection 0 (a+1) (b+1) hz' hb
  convert out using 1 <;> isoSyntax

def zeroIsoStatement : Form :=
  ∀⁰ ∀⁰ (Ordinal.zero (.bvar 1) 🡒 orderIso (.bvar 1) (.bvar 0) 🡒 Ordinal.zero (.bvar 0))

def zeroIsoStatementProof : ND.Proof [] zeroIsoStatement := by
  apply allIntro
  apply allIntro
  let z : Form := Ordinal.zero (.fvar 1)
  let i : Form := orderIso (.fvar 1) (.fvar 0)
  let Γ : List Form := [i,z]
  have hz : ND.Proof Γ z := assumption (by simp [Γ])
  have hi : ND.Proof Γ i := assumption (by simp [Γ])
  have out := zeroFromIso 1 0 hz hi
  have h := impIntro (impIntro out)
  convert h using 1 <;> (try dsimp [Γ,z,i,zeroIsoStatement]) <;> (try isoSyntax) <;> (try simp [shifted])

def zeroIsoStatementDerivation : LO.FirstOrder.Derivation [zeroIsoStatement] := by
  simpa [ND.Proof] using zeroIsoStatementProof

#print axioms zeroIsoStatementProof
#print axioms zeroIsoStatementDerivation
#print axioms zeroFromBijection
#print axioms zeroFromIso
#print axioms zeroAt
#print axioms noMemberOfIsoTarget
#print axioms typedEdgeLeft
#print axioms rightTotalAt
end M6.PA.RelationalSource.PairGraph
