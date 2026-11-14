import PA194FoundationOrdinalSuccessorClosureStructural
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def eqTrans {Γ : List Form} (d : ND.Proof Γ transitivityFormula) (i j k : Nat)
    (hij : ND.Proof Γ (eq (.fvar i) (.fvar j)))
    (hjk : ND.Proof Γ (eq (.fvar j) (.fvar k))) : ND.Proof Γ (eq (.fvar i) (.fvar k)) := by
  have h : ND.Proof Γ (eq (.fvar i) (.fvar j) 🡒 eq (.fvar j) (.fvar k) 🡒 eq (.fvar i) (.fvar k)) := by
    convert allElim _ (.fvar k) (allElim _ (.fvar j) (allElim _ (.fvar i) d)) using 1
    simp only [transitivityFormula,eqAtom,notEqAtom]
    sourceSyntaxEq
  exact mp hjk (mp hij h)

def equalityTransShift {Γ : List Form} (d : ND.Proof Γ transitivityFormula) :
    ND.Proof (shifted Γ) transitivityFormula := by
  convert shiftProof d using 1
  simp only [transitivityFormula,eqAtom,notEqAtom]
  sourceSyntaxEq

def memberLinearShift {Γ : List Form} (i : Nat) (d : ND.Proof Γ (memberLinear (.fvar i))) :
    ND.Proof (shifted Γ) (memberLinear (.fvar (i+1))) := by
  convert shiftProof d using 1 ; ordinalSyntax

def memberLinearAt {Γ : List Form} (i x y : Nat)
    (d : ND.Proof Γ (memberLinear (.fvar i)))
    (hx : ND.Proof Γ (mem (.fvar i) (.fvar x)))
    (hy : ND.Proof Γ (mem (.fvar i) (.fvar y))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y) ⋎
      (mem (.fvar y) (.fvar x) ⋎ mem (.fvar x) (.fvar y))) := by
  have h : ND.Proof Γ ((mem (.fvar i) (.fvar x) ⋏ mem (.fvar i) (.fvar y)) 🡒
      (eq (.fvar x) (.fvar y) ⋎ (mem (.fvar y) (.fvar x) ⋎ mem (.fvar x) (.fvar y)))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) d) using 1 ; ordinalSyntax
  exact mp (andIntro hx hy) h

def successorCompare {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (i j x y : Nat)
    (hl : ND.Proof Γ (memberLinear (.fvar i)))
    (hs : ND.Proof Γ (successor (.fvar i) (.fvar j)))
    (hx : ND.Proof Γ (mem (.fvar j) (.fvar x)))
    (hy : ND.Proof Γ (mem (.fvar j) (.fvar y))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y) ⋎
      (mem (.fvar y) (.fvar x) ⋎ mem (.fvar x) (.fvar y))) := by
  have sx := mp hx (andLeft (successorAt i j x hs))
  have sy := mp hy (andLeft (successorAt i j y hs))
  apply orElim sx
  · apply orElim (up sy _)
    · exact memberLinearAt i x y (up (up hl _) _)
        (assumption (by simp)) (assumption (by simp))
    · exact ND.orRight (ND.orLeft (memContainer ((e.up _).up _) i y x
        (eqSymm ((e.up _).up _) y i (assumption (by simp))) (assumption (by simp))))
  · apply orElim (up sy _)
    · exact ND.orRight (ND.orRight (memContainer ((e.up _).up _) i x y
        (eqSymm ((e.up _).up _) x i (assumption (by simp))) (assumption (by simp))))
    · exact ND.orLeft (eqTrans (up (up et _) _) x i y (assumption (by simp))
        (eqSymm ((e.up _).up _) y i (assumption (by simp))))

def successorMemberLinear {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (i j : Nat)
    (hl : ND.Proof Γ (memberLinear (.fvar i)))
    (hs : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (memberLinear (.fvar j)) := by
  apply allIntro
  apply allIntro
  let p : Form := mem (.fvar (j+1+1)) (.fvar 1) ⋏ mem (.fvar (j+1+1)) (.fvar 0)
  have hp : ND.Proof (p :: shifted (shifted Γ)) p := assumption (by simp)
  have h := impIntro (successorCompare (e.shift.shift.up p)
    (up (equalityTransShift (equalityTransShift et)) p) (i+1+1) (j+1+1) 1 0
    (up (memberLinearShift (i+1) (memberLinearShift i hl)) p)
    (up (successorShift (i+1) (j+1) (successorShift i j hs)) p) (andLeft hp) (andRight hp))
  convert h using 1 ; dsimp [p] ; ordinalSyntax

#print axioms successorCompare
#print axioms successorMemberLinear
end M6.PA.RelationalSource.Ordinal

