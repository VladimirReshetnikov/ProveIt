import PA194FoundationGraphExtension
import PA194FoundationOrdinalSuccessorClosureLinear
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula EqualityProofs eqTrans eqSymm equalityTransShift)

def eqShift {Γ : List Form} (a b : Nat)
    (h : ND.Proof Γ (eq (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (eq (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 ; pairSyntax

def singletonCoordinate {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (a b s : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (singleton (.fvar a) (.fvar s))) :
    ND.Proof Γ (singleton (.fvar b) (.fvar s)) := by
  apply allIntro
  have hi := singletonAt (a+1) (s+1) 0 (singletonShift a s hs)
  have he := eqShift a b hab
  have ht := equalityTransShift et
  have hb := eqSymm e.shift (a+1) (b+1) he
  have result : ND.Proof (shifted Γ) (sourceIff (mem (.fvar (s+1)) (.fvar 0))
      (eq (.fvar 0) (.fvar (b+1)))) := by
    apply andIntro
    · apply impIntro
      have h := mp (assumption (by simp)) (up (andLeft hi) (mem (.fvar (s+1)) (.fvar 0)))
      exact eqTrans (up ht _) 0 (a+1) (b+1) h (up he _)
    · apply impIntro
      have h := eqTrans (up ht (eq (.fvar 0) (.fvar (b+1)))) 0 (b+1) (a+1)
        (assumption (by simp)) (up hb _)
      exact mp h (up (andRight hi) _)
  convert result using 1 ; pairSyntax

def pairAt {Γ : List Form} (a b p y : Nat)
    (d : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (sourceIff (mem (.fvar p) (.fvar y))
      (eq (.fvar y) (.fvar a) ⋎ eq (.fvar y) (.fvar b))) := by
  convert allElim _ (.fvar y) d using 1 ; pairSyntax

def coordinateDisjunction {Γ : List Form}
    (et : ND.Proof Γ transitivityFormula) (a b c d y : Nat)
    (hac : ND.Proof Γ (eq (.fvar a) (.fvar c)))
    (hbd : ND.Proof Γ (eq (.fvar b) (.fvar d)))
    (h : ND.Proof Γ (eq (.fvar y) (.fvar a) ⋎ eq (.fvar y) (.fvar b))) :
    ND.Proof Γ (eq (.fvar y) (.fvar c) ⋎ eq (.fvar y) (.fvar d)) := by
  apply orElim h
  · exact ND.orLeft (eqTrans (up et _) y a c (assumption (by simp)) (up hac _))
  · exact ND.orRight (eqTrans (up et _) y b d (assumption (by simp)) (up hbd _))

def pairCoordinate {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (a b c d p : Nat)
    (hac : ND.Proof Γ (eq (.fvar a) (.fvar c)))
    (hbd : ND.Proof Γ (eq (.fvar b) (.fvar d)))
    (hp : ND.Proof Γ (pair (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (pair (.fvar c) (.fvar d) (.fvar p)) := by
  apply allIntro
  have hi := pairAt (a+1) (b+1) (p+1) 0 (pairShift a b p hp)
  have hc := eqShift a c hac
  have hd := eqShift b d hbd
  have ht := equalityTransShift et
  have hca := eqSymm e.shift (a+1) (c+1) hc
  have hdb := eqSymm e.shift (b+1) (d+1) hd
  have result : ND.Proof (shifted Γ) (sourceIff (mem (.fvar (p+1)) (.fvar 0))
      (eq (.fvar 0) (.fvar (c+1)) ⋎ eq (.fvar 0) (.fvar (d+1)))) := by
    apply andIntro
    · apply impIntro
      have hm := mp (assumption (by simp)) (up (andLeft hi) (mem (.fvar (p+1)) (.fvar 0)))
      exact coordinateDisjunction (up ht _) (a+1) (b+1) (c+1) (d+1) 0 (up hc _) (up hd _) hm
    · apply impIntro
      have hm := coordinateDisjunction
        (up ht (eq (.fvar 0) (.fvar (c+1)) ⋎ eq (.fvar 0) (.fvar (d+1))))
        (c+1) (d+1) (a+1) (b+1) 0 (up hca _) (up hdb _) (assumption (by simp))
      exact mp hm (up (andRight hi) _)
  convert result using 1 ; pairSyntax

#print axioms singletonCoordinate
#print axioms pairAt
#print axioms coordinateDisjunction
#print axioms pairCoordinate
end M6.PA.RelationalSource.PairGraph
