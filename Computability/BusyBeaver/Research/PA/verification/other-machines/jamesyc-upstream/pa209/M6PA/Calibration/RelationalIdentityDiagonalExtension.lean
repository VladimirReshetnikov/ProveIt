module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEntriesExtension
@[expose] public section

/-! Diagonal edge classification after adjoining the actual (a,a) object. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def identityDiagonalShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a))) :
    ND.Proof (shifted Γ) (identityDiagonal (.fvar (g+1)) (.fvar (a+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def successorDiagonalAt {Γ : List Form} (E : FormulaEquality Γ) (g p h a b x y : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar b) (.fvar x) ⋏ eq (.fvar x) (.fvar y)) := by
  apply orElim (classifyEdge E.core E.transitive g p h a a x y ha hp he)
  · let d : Form := edge (.fvar g) (.fvar x) (.fvar y)
    have v := identityDiagonalAt g a x y (up hg d) (assumption (by simp [d]))
    exact andIntro (Ordinal.successorOld a b x (up hs d) (andLeft v)) (andRight v)
  · let d : Form := eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar a)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    have hm := mp (ND.orRight (Ordinal.eqRefl ee.core a)) (andRight (Ordinal.successorAt a b a (up hs d)))
    exact andIntro (Ordinal.memElement ee.core b a x (Ordinal.eqSymm ee.core x a (andLeft hd)) hm)
      (Ordinal.eqTrans ee.transitive x a y (andLeft hd) (Ordinal.eqSymm ee.core y a (andRight hd)))

def successorIdentityDiagonal {Γ : List Form} (E : FormulaEquality Γ) (g p h a b : Nat)
    (hg : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a))) :
    ND.Proof Γ (identityDiagonal (.fvar h) (.fvar b)) := by
  apply allIntro
  apply allIntro
  let d : Form := edge (.fvar (h+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have ee := E.shifted.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq)
  have out := successorDiagonalAt ee (g+1+1) (p+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0
    (up (identityDiagonalShift (g+1) (a+1) (identityDiagonalShift g a hg)) d)
    (up (Ordinal.successorShift (a+1) (b+1) (Ordinal.successorShift a b hs)) d)
    (up (adjunctionShift (g+1) (p+1) (h+1) (adjunctionShift g p h ha)) d)
    (up (kuratowskiShift (p+1) (a+1) (a+1) (kuratowskiShift p a a hp)) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

#print axioms identityDiagonalShift
#print axioms successorDiagonalAt
#print axioms successorIdentityDiagonal
end M6.PA.RelationalSource.PairGraph
