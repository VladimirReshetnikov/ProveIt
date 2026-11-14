import PA194FoundationIdentityDiagonalExtension

/-! The successor identity graph has every required diagonal edge. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityTotalShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (identityTotal (.fvar g) (.fvar a))) :
    ND.Proof (shifted Γ) (identityTotal (.fvar (g+1)) (.fvar (a+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def successorTotalAt {Γ : List Form} (E : FormulaEquality Γ) (g p h a b x : Nat)
    (hg : ND.Proof Γ (identityTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar b) (.fvar x))) :
    ND.Proof Γ (edge (.fvar h) (.fvar x) (.fvar x)) := by
  apply orElim (mp hx (andLeft (Ordinal.successorAt a b x hs)))
  · let d : Form := mem (.fvar a) (.fvar x)
    exact adjunctionPreservesEdge g p h x x (up ha d)
      (identityTotalAt g a x (up hg d) (assumption (by simp [d])))
  · let d : Form := eq (.fvar x) (.fvar a)
    have hd : ND.Proof (d :: Γ) d := assumption (by simp)
    have ee := E.weaken (fun q hq => List.mem_cons_of_mem d hq)
    exact classifiedEdge ee.core ee.transitive g p h a a x x (up ha d) (up hp d)
      (ND.orRight (andIntro hd hd))

def successorIdentityTotal {Γ : List Form} (E : FormulaEquality Γ) (g p h a b : Nat)
    (hg : ND.Proof Γ (identityTotal (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a))) :
    ND.Proof Γ (identityTotal (.fvar h) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (b+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := successorTotalAt (E.shifted.weaken (fun q hq => List.mem_cons_of_mem d hq))
    (g+1) (p+1) (h+1) (a+1) (b+1) 0 (up (identityTotalShift g a hg) d)
    (up (Ordinal.successorShift a b hs) d) (up (adjunctionShift g p h ha) d)
    (up (kuratowskiShift p a a hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

def successorIdentityGraph {Γ : List Form} (E : FormulaEquality Γ) (g p h a b : Nat)
    (hg : ND.Proof Γ (identityGraph (.fvar g) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a))) :
    ND.Proof Γ (identityGraph (.fvar h) (.fvar b)) :=
  andIntro (successorGraphEntries E.core g p h a b (andLeft hg) hs ha hp)
    (andIntro (successorIdentityDiagonal E g p h a b (andLeft (andRight hg)) hs ha hp)
      (successorIdentityTotal E g p h a b (andRight (andRight hg)) hs ha hp))

#print axioms identityTotalShift
#print axioms successorTotalAt
#print axioms successorIdentityTotal
#print axioms successorIdentityGraph
end M6.PA.RelationalSource.PairGraph
