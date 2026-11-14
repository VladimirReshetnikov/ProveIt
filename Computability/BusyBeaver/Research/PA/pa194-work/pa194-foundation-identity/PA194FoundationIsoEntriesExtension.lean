import PA194FoundationIsoEntrySuccessor

/-! Actual objectwise graph-entry preservation under raw diagonal adjunction. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def graphEntriesShift {Γ : List Form} (g a b : Nat)
    (h : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (graphEntries (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def successorGraphEntries {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g p h a b : Nat)
    (hg : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a))) :
    ND.Proof Γ (graphEntries (.fvar h) (.fvar b) (.fvar b)) := by
  apply allIntro
  let d : Form := mem (.fvar (h+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := successorEntriesAt (E.shift.up d) (g+1) (p+1) (h+1) (a+1) (b+1) 0
    (up (graphEntriesShift g a a hg) d) (up (Ordinal.successorShift a b hs) d)
    (up (adjunctionShift g p h ha) d) (up (kuratowskiShift p a a hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> isoSyntax)

#print axioms graphEntriesShift
#print axioms successorGraphEntries
end M6.PA.RelationalSource.PairGraph
