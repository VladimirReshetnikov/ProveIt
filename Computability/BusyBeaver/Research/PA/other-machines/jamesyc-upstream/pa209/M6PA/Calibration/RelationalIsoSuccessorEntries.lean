module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEntriesExtension
@[expose] public section

/-! Objectwise entries under simultaneous successor extension on both sides.
The old coordinates and the new ordered-pair object remain actual witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def entryTwoSuccessors {Γ : List Form} (a b c d p : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (h : ND.Proof Γ (entryWitness (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar c) (.fvar d) (.fvar p)) := by
  apply entryEliminate a b p _ h
  intro Δ incl coordinates
  have ss := ND.weaken (Ordinal.successorShift (a+1) (c+1) (Ordinal.successorShift a c hs)) incl
  have st := ND.weaken (Ordinal.successorShift (b+1) (d+1) (Ordinal.successorShift b d ht)) incl
  have out := entryIntro (c+1+1) (d+1+1) (p+1+1) 1 0
    ⟨Ordinal.successorOld (a+1+1) (c+1+1) 1 ss coordinates.left,
      Ordinal.successorOld (b+1+1) (d+1+1) 0 st coordinates.right,coordinates.object⟩
  convert out using 1 <;> isoSyntax

def successorEndpointEntry {Γ : List Form} (E : Ordinal.EqualityProofs Γ)
    (a b c d p q : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hq : ND.Proof Γ (eq (.fvar q) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar c) (.fvar d) (.fvar q)) := by
  have hm := mp (ND.orRight (Ordinal.eqRefl E a)) (andRight (Ordinal.successorAt a c a hs))
  have hn := mp (ND.orRight (Ordinal.eqRefl E b)) (andRight (Ordinal.successorAt b d b ht))
  exact entryIntro c d q a b ⟨hm,hn,kuratowskiContainer E p q a b (Ordinal.eqSymm E q p hq) hp⟩

def successorTwoEntriesAt {Γ : List Form} (E : Ordinal.EqualityProofs Γ)
    (g p h a b c d q : Nat)
    (hg : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b)))
    (hq : ND.Proof Γ (mem (.fvar h) (.fvar q))) :
    ND.Proof Γ (entryWitness (.fvar c) (.fvar d) (.fvar q)) := by
  apply orElim (mp hq (andLeft (adjunctionAt g p h q ha)))
  · let premise : Form := mem (.fvar g) (.fvar q)
    exact entryTwoSuccessors a b c d q (up hs premise) (up ht premise)
      (graphEntriesAt g a b q (up hg premise) (assumption (by simp [premise])))
  · let premise : Form := eq (.fvar q) (.fvar p)
    exact successorEndpointEntry (E.up premise) a b c d p q (up hs premise)
      (up ht premise) (up hp premise) (assumption (by simp [premise]))

def successorTwoGraphEntries {Γ : List Form} (E : Ordinal.EqualityProofs Γ)
    (g p h a b c d : Nat)
    (hg : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphEntries (.fvar h) (.fvar c) (.fvar d)) := by
  apply allIntro
  let premise : Form := mem (.fvar (h+1)) (.fvar 0)
  have out := successorTwoEntriesAt (E.shift.up premise) (g+1) (p+1) (h+1)
    (a+1) (b+1) (c+1) (d+1) 0 (up (graphEntriesShift g a b hg) premise)
    (up (Ordinal.successorShift a c hs) premise) (up (Ordinal.successorShift b d ht) premise)
    (up (adjunctionShift g p h ha) premise) (up (kuratowskiShift p a b hp) premise)
    (assumption (by simp [premise]))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms successorTwoEntriesAt
#print axioms successorTwoGraphEntries
#print axioms entryTwoSuccessors
#print axioms successorEndpointEntry
end M6.PA.RelationalSource.PairGraph
