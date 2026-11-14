import PA194FoundationIsoEntryElimination

/-! Successor inclusion transports the actual coordinates of every old graph
object; the newly adjoined object has displayed diagonal coordinates. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def entrySuccessor {Γ : List Form} (a b p : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (h : ND.Proof Γ (entryWitness (.fvar a) (.fvar a) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar b) (.fvar b) (.fvar p)) := by
  apply entryEliminate a a p _ h
  intro Δ incl c
  have ss := ND.weaken (Ordinal.successorShift (a+1) (b+1) (Ordinal.successorShift a b hs)) incl
  have out := entryIntro (b+1+1) (b+1+1) (p+1+1) 1 0
    ⟨Ordinal.successorOld (a+1+1) (b+1+1) 1 ss c.left,
      Ordinal.successorOld (a+1+1) (b+1+1) 0 ss c.right,c.object⟩
  convert out using 1 <;> isoSyntax

def successorDiagonalEntry {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (a b p q : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a)))
    (hq : ND.Proof Γ (eq (.fvar q) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar b) (.fvar b) (.fvar q)) := by
  have hm := mp (ND.orRight (Ordinal.eqRefl E a)) (andRight (Ordinal.successorAt a b a hs))
  exact entryIntro b b q a a ⟨hm,hm,kuratowskiContainer E p q a a (Ordinal.eqSymm E q p hq) hp⟩

def successorEntriesAt {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g p h a b q : Nat)
    (hg : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar a)))
    (hq : ND.Proof Γ (mem (.fvar h) (.fvar q))) :
    ND.Proof Γ (entryWitness (.fvar b) (.fvar b) (.fvar q)) := by
  apply orElim (mp hq (andLeft (adjunctionAt g p h q ha)))
  · let d : Form := mem (.fvar g) (.fvar q)
    exact entrySuccessor a b q (up hs d) (graphEntriesAt g a a q (up hg d) (assumption (by simp [d])))
  · let d : Form := eq (.fvar q) (.fvar p)
    exact successorDiagonalEntry (E.up d) a b p q (up hs d) (up hp d) (assumption (by simp [d]))

#print axioms entrySuccessor
#print axioms successorDiagonalEntry
#print axioms successorEntriesAt
end M6.PA.RelationalSource.PairGraph
