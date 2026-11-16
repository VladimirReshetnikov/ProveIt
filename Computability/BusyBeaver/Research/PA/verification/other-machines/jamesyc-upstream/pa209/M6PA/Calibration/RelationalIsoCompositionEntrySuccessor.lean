module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEntryElimination
@[expose] public section

/-! Actual triple-coordinate entries survive a composition-prefix extension. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionEntrySuccessor {Γ : List Form} (g h n s p : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (he : ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar n) (.fvar p))) :
    ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar s) (.fvar p)) := by
  apply compositionEntryEliminate g h n p _ he
  intro Δ inc c
  have ss := ND.weaken (Ordinal.successorShift (n+1+1) (s+1+1)
    (Ordinal.successorShift (n+1) (s+1) (Ordinal.successorShift n s hs))) inc
  have out := compositionEntryIntro (g+1+1+1) (h+1+1+1) (s+1+1+1) (p+1+1+1) 2 1 0
    ⟨Ordinal.successorOld (n+1+1+1) (s+1+1+1) 2 ss c.member,c.leftEdge,c.rightEdge,c.object⟩
  convert out using 1 <;> compositionSyntax

def successorCompositionEntry {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g h n s y z p q : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z)))
    (hq : ND.Proof Γ (eq (.fvar q) (.fvar p))) :
    ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar s) (.fvar q)) := by
  have hm := mp (ND.orRight (Ordinal.eqRefl E n)) (andRight (Ordinal.successorAt n s n hs))
  exact compositionEntryIntro g h s q n y z
    ⟨hm,hg,hh,kuratowskiContainer E p q n z (Ordinal.eqSymm E q p hq) hp⟩

def successorCompositionEntriesAt {Γ : List Form} (E : Ordinal.EqualityProofs Γ)
    (g h n s k y z p l q : Nat)
    (he : ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z)))
    (hq : ND.Proof Γ (mem (.fvar l) (.fvar q))) :
    ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar s) (.fvar q)) := by
  apply orElim (mp hq (andLeft (adjunctionAt k p l q ha)))
  · let d : Form := mem (.fvar k) (.fvar q)
    exact compositionEntrySuccessor g h n s q (up hs d)
      (compositionEntriesAt g h n k q (up he d) (assumption (by simp [d])))
  · let d : Form := eq (.fvar q) (.fvar p)
    exact successorCompositionEntry (E.up d) g h n s y z p q (up hs d) (up hg d) (up hh d)
      (up hp d) (assumption (by simp [d]))

#print axioms compositionEntrySuccessor
#print axioms successorCompositionEntry
#print axioms successorCompositionEntriesAt
end M6.PA.RelationalSource.PairGraph
