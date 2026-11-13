module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseEntryElimination
@[expose] public section

/-! Successor transport and insertion preserve actual reverse-entry witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseEntrySuccessor {Γ : List Form} (g n s p : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (h : ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar n) (.fvar p))) :
    ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar s) (.fvar p)) := by
  apply inverseEntryEliminate g n p _ h
  intro Δ incl c
  have ss := ND.weaken (Ordinal.successorShift (n+1) (s+1) (Ordinal.successorShift n s hs)) incl
  have out := inverseEntryIntro (g+1+1) (s+1+1) (p+1+1) 1 0
    ⟨Ordinal.successorOld (n+1+1) (s+1+1) 1 ss c.member,c.forward,c.object⟩
  convert out using 1 <;> inverseSyntax

def successorReverseEntry {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g n s v p q : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n)))
    (hq : ND.Proof Γ (eq (.fvar q) (.fvar p))) :
    ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar s) (.fvar q)) := by
  have hm := mp (ND.orRight (Ordinal.eqRefl E n)) (andRight (Ordinal.successorAt n s n hs))
  exact inverseEntryIntro g s q n v
    ⟨hm,hv,kuratowskiContainer E p q v n (Ordinal.eqSymm E q p hq) hp⟩

def successorInverseEntriesAt {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g n s h v p j q : Nat)
    (hg : ND.Proof Γ (inverseEntries (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n)))
    (hq : ND.Proof Γ (mem (.fvar j) (.fvar q))) :
    ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar s) (.fvar q)) := by
  apply orElim (mp hq (andLeft (adjunctionAt h p j q ha)))
  · let d : Form := mem (.fvar h) (.fvar q)
    exact inverseEntrySuccessor g n s q (up hs d)
      (inverseEntriesAt g n h q (up hg d) (assumption (by simp [d])))
  · let d : Form := eq (.fvar q) (.fvar p)
    exact successorReverseEntry (E.up d) g n s v p q (up hs d) (up hv d) (up hp d)
      (assumption (by simp [d]))

#print axioms inverseEntrySuccessor
#print axioms successorReverseEntry
#print axioms successorInverseEntriesAt
end M6.PA.RelationalSource.PairGraph
