module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseEntrySuccessor
@[expose] public section

/-! Every object of the raw adjoined inverse prefix has actual coordinates. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseEntriesShift {Γ : List Form} (g n h : Nat)
    (he : ND.Proof Γ (inverseEntries (.fvar g) (.fvar n) (.fvar h))) :
    ND.Proof (shifted Γ) (inverseEntries (.fvar (g+1)) (.fvar (n+1)) (.fvar (h+1))) := by
  convert shiftProof he using 1 <;> inverseSyntax

def successorInverseEntries {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (g n s h v p j : Nat)
    (hg : ND.Proof Γ (inverseEntries (.fvar g) (.fvar n) (.fvar h)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hv : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar v)))
    (ha : ND.Proof Γ (adjunction (.fvar h) (.fvar p) (.fvar j)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar v) (.fvar n))) :
    ND.Proof Γ (inverseEntries (.fvar g) (.fvar s) (.fvar j)) := by
  apply allIntro
  let d : Form := mem (.fvar (j+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have vv : ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (v+1))) := by
    convert shiftProof hv using 1 <;> inverseSyntax
  have out := successorInverseEntriesAt (E.shift.up d) (g+1) (n+1) (s+1) (h+1) (v+1) (p+1) (j+1) 0
    (up (inverseEntriesShift g n h hg) d) (up (Ordinal.successorShift n s hs) d)
    (up vv d) (up (adjunctionShift h p j ha) d)
    (up (kuratowskiShift p v n hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

#print axioms inverseEntriesShift
#print axioms successorInverseEntries
end M6.PA.RelationalSource.PairGraph
