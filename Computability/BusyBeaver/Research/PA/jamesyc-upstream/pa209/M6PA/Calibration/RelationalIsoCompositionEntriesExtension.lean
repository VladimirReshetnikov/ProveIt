module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEntrySuccessor
@[expose] public section

/-! Universal actual-entry preservation under the raw composition adjunction. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionEntriesShift {Γ : List Form} (g h n k : Nat)
    (he : ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar n) (.fvar k))) :
    ND.Proof (shifted Γ) (compositionEntries (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar (k+1))) := by
  convert shiftProof he using 1 <;> compositionSyntax

def successorCompositionEntries {Γ : List Form} (E : Ordinal.EqualityProofs Γ)
    (g h n s k y z p l : Nat)
    (he : ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar n) (.fvar s)))
    (hg : ND.Proof Γ (edge (.fvar g) (.fvar n) (.fvar y)))
    (hh : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z)))
    (ha : ND.Proof Γ (adjunction (.fvar k) (.fvar p) (.fvar l)))
    (hp : ND.Proof Γ (kuratowski (.fvar p) (.fvar n) (.fvar z))) :
    ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar s) (.fvar l)) := by
  apply allIntro
  let d : Form := mem (.fvar (l+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have gg : ND.Proof (shifted Γ) (edge (.fvar (g+1)) (.fvar (n+1)) (.fvar (y+1))) := by
    convert shiftProof hg using 1 <;> compositionSyntax
  have hh' : ND.Proof (shifted Γ) (edge (.fvar (h+1)) (.fvar (y+1)) (.fvar (z+1))) := by
    convert shiftProof hh using 1 <;> compositionSyntax
  have out := successorCompositionEntriesAt (E.shift.up d)
    (g+1) (h+1) (n+1) (s+1) (k+1) (y+1) (z+1) (p+1) (l+1) 0
    (up (compositionEntriesShift g h n k he) d) (up (Ordinal.successorShift n s hs) d)
    (up gg d) (up hh' d) (up (adjunctionShift k p l ha) d) (up (kuratowskiShift p n z hp) d) hd
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

#print axioms compositionEntriesShift
#print axioms successorCompositionEntries
end M6.PA.RelationalSource.PairGraph
