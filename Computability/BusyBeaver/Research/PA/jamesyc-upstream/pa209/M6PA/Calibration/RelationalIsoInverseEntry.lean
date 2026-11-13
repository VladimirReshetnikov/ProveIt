module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseEmpty
@[expose] public section

/-! Actual coordinate witnesses for reversed graph entries. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

structure InverseEntryComponents (Γ : List Form) (g n p x y : Nat) where
  member : ND.Proof Γ (mem (.fvar n) (.fvar x))
  forward : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))
  object : ND.Proof Γ (kuratowski (.fvar p) (.fvar y) (.fvar x))

def inverseEntryIntro {Γ : List Form} (g n p x y : Nat)
    (h : InverseEntryComponents Γ g n p x y) :
    ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar n) (.fvar p)) := by
  apply exsIntro _ (.fvar x)
  have hh : ND.Proof Γ (∃¹ (mem (.fvar n) (.fvar x) ⋏
      (edge (.fvar g) (.fvar x) (.bvar 0) ⋏ kuratowski (.fvar p) (.bvar 0) (.fvar x)))) := by
    apply exsIntro _ (.fvar y)
    convert andIntro h.member (andIntro h.forward h.object) using 1 <;> inverseSyntax
  convert hh using 1 <;> inverseSyntax

def inverseEntriesAt {Γ : List Form} (g n h p : Nat)
    (he : ND.Proof Γ (inverseEntries (.fvar g) (.fvar n) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar h) (.fvar p))) :
    ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar n) (.fvar p)) := by
  have hi : ND.Proof Γ (mem (.fvar h) (.fvar p) 🡒 inverseEntryWitness (.fvar g) (.fvar n) (.fvar p)) := by
    convert allElim _ (.fvar p) he using 1 <;> inverseSyntax
  exact mp hm hi

#print axioms inverseEntryIntro
#print axioms inverseEntriesAt
end M6.PA.RelationalSource.PairGraph
