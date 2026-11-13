module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionPrefix
@[expose] public section

/-! Actual three-coordinate witnesses for each composition graph object. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

structure CompositionEntryComponents (Γ : List Form) (g h n p x y z : Nat) where
  member : ND.Proof Γ (mem (.fvar n) (.fvar x))
  leftEdge : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))
  rightEdge : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar z))
  object : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar z))

def compositionEntryIntro {Γ : List Form} (g h n p x y z : Nat)
    (c : CompositionEntryComponents Γ g h n p x y z) :
    ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar n) (.fvar p)) := by
  have hz : ND.Proof Γ (∃¹ (mem (.fvar n) (.fvar x) ⋏
      (edge (.fvar g) (.fvar x) (.fvar y) ⋏
        (edge (.fvar h) (.fvar y) (.bvar 0) ⋏ kuratowski (.fvar p) (.fvar x) (.bvar 0))))) := by
    apply exsIntro _ (.fvar z)
    convert andIntro c.member (andIntro c.leftEdge (andIntro c.rightEdge c.object)) using 1 <;> compositionSyntax
  have hy : ND.Proof Γ (∃¹ ∃¹ (mem (.fvar n) (.fvar x) ⋏
      (edge (.fvar g) (.fvar x) (.bvar 1) ⋏
        (edge (.fvar h) (.bvar 1) (.bvar 0) ⋏ kuratowski (.fvar p) (.fvar x) (.bvar 0))))) := by
    apply exsIntro _ (.fvar y)
    convert hz using 1 <;> compositionSyntax
  apply exsIntro _ (.fvar x)
  convert hy using 1 <;> compositionSyntax

def compositionEntriesAt {Γ : List Form} (g h n k p : Nat)
    (he : ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hm : ND.Proof Γ (mem (.fvar k) (.fvar p))) :
    ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar n) (.fvar p)) := by
  have hi : ND.Proof Γ (mem (.fvar k) (.fvar p) 🡒
      compositionEntryWitness (.fvar g) (.fvar h) (.fvar n) (.fvar p)) := by
    convert allElim _ (.fvar p) he using 1 <;> compositionSyntax
  exact mp hm hi

#print axioms compositionEntryIntro
#print axioms compositionEntriesAt
end M6.PA.RelationalSource.PairGraph
