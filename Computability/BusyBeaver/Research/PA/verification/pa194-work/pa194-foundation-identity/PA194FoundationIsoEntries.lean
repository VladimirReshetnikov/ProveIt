import PA194FoundationIdentityEmpty

/-! Every graph object carries actual coordinate witnesses, independently of
edge typing. This interface deliberately preserves that stronger clause. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

structure EntryComponents (Γ : List Form) (a b p x y : Nat) where
  left : ND.Proof Γ (mem (.fvar a) (.fvar x))
  right : ND.Proof Γ (mem (.fvar b) (.fvar y))
  object : ND.Proof Γ (kuratowski (.fvar p) (.fvar x) (.fvar y))

def entryIntro {Γ : List Form} (a b p x y : Nat) (h : EntryComponents Γ a b p x y) :
    ND.Proof Γ (entryWitness (.fvar a) (.fvar b) (.fvar p)) := by
  apply exsIntro _ (.fvar x)
  have hh : ND.Proof Γ (∃⁰ (mem (.fvar a) (.fvar x) ⋏
      (mem (.fvar b) (.bvar 0) ⋏ kuratowski (.fvar p) (.fvar x) (.bvar 0)))) := by
    apply exsIntro _ (.fvar y)
    convert andIntro h.left (andIntro h.right h.object) using 1 <;> isoSyntax
  convert hh using 1 <;> isoSyntax

def graphEntriesAt {Γ : List Form} (g a b p : Nat)
    (h : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar g) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar a) (.fvar b) (.fvar p)) := by
  have hi : ND.Proof Γ (mem (.fvar g) (.fvar p) 🡒 entryWitness (.fvar a) (.fvar b) (.fvar p)) := by
    convert allElim _ (.fvar p) h using 1 <;> isoSyntax
  exact mp hm hi

def identityDiagonalAt {Γ : List Form} (g a x y : Nat)
    (h : ND.Proof Γ (identityDiagonal (.fvar g) (.fvar a)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ eq (.fvar x) (.fvar y)) := by
  have hi : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) 🡒
      (mem (.fvar a) (.fvar x) ⋏ eq (.fvar x) (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) h) using 1 <;> isoSyntax
  exact mp he hi

def identityTotalAt {Γ : List Form} (g a x : Nat)
    (h : ND.Proof Γ (identityTotal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar x)) := by
  have hi : ND.Proof Γ (mem (.fvar a) (.fvar x) 🡒 edge (.fvar g) (.fvar x) (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;> isoSyntax
  exact mp hx hi

#print axioms entryIntro
#print axioms graphEntriesAt
#print axioms identityDiagonalAt
#print axioms identityTotalAt
end M6.PA.RelationalSource.PairGraph
