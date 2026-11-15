import PA194FoundationInverseEntryElimination
import PA194FoundationIsoEntries
import PA194FoundationInverseOrderRules
set_option maxHeartbeats 8000000

/-! Full inverse-prefix objects have genuine entries with the codomain and
domain reversed, not just decoded edge typing. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def inverseBijectionEntry {Γ : List Form} (g a b p : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (inverseEntryWitness (.fvar g) (.fvar a) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar b) (.fvar a) (.fvar p)) := by
  apply inverseEntryEliminate g a p _ he
  intro Δ inc c
  have tt := ND.weaken (inverseOrderTypedShift (g+1) (a+1) (b+1) (inverseOrderTypedShift g a b ht)) inc
  have hm := inverseOrderTypedAt (g+1+1) (a+1+1) (b+1+1) 1 0 tt c.forward
  have out := entryIntro (b+1+1) (a+1+1) (p+1+1) 0 1 ⟨andRight hm,c.member,c.object⟩
  convert out using 1 <;> inverseSyntax

def inverseBijectionEntries {Γ : List Form} (g a b h : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (inverseEntries (.fvar g) (.fvar a) (.fvar h))) :
    ND.Proof Γ (graphEntries (.fvar h) (.fvar b) (.fvar a)) := by
  apply allIntro
  let d : Form := mem (.fvar (h+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have ee : ND.Proof (shifted Γ) (inverseEntries (.fvar (g+1)) (.fvar (a+1)) (.fvar (h+1))) := by
    convert shiftProof he using 1 <;> inverseSyntax
  have out := inverseBijectionEntry (g+1) (a+1) (b+1) 0 (up (inverseOrderTypedShift g a b ht) d)
    (inverseEntriesAt (g+1) (a+1) (h+1) 0 (up ee d) hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> inverseSyntax)

#print axioms inverseBijectionEntry
#print axioms inverseBijectionEntries
end M6.PA.RelationalSource.PairGraph
