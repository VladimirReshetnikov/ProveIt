import PA194FoundationCompositionEntryElimination
import PA194FoundationCompositionEntriesExtension
import PA194FoundationIsoEntries
import PA194FoundationInverseOrderRules
set_option maxHeartbeats 8000000

/-! Every actual composite graph object carries the required endpoint pair. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def compositionBijectionEntry {Γ : List Form} (g h a b c p : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (he : ND.Proof Γ (compositionEntryWitness (.fvar g) (.fvar h) (.fvar a) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar a) (.fvar c) (.fvar p)) := by
  apply compositionEntryEliminate g h a p _ he
  intro Δ inc w
  have tt := ND.weaken (inverseOrderTypedShift (h+1+1) (b+1+1) (c+1+1)
    (inverseOrderTypedShift (h+1) (b+1) (c+1) (inverseOrderTypedShift h b c ht))) inc
  have hz := andRight (inverseOrderTypedAt (h+1+1+1) (b+1+1+1) (c+1+1+1) 1 0 tt w.rightEdge)
  have out := entryIntro (a+1+1+1) (c+1+1+1) (p+1+1+1) 2 0 ⟨w.member,hz,w.object⟩
  convert out using 1 <;> compositionSyntax

def compositionBijectionEntries {Γ : List Form} (g h a b c k : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar h) (.fvar b) (.fvar c)))
    (he : ND.Proof Γ (compositionEntries (.fvar g) (.fvar h) (.fvar a) (.fvar k))) :
    ND.Proof Γ (graphEntries (.fvar k) (.fvar a) (.fvar c)) := by
  apply allIntro
  let d : Form := mem (.fvar (k+1)) (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := compositionBijectionEntry (g+1) (h+1) (a+1) (b+1) (c+1) 0
    (up (inverseOrderTypedShift h b c ht) d)
    (compositionEntriesAt (g+1) (h+1) (a+1) (k+1) 0 (up (compositionEntriesShift g h a k he) d) hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> compositionSyntax)

#print axioms compositionBijectionEntry
#print axioms compositionBijectionEntries
end M6.PA.RelationalSource.PairGraph
