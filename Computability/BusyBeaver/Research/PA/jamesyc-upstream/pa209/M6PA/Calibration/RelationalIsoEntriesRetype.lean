module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoEntriesExtension
public import M6PA.Calibration.RelationalOrderIsoRules
@[expose] public section

/-! Retyping actual graph objects via a new typing proof. Unlike typing alone,
the explicit old entries premise supplies genuine ordered-pair witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def entryRetype {Γ : List Form} (g a b c d p : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar c) (.fvar d)))
    (hm : ND.Proof Γ (mem (.fvar g) (.fvar p)))
    (he : ND.Proof Γ (entryWitness (.fvar a) (.fvar b) (.fvar p))) :
    ND.Proof Γ (entryWitness (.fvar c) (.fvar d) (.fvar p)) := by
  apply entryEliminate a b p _ he
  intro Δ incl coordinates
  have mm : ND.Proof Δ (mem (.fvar (g+1+1)) (.fvar (p+1+1))) := by
    have v := ND.weaken (shiftProof (shiftProof hm)) incl
    convert v using 1 <;> isoSyntax
  have edgeActual := edgeFromEntry (g+1+1) 1 0 (p+1+1) mm coordinates.object
  have tt := ND.weaken (orderTypedShift (g+1) (c+1) (d+1) (orderTypedShift g c d ht)) incl
  have typed := orderTypedAt (g+1+1) (c+1+1) (d+1+1) 1 0 tt edgeActual
  have out := entryIntro (c+1+1) (d+1+1) (p+1+1) 1 0
    ⟨andLeft typed,andRight typed,coordinates.object⟩
  convert out using 1 <;> isoSyntax

def graphEntriesRetype {Γ : List Form} (g a b c d : Nat)
    (he : ND.Proof Γ (graphEntries (.fvar g) (.fvar a) (.fvar b)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar c) (.fvar d))) :
    ND.Proof Γ (graphEntries (.fvar g) (.fvar c) (.fvar d)) := by
  apply allIntro
  let premise : Form := mem (.fvar (g+1)) (.fvar 0)
  have hm : ND.Proof (premise::shifted Γ) premise := assumption (by simp)
  have old := graphEntriesAt (g+1) (a+1) (b+1) 0 (up (graphEntriesShift g a b he) premise) hm
  have out := entryRetype (g+1) (a+1) (b+1) (c+1) (d+1) 0
    (up (orderTypedShift g c d ht) premise) hm old
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

#print axioms entryRetype
#print axioms graphEntriesRetype
end M6.PA.RelationalSource.PairGraph
