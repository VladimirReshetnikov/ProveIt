module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionEdge
@[expose] public section

/-! Pointwise and shifting interfaces for composition-prefix clauses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def compositionCorrectAt {Γ : List Form} (g h n k x z : Nat)
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (he : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z))) :
    ND.Proof Γ (mem (.fvar n) (.fvar x) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z)) := by
  have hi : ND.Proof Γ (edge (.fvar k) (.fvar x) (.fvar z) 🡒
      (mem (.fvar n) (.fvar x) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.fvar z))) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar x) hc) using 1 <;> compositionSyntax
  exact mp he hi

def compositionCoverageAt {Γ : List Form} (g h n k x : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar k)))
    (hm : ND.Proof Γ (mem (.fvar n) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar k) (.fvar x) (.bvar 0) ⋏
      compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0))) := by
  have hi : ND.Proof Γ (mem (.fvar n) (.fvar x) 🡒
      (∃¹ (edge (.fvar k) (.fvar x) (.bvar 0) ⋏ compositionEdge (.fvar g) (.fvar h) (.fvar x) (.bvar 0)))) := by
    convert allElim _ (.fvar x) hc using 1 <;> compositionSyntax
  exact mp hm hi

def compositionCorrectShift {Γ : List Form} (g h n k : Nat)
    (hc : ND.Proof Γ (compositionCorrect (.fvar g) (.fvar h) (.fvar n) (.fvar k))) :
    ND.Proof (shifted Γ) (compositionCorrect (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar (k+1))) := by
  convert shiftProof hc using 1 <;> compositionSyntax

def compositionCoverageShift {Γ : List Form} (g h n k : Nat)
    (hc : ND.Proof Γ (compositionCoverage (.fvar g) (.fvar h) (.fvar n) (.fvar k))) :
    ND.Proof (shifted Γ) (compositionCoverage (.fvar (g+1)) (.fvar (h+1)) (.fvar (n+1)) (.fvar (k+1))) := by
  convert shiftProof hc using 1 <;> compositionSyntax

#print axioms compositionCorrectAt
#print axioms compositionCoverageAt
#print axioms compositionCorrectShift
#print axioms compositionCoverageShift
end M6.PA.RelationalSource.PairGraph
