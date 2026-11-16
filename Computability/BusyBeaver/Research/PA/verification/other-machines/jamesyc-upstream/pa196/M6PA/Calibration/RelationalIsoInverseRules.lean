module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseEntriesExtension
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

/-! Pointwise rules and capture-aware shifts for inverse prefixes. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def inverseCorrectAt {Γ : List Form} (g n h y x : Nat)
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar n) (.fvar h)))
    (he : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x))) :
    ND.Proof Γ (mem (.fvar n) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.fvar y)) := by
  have hi : ND.Proof Γ (edge (.fvar h) (.fvar y) (.fvar x) 🡒
      (mem (.fvar n) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.fvar y))) := by
    convert allElim _ (.fvar x) (allElim _ (.fvar y) hc) using 1 <;> inverseSyntax
  exact mp he hi

def inverseCoverageAt {Γ : List Form} (g n h x : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar h)))
    (hm : ND.Proof Γ (mem (.fvar n) (.fvar x))) :
    ND.Proof Γ (∃¹ (edge (.fvar h) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0))) := by
  have hi : ND.Proof Γ (mem (.fvar n) (.fvar x) 🡒
      (∃¹ (edge (.fvar h) (.bvar 0) (.fvar x) ⋏ edge (.fvar g) (.fvar x) (.bvar 0)))) := by
    convert allElim _ (.fvar x) hc using 1 <;> inverseSyntax
  exact mp hm hi

def inverseCorrectShift {Γ : List Form} (g n h : Nat)
    (hc : ND.Proof Γ (inverseCorrect (.fvar g) (.fvar n) (.fvar h))) :
    ND.Proof (shifted Γ) (inverseCorrect (.fvar (g+1)) (.fvar (n+1)) (.fvar (h+1))) := by
  convert shiftProof hc using 1 <;> inverseSyntax

def inverseCoverageShift {Γ : List Form} (g n h : Nat)
    (hc : ND.Proof Γ (inverseCoverage (.fvar g) (.fvar n) (.fvar h))) :
    ND.Proof (shifted Γ) (inverseCoverage (.fvar (g+1)) (.fvar (n+1)) (.fvar (h+1))) := by
  convert shiftProof hc using 1 <;> inverseSyntax

def inverseEdgeOutputTransport {Γ : List Form} (E : FormulaEquality Γ) (g x y v : Nat)
    (hyv : ND.Proof Γ (eq (.fvar y) (.fvar v)))
    (h : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar v)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar y]) (edge (.fvar g) (.fvar x) (.bvar 0))) := by
    convert h using 1 <;> inverseSyntax
  have ht := E.substituteOne (edge (.fvar g) (.fvar x) (.bvar 0)) (.fvar y) (.fvar v) hyv hp
  convert ht using 1 <;> inverseSyntax

#print axioms inverseCorrectAt
#print axioms inverseCoverageAt
#print axioms inverseCorrectShift
#print axioms inverseCoverageShift
#print axioms inverseEdgeOutputTransport
end M6.PA.RelationalSource.PairGraph
