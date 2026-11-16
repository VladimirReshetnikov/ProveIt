module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIso
@[expose] public section

/-! Literal finite instantiation rules for the shared order-bijection clauses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def orderTypedAt {Γ : List Form} (g a b x y : Nat)
    (h : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y)) := by
  have hi : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) 🡒
      (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) h) using 1 <;> isoSyntax
  exact mp he hi

def orderLeftAt {Γ : List Form} (g a x : Nat)
    (h : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃¹ edge (.fvar g) (.fvar x) (.bvar 0)) := by
  have hi : ND.Proof Γ (mem (.fvar a) (.fvar x) 🡒 ∃¹ edge (.fvar g) (.fvar x) (.bvar 0)) := by
    convert allElim _ (.fvar x) h using 1 <;> isoSyntax
  exact mp hx hi

def orderRightAt {Γ : List Form} (g b y : Nat)
    (h : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hy : ND.Proof Γ (mem (.fvar b) (.fvar y))) :
    ND.Proof Γ (∃¹ edge (.fvar g) (.bvar 0) (.fvar y)) := by
  have hi : ND.Proof Γ (mem (.fvar b) (.fvar y) 🡒 ∃¹ edge (.fvar g) (.bvar 0) (.fvar y)) := by
    convert allElim _ (.fvar y) h using 1 <;> isoSyntax
  exact mp hy hi

def orderTypedShift {Γ : List Form} (g a b : Nat)
    (h : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def orderLeftShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof (shifted Γ) (graphLeftTotal (.fvar (g+1)) (.fvar (a+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def orderRightShift {Γ : List Form} (g b : Nat)
    (h : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b))) :
    ND.Proof (shifted Γ) (graphRightTotal (.fvar (g+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

#print axioms orderTypedAt
#print axioms orderLeftAt
#print axioms orderRightAt
#print axioms orderTypedShift
#print axioms orderLeftShift
#print axioms orderRightShift
end M6.PA.RelationalSource.PairGraph
