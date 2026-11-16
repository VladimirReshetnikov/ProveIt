import PA194FoundationOrderIso
set_option maxHeartbeats 8000000

/-! Literal finite instantiation rules for the shared order-bijection clauses. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def inverseOrderTypedAt {Γ : List Form} (g a b x y : Nat)
    (h : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y)) := by
  have hi : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y) 🡒
      (mem (.fvar a) (.fvar x) ⋏ mem (.fvar b) (.fvar y))) := by
    convert allElim _ (.fvar y) (allElim _ (.fvar x) h) using 1 <;> isoSyntax
  exact mp he hi

def inverseOrderLeftAt {Γ : List Form} (g a x : Nat)
    (h : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hx : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (∃⁰ edge (.fvar g) (.fvar x) (.bvar 0)) := by
  have hi : ND.Proof Γ (mem (.fvar a) (.fvar x) 🡒 ∃⁰ edge (.fvar g) (.fvar x) (.bvar 0)) := by
    convert allElim _ (.fvar x) h using 1 <;> isoSyntax
  exact mp hx hi

def inverseOrderRightAt {Γ : List Form} (g b y : Nat)
    (h : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b)))
    (hy : ND.Proof Γ (mem (.fvar b) (.fvar y))) :
    ND.Proof Γ (∃⁰ edge (.fvar g) (.bvar 0) (.fvar y)) := by
  have hi : ND.Proof Γ (mem (.fvar b) (.fvar y) 🡒 ∃⁰ edge (.fvar g) (.bvar 0) (.fvar y)) := by
    convert allElim _ (.fvar y) h using 1 <;> isoSyntax
  exact mp hy hi

def inverseOrderTypedShift {Γ : List Form} (g a b : Nat)
    (h : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (graphTyped (.fvar (g+1)) (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def inverseOrderLeftShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof (shifted Γ) (graphLeftTotal (.fvar (g+1)) (.fvar (a+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def inverseOrderRightShift {Γ : List Form} (g b : Nat)
    (h : ND.Proof Γ (graphRightTotal (.fvar g) (.fvar b))) :
    ND.Proof (shifted Γ) (graphRightTotal (.fvar (g+1)) (.fvar (b+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

#print axioms inverseOrderTypedAt
#print axioms inverseOrderLeftAt
#print axioms inverseOrderRightAt
#print axioms inverseOrderTypedShift
#print axioms inverseOrderLeftShift
#print axioms inverseOrderRightShift
end M6.PA.RelationalSource.PairGraph
