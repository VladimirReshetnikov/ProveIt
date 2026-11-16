import PA194FoundationInverseOrderRules
set_option maxHeartbeats 8000000

/-! Shared literal injectivity and membership-order rules, with both actual
edge premises retained. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def inverseOrderInjectiveAt {Γ : List Form} (g x y z : Nat)
    (h : ND.Proof Γ (graphInjective (.fvar g)))
    (hx : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar z)))
    (hy : ND.Proof Γ (edge (.fvar g) (.fvar y) (.fvar z))) :
    ND.Proof Γ (eq (.fvar x) (.fvar y)) := by
  have hi : ND.Proof Γ ((edge (.fvar g) (.fvar x) (.fvar z) ⋏
      edge (.fvar g) (.fvar y) (.fvar z)) 🡒 eq (.fvar x) (.fvar y)) := by
    convert allElim _ (.fvar z) (allElim _ (.fvar y) (allElim _ (.fvar x) h)) using 1 <;> isoSyntax
  exact mp (andIntro hx hy) hi

def inverseOrderOrderAt {Γ : List Form} (g x u y v : Nat)
    (h : ND.Proof Γ (graphOrder (.fvar g)))
    (hxy : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y)))
    (huv : ND.Proof Γ (edge (.fvar g) (.fvar u) (.fvar v))) :
    ND.Proof Γ (sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar y) (.fvar v))) := by
  have hi : ND.Proof Γ ((edge (.fvar g) (.fvar x) (.fvar y) ⋏
      edge (.fvar g) (.fvar u) (.fvar v)) 🡒
      sourceIff (mem (.fvar x) (.fvar u)) (mem (.fvar y) (.fvar v))) := by
    convert allElim _ (.fvar v) (allElim _ (.fvar y) (allElim _ (.fvar u) (allElim _ (.fvar x) h))) using 1 <;> isoSyntax
  exact mp (andIntro hxy huv) hi

def inverseOrderInjectiveShift {Γ : List Form} (g : Nat)
    (h : ND.Proof Γ (graphInjective (.fvar g))) :
    ND.Proof (shifted Γ) (graphInjective (.fvar (g+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

def inverseOrderOrderShift {Γ : List Form} (g : Nat)
    (h : ND.Proof Γ (graphOrder (.fvar g))) :
    ND.Proof (shifted Γ) (graphOrder (.fvar (g+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

#print axioms inverseOrderInjectiveAt
#print axioms inverseOrderOrderAt
#print axioms inverseOrderInjectiveShift
#print axioms inverseOrderOrderShift
end M6.PA.RelationalSource.PairGraph
