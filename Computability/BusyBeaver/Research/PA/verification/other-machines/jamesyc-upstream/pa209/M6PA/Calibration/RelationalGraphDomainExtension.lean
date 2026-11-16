module
public import M6PA.Theory
public import M6PA.Calibration.RelationalGraphOutputExtension
public import M6PA.Calibration.RelationalGraphFreshInput
@[expose] public section

/-! Exact inclusive domain advancement by one ordinal successor. No model
reasoning or finiteness assumption replaces the object-level proofs. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def oldOutputMember {Γ : List Form} (top a g x : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar a)))
    (hd : ND.Proof Γ (graphDomain (.fvar top) (.fvar g)))
    (ho : ND.Proof Γ (hasOutput (.fvar g) (.fvar x))) :
    ND.Proof Γ (mem (.fvar a) (.fvar x)) :=
  mp (mp ho (andLeft (graphDomainAt top g x hd))) (andRight (Ordinal.successorAt top a x hs))

def newMemberOutput {Γ : List Form} (top a g x : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar a)))
    (hd : ND.Proof Γ (graphDomain (.fvar top) (.fvar g)))
    (hm : ND.Proof Γ (mem (.fvar a) (.fvar x))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar x)) :=
  mp (mp hm (andLeft (Ordinal.successorAt top a x hs))) (andRight (graphDomainAt top g x hd))

def domainExtensionAt {Γ : List Form} (E : FormulaEquality Γ) (top a b g h x : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar a)))
    (hd : ND.Proof Γ (graphDomain (.fvar top) (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (sourceIff (hasOutput (.fvar h) (.fvar x))
      (mem (.fvar a) (.fvar x) ⋎ eq (.fvar x) (.fvar a))) := by
  apply andIntro
  · apply impIntro
    let q : Form := hasOutput (.fvar h) (.fvar x)
    have hc := outputExtensionForward g h a b x (up hx q) (assumption (by simp [q]))
    apply orElim hc
    · exact ND.orLeft (oldOutputMember top a g x (up (up hs q) _) (up (up hd q) _)
        (assumption (by simp)))
    · exact ND.orRight (assumption (by simp))
  · apply impIntro
    let q : Form := mem (.fvar a) (.fvar x) ⋎ eq (.fvar x) (.fvar a)
    have hc : ND.Proof (q::Γ) q := assumption (by simp)
    apply orElim hc
    · have ho := newMemberOutput top a g x (up (up hs q) (mem (.fvar a) (.fvar x)))
        (up (up hd q) _) (assumption (by simp))
      exact preservesOutput g h a b x (up (up hx q) _) ho
    · let EE := E.weaken (fun r hr => List.mem_cons_of_mem (eq (.fvar x) (.fvar a))
        (List.mem_cons_of_mem q hr))
      exact insertedOutput EE g h a b x (up (up hx q) _) (assumption (by simp))

def successorGraphDomain {Γ : List Form} (E : FormulaEquality Γ) (top a b g h : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar a)))
    (hd : ND.Proof Γ (graphDomain (.fvar top) (.fvar g)))
    (hx : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar a) (.fvar b))) :
    ND.Proof Γ (graphDomain (.fvar a) (.fvar h)) := by
  apply allIntro
  have result := domainExtensionAt E.shifted (top+1) (a+1) (b+1) (g+1) (h+1) 0
    (Ordinal.successorShift top a hs) (graphDomainShift top g hd) (exactShift g h a b hx)
  convert result using 1 <;> (dsimp only [hasOutput] <;> traceSyntax)

#print axioms domainExtensionAt
#print axioms successorGraphDomain
end M6.PA.RelationalSource.PairGraph
