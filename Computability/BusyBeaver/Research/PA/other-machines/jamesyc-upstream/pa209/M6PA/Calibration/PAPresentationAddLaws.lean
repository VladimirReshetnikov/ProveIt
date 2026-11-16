module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationMulZeroOne
@[expose] public section

/-! Reusable finite proof data for the already-derived addition laws. -/
namespace M6.PA.Presentation
open FFL FFL.FirstOrder

namespace EqualityPremises
def additionOf {Γ : List ND.Form} (E : EqualityPremises Γ)
    {a b c d : GroundTerm} (h : ND.Proof Γ (eq a b)) (k : ND.Proof Γ (eq c d)) :
    ND.Proof Γ (eq (Presentation.add a c) (Presentation.add b d)) :=
  ND.mp k (ND.mp h (E.addition a b c d))
def multiplicationOf {Γ : List ND.Form} (E : EqualityPremises Γ)
    {a b c d : GroundTerm} (h : ND.Proof Γ (eq a b)) (k : ND.Proof Γ (eq c d)) :
    ND.Proof Γ (eq (Presentation.mul a c) (Presentation.mul b d)) :=
  ND.mp k (ND.mp h (E.multiplication a b c d))
end EqualityPremises

structure AddLaws (Γ : List ND.Form) where
  assoc : ∀ a b c : GroundTerm, ND.Proof Γ (eq (add (add a b) c) (add a (add b c)))
  comm : ∀ a b : GroundTerm, ND.Proof Γ (eq (add a b) (add b a))

namespace AddLaws
def weaken {Γ Δ : List ND.Form} (A : AddLaws Γ) (h : ∀ p,p ∈ Γ → p ∈ Δ) : AddLaws Δ where
  assoc a b c := ND.weaken (A.assoc a b c) h
  comm a b := ND.weaken (A.comm a b) h

def medial {Γ : List ND.Form} (A : AddLaws Γ) (E : EqualityPremises Γ)
    (a b c d : GroundTerm) : ND.Proof Γ
      (eq (add (add a b) (add c d)) (add (add a c) (add b d))) := by
  have h1 := A.assoc a b (add c d)
  have h2 := E.additionOf (E.reflexive a) (E.symmetryOf (A.assoc b c d))
  have h3 := E.additionOf (E.reflexive a)
    (E.additionOf (A.comm b c) (E.reflexive d))
  have h4 := E.additionOf (E.reflexive a) (A.assoc c b d)
  have h5 := E.symmetryOf (A.assoc a c (add b d))
  exact E.transitivityOf (E.transitivityOf (E.transitivityOf (E.transitivityOf h1 h2) h3) h4) h5
end AddLaws

def addLawsContext : List ND.Form :=
  equalityContext ++ (closedContext assocContext ++ closedContext commContext)

def derivedAddLaws : AddLaws addLawsContext where
  assoc a b c := by
    have d := ND.closeIter (closedContext_closed assocContext)
      (ND.replaceByClosures assocCertificate) 2
    have h := ND.allElim3 _ a b c d
    have hp : ND.Proof (closedContext assocContext) (eq (add (add a b) c) (add a (add b c))) := by
      convert h using 1 <;> dsimp [closureIter,assocProperty] <;> equalityInstanceSyntax
    exact ND.weaken hp (by intro p hp; simp [addLawsContext,hp])
  comm a b := by
    have d := ND.closeIter (closedContext_closed commContext)
      (ND.replaceByClosures commCertificate) 1
    have h := ND.allElim2 _ a b d
    have hp : ND.Proof (closedContext commContext) (eq (add a b) (add b a)) := by
      convert h using 1 <;> dsimp [closureIter,commProperty] <;> equalityInstanceSyntax
    exact ND.weaken hp (by intro p hp; simp [addLawsContext,hp])

theorem addLawsContext_mem_theory (p : ND.Form) (hp : p ∈ addLawsContext) :
    p.univCl ∈ ordinaryPAeq := by
  simp only [addLawsContext,List.mem_append] at hp
  rcases hp with hp | hp | hp
  · exact ⟨p,equalityContext_is_PAeq p hp,rfl⟩
  · exact closedContext_mem_theory (T := ordinaryPAeq)
      (fun q hq => ⟨q,assocContext_is_PAeq q hq,rfl⟩) p hp
  · exact closedContext_mem_theory commContext_mem_theory p hp

#print axioms derivedAddLaws
#print axioms AddLaws.medial
end M6.PA.Presentation
