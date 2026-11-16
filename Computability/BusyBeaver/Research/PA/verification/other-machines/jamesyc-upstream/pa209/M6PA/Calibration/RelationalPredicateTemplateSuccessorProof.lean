module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorSyntax
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder ND Ordinal

def pack {Γ : List ND.Form} (x y : Nat)
    (hd : ND.Proof Γ (domain (.fvar y)))
    (hp : ND.Proof Γ (pred (.fvar x)))
    (hs : ND.Proof Γ (successor (.fvar x) (.fvar y))) : ND.Proof Γ output := by
  apply exsIntro outputBody (.fvar y)
  have hx : ND.Proof Γ (∃¹ (pred (.bvar 0) ⋏ successor (.bvar 0) (.fvar y))) := by
    apply exsIntro (pred (.bvar 0) ⋏ successor (.bvar 0) (.fvar y)) (.fvar x)
    convert andIntro hp hs using 1 <;> first | rfl | successorTemplateSyntax
  convert andIntro hd hx using 1 <;> first | rfl | successorTemplateSyntax

def step {Γ : List ND.Form}
    (hp : ND.Proof Γ (pred (.fvar 0)))
    (hs : ND.Proof Γ (∃¹ (domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0)))) :
    ND.Proof Γ output := by
  apply exsElim hs
  have hpair : ND.Proof ((domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0)).free :: shifted Γ)
      (domain (.fvar 0) ⋏ successor (.fvar 1) (.fvar 0)) := by
    convert (assumption (Γ:=((domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0)).free :: shifted Γ))
      (p:=(domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0)).free) (by simp)) using 1
    successorTemplateSyntax
  have hd := andLeft hpair
  have hsucc := andRight hpair
  have hp' : ND.Proof ((domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0)).free :: shifted Γ)
      (pred (.fvar 1)) := by
    convert ND.up (shiftProof hp) _ using 1 <;> first | rfl | successorTemplateSyntax
  convert pack 1 0 hd hp' hsucc using 1 <;> first | rfl | successorTemplateSyntax

def derivation : ND.Proof [closure] statement := by
  apply impIntro
  apply exsElim (p:=inputBody) (assumption (p:=input) (by simp))
  have hd : ND.Proof (inputBody.free :: shifted [input,closure]) (domain (.fvar 0)) := by
    convert andLeft (assumption (Γ:=(inputBody.free :: shifted [input,closure])) (p:=inputBody.free) (by simp)) using 1 <;> first | rfl | successorTemplateSyntax
  have hp : ND.Proof (inputBody.free :: shifted [input,closure]) (pred (.fvar 0)) := by
    convert andRight (assumption (Γ:=(inputBody.free :: shifted [input,closure])) (p:=inputBody.free) (by simp)) using 1 <;> first | rfl | successorTemplateSyntax
  have hc : ND.Proof (inputBody.free :: shifted [input,closure]) closure := by
    have h := ND.up (shiftProof (assumption (Γ:=[input,closure]) (p:=closure) (by simp))) inputBody.free
    convert h using 1 <;> first | rfl | successorTemplateSyntax
  have hi : ND.Proof (inputBody.free :: shifted [input,closure])
      (domain (.fvar 0) 🡒 ∃¹ (domain (.bvar 0) ⋏ successor (.fvar 0) (.bvar 0))) := by
    convert allElim closureBody (.fvar 0) hc using 1 <;> first | rfl | successorTemplateSyntax
  convert step hp (mp hd hi) using 1 <;> first | rfl | successorTemplateSyntax

#print axioms pack
#print axioms step
#print axioms derivation
end M6.PA.RelationalPredicateTemplate.Successor

