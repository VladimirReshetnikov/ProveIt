module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalTrace
public import M6PA.Calibration.RelationalPredicateTemplateLiftOrdinal
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND
macro "templateSuccessorSyntax" : tactic => `(tactic|
  (simp only [successor,sourceIff]; templateOrdinalSyntax))
def memberShift {Γ : List Form} (a b : Nat)
    (d : ND.Proof Γ (mem (.fvar a) (.fvar b))) :
    ND.Proof (shifted Γ) (mem (.fvar (a+1)) (.fvar (b+1))) := by
  convert shiftProof d using 1 ; templateOrdinalSyntax

def domainShift {Γ : List Form} (a : Nat)
    (d : ND.Proof Γ (domain (.fvar a))) :
    ND.Proof (shifted Γ) (domain (.fvar (a+1))) := by
  convert shiftProof d using 1 ; templateOrdinalSyntax

def successorAt {Γ : List Form} (i j k : Nat)
    (d : ND.Proof Γ (successor (.fvar i) (.fvar j))) :
    ND.Proof Γ (sourceIff (mem (.fvar j) (.fvar k))
      (mem (.fvar i) (.fvar k) ⋎ eq (.fvar k) (.fvar i))) := by
  convert allElim _ (.fvar k) d using 1 ; templateSuccessorSyntax

def transitiveAt {Γ : List Form} (i j k : Nat)
    (d : ND.Proof Γ (transitive (.fvar i)))
    (hx : ND.Proof Γ (mem (.fvar i) (.fvar j)))
    (hy : ND.Proof Γ (mem (.fvar j) (.fvar k))) :
    ND.Proof Γ (mem (.fvar i) (.fvar k)) := by
  have h : ND.Proof Γ ((mem (.fvar i) (.fvar j) ⋏ mem (.fvar j) (.fvar k)) 🡒
      mem (.fvar i) (.fvar k)) := by
    convert allElim _ (.fvar k) (allElim _ (.fvar j) d) using 1 ; templateOrdinalSyntax
  exact mp (andIntro hx hy) h

def nonemptyIntro {Γ : List Form} (s x : Nat)
    (d : ND.Proof Γ (mem (.fvar s) (.fvar x))) : ND.Proof Γ (nonempty (.fvar s)) := by
  apply exsIntro _ (.fvar x)
  convert d using 1 ; templateOrdinalSyntax

def leastShift {Γ : List Form} (s m : Nat) (d : ND.Proof Γ (least (.fvar s) (.fvar m))) :
    ND.Proof (shifted Γ) (least (.fvar (s+1)) (.fvar (m+1))) := by
  convert shiftProof d using 1 ; templateOrdinalSyntax

def leastMemberGood {Γ : List Form} (e : EqualityProofs Γ) (c b m : Nat) (q : Form)
    (hb : ND.Proof Γ (domain (.fvar b)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar m)))
    (hbad : ND.Proof Γ (∼q 🡒 mem (.fvar c) (.fvar m))) : ND.Proof Γ q := by
  apply byContradiction
  exact contradiction (mp (assumption (by simp)) (up hbad _))
    (up (leastExcludesMember e c b m hb hl hm) _)


def internalExtremaAt {Γ : List Form} (a c : Nat)
    (d : ND.Proof Γ (internalExtrema (.fvar a)))
    (hc : ND.Proof Γ (subset (.fvar c) (.fvar a)))
    (hne : ND.Proof Γ (nonempty (.fvar c))) :
    ND.Proof Γ ((∃¹ least (Rew.bShift (.fvar c : Term 0)) (.bvar 0)) ⋏
      (∃¹ greatest (Rew.bShift (.fvar c : Term 0)) (.bvar 0))) := by
  have hd := allElim _ (.fvar c) d
  have hh : ND.Proof Γ ((subset (.fvar c) (.fvar a) ⋏ nonempty (.fvar c)) 🡒
      ((∃¹ least (Rew.bShift (.fvar c : Term 0)) (.bvar 0)) ⋏
      (∃¹ greatest (Rew.bShift (.fvar c : Term 0)) (.bvar 0)))) := by
    convert hd using 1
    templateOrdinalSyntax
  exact mp (andIntro hc hne) hh
#print axioms internalExtremaAt
#print axioms leastMemberGood
#print axioms successorAt
end M6.PA.RelationalPredicateTemplate.Ordinal
