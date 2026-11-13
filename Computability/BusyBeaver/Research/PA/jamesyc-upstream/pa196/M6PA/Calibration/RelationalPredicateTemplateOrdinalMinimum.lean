module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalRules
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate.Ordinal
open FFL FFL.FirstOrder ND
def predicateTraceMinimum {Γ : List Form} (p : Formula 1) (s c a : Nat)
    (hs : ND.Proof Γ (domain (.fvar s)))
    (hc : ND.Proof Γ (predicateTrace p (.fvar s) (.fvar c)))
    (ha : ND.Proof Γ (mem (.fvar s) (.fvar a)))
    (hp : ND.Proof Γ (p/[.fvar a])) : ND.Proof Γ ((∃¹ least (Rew.bShift (.fvar c : Term 0)) (.bvar 0))) :=
  andLeft (internalExtremaAt s c (andRight (andRight (andRight (andLeft hs))))
    (predicateTraceSubset p s c hc)
    (nonemptyIntro c a (mp (andIntro ha hp) (andRight (predicateTraceAt p s c a hc)))))

def badTraceMemberGood {Γ : List Form} (e : EqualityProofs Γ) (p : Formula 1) (s c b m : Nat)
    (hs : ND.Proof Γ (domain (.fvar s)))
    (hc : ND.Proof Γ (predicateTrace (∼p) (.fvar s) (.fvar c)))
    (hl : ND.Proof Γ (least (.fvar c) (.fvar b)))
    (hm : ND.Proof Γ (mem (.fvar b) (.fvar m))) : ND.Proof Γ (p/[.fvar m]) := by
  have hb := andLeft (mp (andLeft hl) (andLeft (predicateTraceAt (∼p) s c b hc)))
  have hbm := transitiveAt s b m (andLeft (andLeft hs)) hb hm
  have hbad : ND.Proof Γ (∼(p/[.fvar m]) 🡒 mem (.fvar c) (.fvar m)) := by
    apply impIntro
    have hn : ND.Proof (∼(p/[.fvar m]) :: Γ) ((∼p)/[.fvar m]) := by
      simpa using (assumption (p := ∼(p/[.fvar m])) (by simp))
    exact mp (andIntro (up hbm _) hn) (up (andRight (predicateTraceAt (∼p) s c m hc)) _)
  exact leastMemberGood e c b m (p/[.fvar m]) (memberDomain s b hs hb) hl hm hbad

#print axioms predicateTraceMinimum
#print axioms badTraceMemberGood
end M6.PA.RelationalPredicateTemplate.Ordinal
