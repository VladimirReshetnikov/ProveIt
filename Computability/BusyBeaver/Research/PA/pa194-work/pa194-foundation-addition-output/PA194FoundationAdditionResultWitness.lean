import PA194FoundationAdditionTotalNumeric
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addPrefix

def addOutput (x y : Term n) : Formula n :=
  ∃⁰ (Ordinal.domain (.bvar 0) ⋏ addResult (Rew.bShift x) (Rew.bShift y) (.bvar 0))

set_option maxHeartbeats 600000 in
def addResultIntro {Γ : List Form} (x y w z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (addPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w))) :
    ND.Proof Γ (addResult (.fvar x) (.fvar y) (.fvar w)) := by
  apply exsIntro _ (.fvar z)
  have h : ND.Proof Γ (∃⁰ (Ordinal.zero (.fvar z) ⋏
      (addPrefix (.fvar x) (.fvar y) (.fvar z) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar w)))) := by
    apply exsIntro _ (.fvar g)
    convert andIntro hz (andIntro hp he) using 1 <;> prefixSyntax
  convert h using 1 <;> prefixSyntax

set_option maxHeartbeats 600000 in
def addOutputFromEndpoint {Γ : List Form} (x y w z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (addPrefix (.fvar x) (.fvar y) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar w))) :
    ND.Proof Γ (addOutput (.fvar x) (.fvar y)) := by
  have hpParts := hp
  unfold addPrefix at hpParts
  have hr := graphRangeAt g x w (andLeft (andRight (andRight hpParts))) he
  have ha := addResultIntro x y w z g hz hp he
  apply exsIntro _ (.fvar w)
  convert andIntro hr ha using 1 <;> prefixSyntax

#print axioms addResultIntro
#print axioms addOutputFromEndpoint
end M6.PA.RelationalSource.PairGraph

