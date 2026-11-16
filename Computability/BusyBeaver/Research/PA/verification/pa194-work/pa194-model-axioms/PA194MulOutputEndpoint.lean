import PA194MulPrefixExistsStep
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulPrefixZero
attribute [local irreducible] addResult mulPrefix

def mulOutput {n : Nat} (x base : Term n) : Formula n :=
  ∃⁰ (Ordinal.domain (.bvar 0) ⋏ mulResult (Rew.bShift x) (Rew.bShift base) (.bvar 0))

def resultIntro {Γ : List Form} (x base out z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar out))) :
    ND.Proof Γ (mulResult (.fvar x) (.fvar base) (.fvar out)) := by
  let P : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out)))
  let Q : Ordinal.Formula 1 := Ordinal.zero (.fvar z) ⋏
    (mulPrefix (.fvar x) (.fvar base) (.fvar z) (.bvar 0) ⋏ edge (.bvar 0) (.fvar x) (.fvar out))
  change ND.Proof Γ (∃⁰ P)
  apply ND.exsIntro P (.fvar z)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar g)
    have hh := ND.andIntro hz (ND.andIntro hp he)
    convert hh using 1
    simp [Q,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.subst,Rew.q,Rew.func]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,Ordinal.zero_rew,mulPrefix_rew,edge_rew,Rew.subst,Rew.q,Rew.func]

def outputFromEndpoint {Γ : List Form} (x base out z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar x) (.fvar base) (.fvar z) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar out))) :
    ND.Proof Γ (mulOutput (.fvar x) (.fvar base)) := by
  have hpParts := hp
  unfold mulPrefix at hpParts
  have hr := graphRangeAt g x out (ND.andLeft (ND.andRight (ND.andRight hpParts))) he
  have ha := resultIntro x base out z g hz hp he
  apply ND.exsIntro _ (.fvar out)
  convert ND.andIntro hr ha using 1 <;>
    simp [mulOutput,Semiformula.rewAux,Ordinal.domain_rew,mulResult_rew,Rew.subst,Rew.q,Rew.func]
#print axioms resultIntro
#print axioms outputFromEndpoint
end PA194MulRecurrenceNew
