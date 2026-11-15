import PA194MulZeroEdgeRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}
attribute [local irreducible] mulPrefix addResult

def resultFromPoint (a base g : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hp : ND.Proof Γ (pointGraph (.fvar a) (.fvar a) (.fvar g))) :
    ND.Proof Γ (mulResult (.fvar a) (.fvar base) (.fvar a)) := by
  have hprefix := pointMulPrefix a base g E hz hd hp
  have he := ND.mp (ND.andIntro (E.reflexive (.fvar a)) (E.reflexive (.fvar a)))
    (ND.andRight (pointAt a a g a a hp))
  let P : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (.fvar a) (.fvar base) (.bvar 1) (.bvar 0) ⋏ edge (.bvar 0) (.fvar a) (.fvar a)))
  let Q : Ordinal.Formula 1 := Ordinal.zero (.fvar a) ⋏
    (mulPrefix (.fvar a) (.fvar base) (.fvar a) (.bvar 0) ⋏ edge (.bvar 0) (.fvar a) (.fvar a))
  change ND.Proof Γ (∃⁰ P)
  apply ND.exsIntro P (.fvar a)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar g)
    have hh := ND.andIntro hz (ND.andIntro hprefix he)
    convert hh using 1
    simp [Q,Semiformula.rewAux,zero_rew,mulPrefix_rew,edge_rew,Rew.subst,Rew.q,Rew.func]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,zero_rew,mulPrefix_rew,edge_rew,Rew.subst,Rew.q,Rew.func]
#print axioms resultFromPoint
end PA194ForwardMulZero
