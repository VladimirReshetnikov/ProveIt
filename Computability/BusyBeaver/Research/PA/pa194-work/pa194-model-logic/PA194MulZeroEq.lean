import PA194MulZeroValue
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def equalAt (b : Nat) : Form := ∃⁰ ∃⁰
  ((Ordinal.domain (.bvar 1) ⋏ (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ mulResult (.bvar 1) (.bvar 0) (.bvar 3))))) ⋏
  ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))

def equalFromZero (a b : Nat) (E : FormulaEquality Γ)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (mulResult (.fvar a) (.fvar b) (.fvar a)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar a))) : ND.Proof Γ (equalAt b) := by
  have hv := valueFromWitnesses a b a E ha hz hb ha hr
  have hbase : ND.Proof Γ (valueAt b a ⋏
      ((Ordinal.domain (.fvar a) ⋏ Ordinal.zero (.fvar a)) ⋏ orderIso (.fvar a) (.fvar a))) :=
    ND.andIntro hv (ND.andIntro (ND.andIntro ha hz) hi)
  let P : Ordinal.Formula 1 := ∃⁰
    ((Ordinal.domain (.bvar 1) ⋏ (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ mulResult (.bvar 1) (.bvar 0) (.bvar 3))))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let Q : Ordinal.Formula 1 :=
    ((Ordinal.domain (.fvar a) ⋏ (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ mulResult (.bvar 1) (.bvar 0) (.fvar a))))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.fvar a) (.bvar 0)))
  apply ND.exsIntro P (.fvar a)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar a)
    convert hbase using 1
    simp [Q,valueAt,Semiformula.rewAux,domain_rew,zero_rew,mulResult_rew,orderIso_rew,eq,Rew.subst,Rew.func,Rew.q]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,domain_rew,zero_rew,mulResult_rew,orderIso_rew,eq,Rew.subst,Rew.func,Rew.q]
#print axioms equalFromZero
end PA194ForwardMulZero
