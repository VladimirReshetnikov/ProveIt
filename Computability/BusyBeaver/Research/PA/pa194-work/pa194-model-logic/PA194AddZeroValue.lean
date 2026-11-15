import PA194AddZeroIso
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardAddZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def valueAt (b out : Nat) : Form := Ordinal.domain (.fvar out) ⋏
  (∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏
      addResult (.bvar 1) (.bvar 0) (.fvar out))))

def valueFromWitnesses (a b out : Nat) (E : FormulaEquality Γ)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b))) (ho : ND.Proof Γ (Ordinal.domain (.fvar out)))
    (hr : ND.Proof Γ (addResult (.fvar a) (.fvar b) (.fvar out))) : ND.Proof Γ (valueAt b out) := by
  apply ND.andIntro ho
  let P : Ordinal.Formula 1 := ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ Ordinal.zero (.bvar 1)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ addResult (.bvar 1) (.bvar 0) (.fvar out)))
  let Q : Ordinal.Formula 1 := (Ordinal.domain (.fvar a) ⋏ Ordinal.zero (.fvar a)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ addResult (.fvar a) (.bvar 0) (.fvar out))
  have hbase : ND.Proof Γ ((Ordinal.domain (.fvar a) ⋏ Ordinal.zero (.fvar a)) ⋏
    ((Ordinal.domain (.fvar b) ⋏ eq (.fvar b) (.fvar b)) ⋏ addResult (.fvar a) (.fvar b) (.fvar out))) :=
      ND.andIntro (ND.andIntro ha hz) (ND.andIntro (ND.andIntro hb (E.reflexive (.fvar b))) hr)
  apply ND.exsIntro P (.fvar a)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar b)
    convert hbase using 1
    simp [Q,Semiformula.rewAux,domain_rew,zero_rew,addResult_rew,eq,Rew.subst,Rew.func,Rew.q]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,domain_rew,zero_rew,addResult_rew,eq,Rew.subst,Rew.func,Rew.q]
#print axioms valueFromWitnesses
end PA194ForwardAddZero
