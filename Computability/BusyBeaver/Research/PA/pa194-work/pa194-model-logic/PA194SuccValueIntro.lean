import PA194SuccEqualSyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def succValueIntro (x pred out : Nat)
    (hp : ND.Proof Γ (Ordinal.domain (.fvar pred) ⋏ eq (.fvar pred) (.fvar x)))
    (ho : ND.Proof Γ (Ordinal.domain (.fvar out)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar pred) (.fvar out))) : ND.Proof Γ (succValue x out) := by
  apply ND.andIntro ho
  let P : Ordinal.Formula 1 := (Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar x)) ⋏
    Ordinal.successor (.bvar 0) (.fvar out)
  apply ND.exsIntro P (.fvar pred)
  have hh := ND.andIntro hp hs
  convert hh using 1
  simp [P,Semiformula.rewAux,domain_rew,successor_rew,eq,Rew.subst,Rew.q,Rew.func]

def succEqualFromWitnesses (a b x y : Nat)
    (hx : ND.Proof Γ (succValue a x)) (hy : ND.Proof Γ (succValue b y))
    (hi : ND.Proof Γ (orderIso (.fvar x) (.fvar y))) : ND.Proof Γ (succEqualAt a b) := by
  let P : Ordinal.Formula 1 := ∃⁰ (succValueTerm (.fvar a) (.bvar 1) ⋏
    (succValueTerm (.fvar b) (.bvar 0) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let Q : Ordinal.Formula 1 := succValueTerm (.fvar a) (.fvar x) ⋏
    (succValueTerm (.fvar b) (.bvar 0) ⋏ orderIso (.fvar x) (.bvar 0))
  apply ND.exsIntro P (.fvar x)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar y)
    have hh := ND.andIntro hx (ND.andIntro hy hi)
    convert hh using 1
    simp [Q,Semiformula.rewAux,succValueTerm_rew,succValueTerm_fvar,orderIso_rew,Rew.subst,Rew.func,Rew.q]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,succValueTerm_rew,succValueTerm_fvar,orderIso_rew,Rew.subst,Rew.func,Rew.q]
#print axioms succValueIntro
#print axioms succEqualFromWitnesses
end PA194SuccInjective
