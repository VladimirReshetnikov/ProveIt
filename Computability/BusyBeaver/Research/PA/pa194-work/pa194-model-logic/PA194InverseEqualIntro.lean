import PA194FoundationInverseSymmetry
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194InverseEqual
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def equalAt (a b : Nat) : Form := ∃⁰ ∃⁰
  ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ orderIso (.bvar 1) (.bvar 0)))

def equalFromWitnesses (a b x y : Nat)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x) ⋏ eq (.fvar x) (.fvar a)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y) ⋏ eq (.fvar y) (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar x) (.fvar y))) : ND.Proof Γ (equalAt a b) := by
  let P : Ordinal.Formula 1 := ∃⁰
    ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ orderIso (.bvar 1) (.bvar 0)))
  let Q : Ordinal.Formula 1 :=
    ((Ordinal.domain (.fvar x) ⋏ eq (.fvar x) (.fvar a)) ⋏
      ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (.fvar b)) ⋏ orderIso (.fvar x) (.bvar 0)))
  apply ND.exsIntro P (.fvar x)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar y)
    have hh := ND.andIntro hx (ND.andIntro hy hi)
    convert hh using 1
    simp [Q,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.subst,Rew.func,Rew.q]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.subst,Rew.func,Rew.q]

theorem equalAt_shift (a b : Nat) : (equalAt a b).shift = equalAt (a+1) (b+1) := by
  change Semiformula.rewAux Rew.shift (equalAt a b) = _
  simp [equalAt,Semiformula.rewAux,domain_rew,orderIso_rew,eq,Rew.shift,Rew.map,Rew.q]
#print axioms equalFromWitnesses
#print axioms equalAt_shift
end PA194InverseEqual
