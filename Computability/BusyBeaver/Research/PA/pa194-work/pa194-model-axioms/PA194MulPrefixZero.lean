import PA194MulZeroExistence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulPrefixZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero
attribute [local irreducible] mulPrefix addResult

def mulPrefixExists {n : Nat} (top base : Term n) : Formula n :=
  ∃⁰ ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (Rew.bShift (Rew.bShift top)) (Rew.bShift (Rew.bShift base)) (.bvar 1) (.bvar 0))

def prefixExistsIntro {Γ : List Form} (top base z g : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulPrefix (.fvar top) (.fvar base) (.fvar z) (.fvar g))) :
    ND.Proof Γ (mulPrefixExists (.fvar top) (.fvar base)) := by
  let P : Ordinal.Formula 1 := ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (.fvar top) (.fvar base) (.bvar 1) (.bvar 0))
  let Q : Ordinal.Formula 1 := Ordinal.zero (.fvar z) ⋏
    mulPrefix (.fvar top) (.fvar base) (.fvar z) (.bvar 0)
  change ND.Proof Γ (∃⁰ P)
  apply ND.exsIntro P (.fvar z)
  have hq : ND.Proof Γ (∃⁰ Q) := by
    apply ND.exsIntro Q (.fvar g)
    have hh := ND.andIntro hz hp
    convert hh using 1
    simp [Q,Semiformula.rewAux,zero_rew,mulPrefix_rew,Rew.subst,Rew.q,Rew.func]
  convert hq using 1
  simp [P,Q,Semiformula.rewAux,zero_rew,mulPrefix_rew,Rew.subst,Rew.q,Rew.func]

def zeroPrefixWitness {Γ : List Form} (E : FormulaEquality Γ) (a base : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (mulPrefixExists (.fvar a) (.fvar base)) := by
  apply ND.exsElim (pointWitness E a a hempty hadj)
  let P : Ordinal.Formula 1 := pointGraph (.fvar a) (.fvar a) (.bvar 0)
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ (pointGraph (.fvar (a+1)) (.fvar (a+1)) (.fvar 0)) := by
    have h := ND.assumption (Γ := Δ) (p := P.free) (by simp [Δ])
    convert h using 1 <;> (dsimp [P] <;> traceSyntax)
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have hz' := ND.up (Ordinal.zeroShift a hz) P.free
  have hd' := Ordinal.zeroDomain (.fvar (a+1)) hz'
  have hm := pointMulPrefix (a+1) (base+1) 0 E' hz' hd' hp
  have out := prefixExistsIntro (a+1) (base+1) (a+1) 0 hz' hm
  convert out using 1 <;> (dsimp [Δ,P,mulPrefixExists] <;> traceSyntax)
  simp only [mulPrefix_rew,Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app]
  rfl
#print axioms prefixExistsIntro
#print axioms zeroPrefixWitness
end PA194MulPrefixZero
