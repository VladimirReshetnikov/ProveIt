import PA194AddRightZeroBase
import PA194FoundationOrdinalInductionUniform
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194AddRightZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.zero

def base {Γ : List Form} (E : FormulaEquality Γ) (x : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x))) : ND.Proof Γ (rightZero (.fvar x)) := by
  unfold rightZero
  apply ND.allIntro
  apply ND.allIntro
  let d : Form := Ordinal.zero (.fvar 1) ⋏ addResult (.fvar (x+1+1)) (.fvar 1) (.fvar 0)
  have hd : ND.Proof (d::ND.shifted (ND.shifted Γ)) d := ND.assumption (by simp)
  let inc : ∀ p, p ∈ ND.shifted (ND.shifted Γ) → p ∈ d :: ND.shifted (ND.shifted Γ) := fun p hp => List.mem_cons_of_mem d hp
  have out := basePoint (E.shifted.shifted.weaken inc) (x+1+1) 1 0
    (ND.weaken (Ordinal.zeroShift (x+1) (Ordinal.zeroShift x hx)) inc) (ND.andLeft hd) (ND.andRight hd)
  convert ND.impIntro out using 1 <;> (dsimp [d,point] <;>
    simp only [Semiformula.free,Rewriting.free,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      addResult_rew,orderIso_rew,Ordinal.zero_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq,Semiformula.rewAux_neg,addResult_rew,orderIso_rew,Ordinal.zero_rew,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax

def inductionBase {Γ : List Form} (E : FormulaEquality Γ) : ND.Proof Γ (Ordinal.inductionBase property) := by
  apply ND.allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::ND.shifted Γ) d := ND.assumption (by simp)
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ d :: ND.shifted Γ := fun p hp => List.mem_cons_of_mem d hp
  have out := base (E.shifted.weaken inc) 0 (ND.andRight hd)
  convert ND.impIntro out using 1 <;> (dsimp [d,Ordinal.inductionBase,property,rightZero,point] <;>
    simp only [Semiformula.free,Rewriting.free,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
      addResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq,Semiformula.rewAux_neg,addResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax
#print axioms base
#print axioms inductionBase
end PA194AddRightZero
