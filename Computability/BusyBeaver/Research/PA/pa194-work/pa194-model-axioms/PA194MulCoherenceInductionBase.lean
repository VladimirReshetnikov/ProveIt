import PA194MulCoherenceZeroCase
import PA194FoundationOrdinalInductionUniform
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
namespace PA194MulCoherence
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardMulZero PA194MulRecurrenceNew
attribute [local irreducible] mulResult orderIso Ordinal.domain

def inductionBase {Γ : List Form} (E : FormulaEquality Γ) :
    ND.Proof Γ (Ordinal.inductionBase property) := by
  apply ND.allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: ND.shifted Γ) d := ND.assumption (by simp)
  let inc : ∀ p, p ∈ ND.shifted Γ → p ∈ d :: ND.shifted Γ := fun p hp => List.mem_cons_of_mem d hp
  have out := zeroCase (E.shifted.weaken inc) 0 (ND.andRight hd)
  have h := ND.impIntro out
  convert h using 1 <;>
    (dsimp [d,Ordinal.inductionBase,property,coherence] <;>
      simp only [point,premise,mulResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,
        Semiformula.free,Rewriting.free,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
        Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ] <;> finishSourceSyntax)
  all_goals simp only [← Semiformula.neg_eq, Semiformula.rewAux_neg, mulResult_rew, orderIso_rew,
    Ordinal.domain_rew,Ordinal.zero_rew,Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  all_goals finishSourceSyntax
#print axioms inductionBase
end PA194MulCoherence
