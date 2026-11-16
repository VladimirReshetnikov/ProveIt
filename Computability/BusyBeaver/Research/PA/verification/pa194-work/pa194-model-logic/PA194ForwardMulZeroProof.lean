import PA194MulZeroDomain
import PA194ForwardTyped
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped
variable {Γ : List Form}

def target : Form := formula PA194PAeq.mulZero
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def proof (E : FormulaEquality Γ) (hempty : ND.Proof Γ emptyFormula)
    (hadj : ND.Proof Γ adjunctionFormula) (orderRefl : ND.Proof Γ orderIsoReflexivityStatement) :
    ND.Proof Γ target := by
  unfold target
  change ND.Proof Γ (∀⁰ _)
  apply ND.allIntro
  let Δ := Ordinal.domain (.fvar 0) :: ND.shifted Γ
  have hd : ND.Proof Δ (Ordinal.domain (.fvar 0)) := ND.assumption (by simp [Δ])
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have he := ND.up (emptyClosedShift hempty) (Ordinal.domain (.fvar 0))
  have hj := ND.up (adjunctionClosedShift hadj) (Ordinal.domain (.fvar 0))
  have ho : ND.Proof Δ orderIsoReflexivityStatement := by
    have h' : ND.Proof Δ orderIsoReflexivityStatement.shift :=
      ND.weaken (ND.shiftProof orderRefl) (fun _ hp => List.mem_cons_of_mem _ hp)
    convert h' using 1 <;> (try simp only [orderIsoReflexivityStatement] <;> isoSyntax)
  have h := ND.impIntro (equalFromDomain 0 E' hd ho he hj)
  convert h using 1
  simp [formula,PA194PAeq.mulZero,PA194PAeq.eq,PA194PAeq.mul,PA194PAeq.zero,equal,value,
    bindEnv,shiftEnv,equalAt,Semiformula.free,Rewriting.free,Semiformula.rewAux,domain_rew,zero_rew,
    mulResult_rew,orderIso_rew,eq,Rew.free,Rew.q,Rew.func]
  simp [sourceImply,Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux_neg,Semiformula.rewAux,
    domain_rew,zero_rew,mulResult_rew,orderIso_rew,Rew.free,Rew.q,Rew.func]
  change Semiformula.rewAux _ (∼Ordinal.domain (.bvar 0)) = ∼Ordinal.domain (.fvar 0)
  rw [Semiformula.rewAux_neg,domain_rew]
  rfl
#print axioms proof
end PA194ForwardMulZero
