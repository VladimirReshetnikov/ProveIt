import PA194ZeroSuccEqFalse
import PA194ForwardTyped
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardZeroSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped
variable {Γ : List Form}

def target : Form := formula PA194PAeq.zeroNotSucc
  (Fin.elim0 : Fin 0 → Ordinal.Term 0) (fun _ : Nat => (.fvar 0 : Ordinal.Term 0))

def notEqualityAt (a : Nat) (E : FormulaEquality Γ) : ND.Proof Γ (∼zeroSuccEqAt a) := by
  apply ND.byContradiction
  let Δ := ∼∼zeroSuccEqAt a :: Γ
  have he : ND.Proof Δ (zeroSuccEqAt a) := by
    simpa [Δ] using (ND.assumption (Γ := Δ) (p := ∼∼zeroSuccEqAt a) (by simp [Δ]))
  exact equalityFalse a (E.weaken (fun _ hp => List.mem_cons_of_mem _ hp)) he

def proof (E : FormulaEquality Γ) : ND.Proof Γ target := by
  unfold target
  change ND.Proof Γ (∀⁰ _)
  apply ND.allIntro
  let Δ := Ordinal.domain (.fvar 0) :: ND.shifted Γ
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have h := ND.impIntro (notEqualityAt 0 E')
  convert h using 1 <;>
    (simp only [formula,PA194PAeq.zeroNotSucc,PA194PAeq.eq,PA194PAeq.zero,PA194PAeq.succ,equal,value,bindEnv,shiftEnv,zeroSuccEqAt] <;>
      simp only [Ordinal.successor,sourceIff,sourceImply] <;> isoSyntax)
#print axioms notEqualityAt
#print axioms proof
end PA194ForwardZeroSucc
