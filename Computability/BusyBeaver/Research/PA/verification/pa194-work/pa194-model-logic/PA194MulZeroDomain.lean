import PA194MulZeroShift
import PA194ForwardReflProof
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def equalFromDomain (b : Nat) (E : FormulaEquality Γ)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (orderRefl : ND.Proof Γ orderIsoReflexivityStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) : ND.Proof Γ (equalAt b) := by
  apply ND.exsElim hempty
  let Q : Ordinal.Formula 1 := Ordinal.zero (.bvar 0)
  let Δ := Q.free :: ND.shifted Γ
  have hz : ND.Proof Δ (Ordinal.zero (.fvar 0)) := by
    have h := ND.assumption (Γ := Δ) (p := Q.free) (by simp [Δ])
    convert h using 1 <;> (dsimp [Q] <;> ordinalSyntax)
  have ha : ND.Proof Δ (Ordinal.domain (.fvar 0)) := zeroDomain (.fvar 0) hz
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have hb' := ND.up (Ordinal.domainShift b hb) Q.free
  have ho : ND.Proof Δ orderIsoReflexivityStatement := by
    have h' : ND.Proof Δ orderIsoReflexivityStatement.shift :=
      ND.weaken (ND.shiftProof orderRefl) (fun _ hp => List.mem_cons_of_mem _ hp)
    convert h' using 1 <;> (try simp only [orderIsoReflexivityStatement] <;> isoSyntax)
  have hi : ND.Proof Δ (orderIso (.fvar 0) (.fvar 0)) := by
    have h := ND.allElim _ (.fvar 0) ho
    have hh : ND.Proof Δ (Ordinal.domain (.fvar 0) 🡒 orderIso (.fvar 0) (.fvar 0)) := by
      convert h using 1
      change _ = Semiformula.rewAux _ _
      simp only [Semiformula.imp_eq,Semiformula.neg_eq,Semiformula.rewAux]
      all_goals isoSyntax
    exact ND.mp ha hh
  have he := ND.up (emptyClosedShift hempty) Q.free
  have hj := ND.up (adjunctionClosedShift hadj) Q.free
  have hr := resultFromZero 0 (b+1) E' hz he hj
  change ND.Proof Δ (equalAt b).shift
  rw [equalAt_shift]
  exact equalFromZero 0 (b+1) E' ha hz hb' hr hi
#print axioms equalFromDomain
end PA194ForwardMulZero
