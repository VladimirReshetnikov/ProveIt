import PA194AddZeroOutput
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardAddZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def equalFromDomain (b : Nat) (E : FormulaEquality Γ)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar b) (.fvar b)))
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
  have hi' : ND.Proof Δ (orderIso (.fvar (b+1)) (.fvar (b+1))) := by
    have h := ND.up (ND.shiftProof hi) Q.free
    convert h using 1
    change _ = Semiformula.rewAux Rew.shift _
    simp [orderIso_rew,Rew.shift,Rew.map]
  have he := ND.up (emptyClosedShift hempty) Q.free
  have hj := ND.up (adjunctionClosedShift hadj) Q.free
  have hout := outputOfZeroAdd 0 (b+1) E' hz hb' he hj
  change ND.Proof Δ (equalAt b).shift
  rw [equalAt_shift]
  exact equalFromOutput 0 (b+1) E' ha hz hb' hi' hout
#print axioms equalFromDomain
end PA194ForwardAddZero
