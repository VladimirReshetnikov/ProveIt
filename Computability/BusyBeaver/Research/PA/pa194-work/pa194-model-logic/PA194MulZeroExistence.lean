import PA194MulZeroResult
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def resultFromZero (a base : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (mulResult (.fvar a) (.fvar base) (.fvar a)) := by
  apply ND.exsElim (pointWitness E a a hempty hadj)
  let P : Ordinal.Formula 1 := pointGraph (.fvar a) (.fvar a) (.bvar 0)
  let Δ := P.free :: ND.shifted Γ
  have hp : ND.Proof Δ (pointGraph (.fvar (a+1)) (.fvar (a+1)) (.fvar 0)) := by
    have h := ND.assumption (Γ := Δ) (p := P.free) (by simp [Δ])
    convert h using 1 <;> (dsimp [P] <;> traceSyntax)
  have E' : FormulaEquality Δ := E.shifted.weaken (fun _ hp => List.mem_cons_of_mem _ hp)
  have hz' := ND.up (Ordinal.zeroShift a hz) P.free
  have hd' := Ordinal.zeroDomain (.fvar (a+1)) hz'
  have h := resultFromPoint (a+1) (base+1) 0 E' hz' hd' hp
  change ND.Proof Δ (mulResult (.fvar a) (.fvar base) (.fvar a)).shift
  change ND.Proof Δ (Semiformula.rewAux Rew.shift (mulResult (.fvar a) (.fvar base) (.fvar a)))
  simpa [mulResult_rew,Rew.shift,Rew.map] using h
#print axioms resultFromZero
end PA194ForwardMulZero
