import PA194ADStep
import PA194ADClock
import PackedStandard
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194ADNumericStandard
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch ConfigurationStep PackedClock PackedStandard List.Vector

theorem evalTarget (i : Nat) : eval PA194ADDispatch.targetCode (i ::ᵥ nil) =
    (PA194ADTable.adRows.getD i (0,0,194)).2.2 := by
  rw [PA194ADDispatch.targetCode, evalLookup]
  exact getDMap (fun r : Nat × Nat × Nat => r.2.2) PA194ADTable.adRows i (0,0,194)

theorem evalNextQ (q l r : Nat) :
    eval PA194ADNext.nextQ (q ::ᵥ l ::ᵥ r ::ᵥ nil) =
      (PA194ADTable.next PA194ADTable.adRows (q,l,r)).1 := by
  rw [PA194ADNext.nextQ, evalSelect]
  change (if eval ltBitCode (q ::ᵥ eval (constantCode 194) (q ::ᵥ nil) ::ᵥ nil) = 0 then q else
    eval PA194ADDispatch.targetCode
      (eval addCode (eval addCode (q ::ᵥ q ::ᵥ nil) ::ᵥ eval parityCode (r ::ᵥ nil) ::ᵥ nil) ::ᵥ nil)) = _
  rw [eval_ltBitCode, evalConstant, eval_addCode, eval_addCode, parityEval, evalTarget]
  have hq : q+q = 2*q := by omega
  rw [hq]
  simp only [PA194ADTable.next, PA194ADTable.rowIndex]
  split_ifs <;> simp_all

#print axioms evalTarget
#print axioms evalNextQ
end PA194ADNumericStandard
