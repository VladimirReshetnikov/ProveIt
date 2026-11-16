import PA194ADNumericTape
import PA194ADNumericStandard
import ConfigurationStandard
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace PA194ADPackedStandard
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes TableDispatch ConfigurationStep PackedClock PackedStandard List.Vector

theorem evalStep (q l r : Nat) :
    (eval PA194ADNext.nextQ (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval ConfigurationStep.nextL (q ::ᵥ l ::ᵥ r ::ᵥ nil),
     eval ConfigurationStep.nextR (q ::ᵥ l ::ᵥ r ::ᵥ nil)) =
    PA194ADTable.next PA194ADTable.adRows (q,l,r) := by
  have ht := congrArg Prod.snd (ConfigurationStandard.evalStepBounded q l r)
  rw [← PA194ADNumericTape.next_tape_eq] at ht
  exact Prod.ext (PA194ADNumericStandard.evalNextQ q l r) ht

theorem evalPackedStep (n : Nat) : eval PA194ADClock.encodedStep (n ::ᵥ nil) =
    pack (PA194ADTable.next PA194ADTable.adRows (unpack n)) := by
  simp only [PA194ADClock.encodedStep, evalBin, evalPair, evalInject, PackedStandard.pack, unpack]
  rw [← evalStep]

theorem evalClock (n : Nat) : eval PA194ADClock.clock (n ::ᵥ nil) =
    pack (PA194ADTable.run PA194ADTable.adRows (0,0,0) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change eval PA194ADClock.encodedStep (eval PA194ADClock.clock (n ::ᵥ nil) ::ᵥ nil) = _
    rw [ih, evalPackedStep, unpackPack]
    rfl

#print axioms evalStep
#print axioms evalPackedStep
#print axioms evalClock
end PA194ADPackedStandard
