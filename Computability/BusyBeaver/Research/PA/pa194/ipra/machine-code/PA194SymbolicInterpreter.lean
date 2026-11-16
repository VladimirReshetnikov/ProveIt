import PA194SymbolicChecker
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace PA194SymbolicInterpreter
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194StateOne PA194FiniteControls TableDispatch PRAModelIOpenPairing PA194SymbolicTrace PA194SymbolicChecker
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)

theorem checkedRunCorrect (rows : List Row) (s t : Config) (h : checkRun s rows = some t) (leftTail rightTail : M) :
    F PA194Stepper.stepper ![modelNumeral M rows.length,encode s leftTail rightTail] = encode t leftTail rightTail :=
  runCorrect (runSound rows s t h) leftTail rightTail
#print axioms checkedRunCorrect
end models
end PA194SymbolicInterpreter
