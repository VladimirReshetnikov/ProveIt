import PA194SourceProgram
import PA194IteratedSimulation
import PackedDecoderModel
import DiophantineConsistency.PRAEqualityCode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194SourceControllerCode
open M6.Source M6.Source.PathTrie PA194.SourceTree
open DiophantineConsistency PRAFiniteFunctionCodes PRAHistoryPairCode PRASelectCode PRATheory
open PRAEqualityCode PackedClock TableDispatch

/-- A configuration is `pair pc file`; `file` is nine nested square pairs,
    with an arbitrary suffix after the ninth register. Ordinals 0..3672 are
    source sites, 3673 is malformed, and 3674 is the absorbing halted state. -/
def pc : Code 1 := decodeLeft
def file : Code 1 := decodeRight

def getRegisterAux : Nat → Code 1 → Code 1
  | 0, f => unary decodeLeft f
  | n+1, f => getRegisterAux n (unary decodeRight f)
def getRegister (n : Nat) : Code 1 := getRegisterAux n file

def putRegisterAux : Nat → Code 1 → Code 1 → Code 1
  | 0, f, value => bin pairCode value (unary decodeRight f)
  | n+1, f, value => bin pairCode (unary decodeLeft f) (putRegisterAux n (unary decodeRight f) value)

def setRegister (n : Nat) (value : Code 1) : Code 1 := putRegisterAux n file value

def state (dest : Nat) (newFile : Code 1) : Code 1 := bin pairCode (constantCode dest) newFile

def destination : Option Nat → Nat
  | none => 0
  | some i => i

def instruction : Option Instruction → Code 1
  | none => state 3673 file
  | some (.inc r next) => state (destination next) (setRegister r.val (unary Code.succ (getRegister r.val)))
  | some (.dec r zero positive) =>
      selectAmong (getRegister r.val)
        (state (destination positive) (setRegister r.val (unary predCode (getRegister r.val))))
        (state (destination zero) file)
  | some (.jump next) => state (destination next) file
  | some .halt => state 3674 file

def isOrdinal (n : Nat) : Code 1 := bin equalityCode pc (constantCode n)

def defaultStep : Code 1 :=
  selectAmong (isOrdinal 3673) (.proj 0)
    (selectAmong (isOrdinal 3674) (.proj 0) (state 3673 file))

def dispatch : Nat → List (Option Instruction) → Code 1
  | _, [] => defaultStep
  | n, i::is => selectAmong (isOrdinal n) (instruction i) (dispatch (n+1) is)

/-- Table entries come directly from the pinned tree and its checked resolver. -/
def program : List (Option Instruction) :=
  (List.range 3673).map (fun i => (nthSite trie i).bind (M6.FastResolve.resolveTree trie))

def step : Code 1 := dispatch 0 program
def run : Code 2 := PA194IteratedSimulation.iterate step

/-- No table evaluation is needed to see that the model-length iterator is a
    finite code with the existing iterator recurrence. -/
theorem stepIsFiniteCode : ∃ c : Code 1, c = step := ⟨step,rfl⟩
#print axioms stepIsFiniteCode
end PA194SourceControllerCode
