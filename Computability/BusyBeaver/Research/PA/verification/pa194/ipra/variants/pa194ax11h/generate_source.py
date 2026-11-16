import hashlib,json,sys
from pathlib import Path
repo=Path(sys.argv[1]); out=Path(sys.argv[2]); source=repo/'Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/machines/PA194AX11H/instructions.json'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='43a4ba0d62f95fe766d5369940b0aa8b7a4da04824feb8836905e289640f59f7'
rows=json.loads(source.read_text());assert len(rows)==3671
def fmt(i):
 if i[0]=='inc':return f'some (.inc {i[1]} (some {i[2]}))'
 if i[0]=='dec':return f'some (.dec {i[1]} (some {i[2]}) (some {i[3]}))'
 if i[0]=='jump':return f'some (.jump (some {i[1]}))'
 if i==['halt']:return 'some .halt'
 raise ValueError(i)
def lst(a): return '[\n'+',\n'.join('  '+fmt(x) for x in a)+'\n]'
prefix,suffix=rows[:3553],rows[3572:]
s='''import PA194AX11HPushRows
import PA194SourceControllerBinding
import PA194SourceInstructionModel
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
noncomputable section
namespace PA194AX11HSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourceControllerBinding PA194SourceInstructionModel
open PA194AX11HPushRows

def beforePush : List (Option M6.Source.Instruction) := '''+lst(prefix)+'''
def suffix : List (Option M6.Source.Instruction) := '''+lst(suffix)+'''

def program : List (Option M6.Source.Instruction) := beforePush ++ newPush.map some ++ suffix

/-- This source code uses the primary malformed/halted sentinels 3673/3674;
    only its behavior at the 3,671 valid revised sites is claimed here. -/
def step : Code 1 := dispatch 0 program

theorem beforePush_length : beforePush.length = 3553 := by decide +kernel
theorem suffix_length : suffix.length = 99 := by decide +kernel
theorem push_length : newPush.length = 19 := by decide +kernel
theorem program_length : program.length = 3671 := by
  simp [program,beforePush_length,suffix_length,push_length]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem selected (i : Nat) (hi : i < 3671) (s : M)
    (hp : F pc ![s] = modelNumeral M i) :
    F step ![s] = instructionSem (program[i]'(by simpa [program_length] using hi)) s := by
  have h := dispatchAt 0 program i (by simpa [program_length] using hi) s (by simpa using hp)
  rw [step,h,instructionModel]

#print axioms program_length
#print axioms selected
end models
end PA194AX11HSource
'''
out.mkdir(parents=True,exist_ok=True);(out/'PA194AX11HSource.lean').write_text(s)
