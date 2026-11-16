"""Emit the pinned M5/M6 source lists and their first coefficient-dependent loop."""

from hashlib import sha256
import json
from pathlib import Path
import sys


repo, out = map(Path, sys.argv[1:3])
packet = repo / "Computability/BusyBeaver/Research/PA/docs/pa194_radix_family_2026-11-13"
source_pins = {
    5: "34375509c46552ff7f5c84e24d265cdf56ecd97b41fad3da14787232aa601ca4",
    6: "03afe51960fe2345637a0e3ea25987a8544612124ad728874cbc45ef1de9126d",
}
for coefficient in map(int, sys.argv[3:]):
    rows_path = packet / f"machines/{coefficient}/instructions.json"
    raw = rows_path.read_bytes()
    assert sha256(raw).hexdigest() == source_pins[coefficient]
    rows = json.loads(raw)
    count = 3673 + 61 * (coefficient - 4)
    assert len(rows) == count
    assert rows.count(["halt"]) == 1
    first, test, end = 124, 123, 125 + coefficient
    assert rows[test] == ["dec", 7, end, first]
    assert rows[first:first + coefficient] == [["inc", 1, q + 1] for q in range(first, first + coefficient)]
    assert rows[first + coefficient] == ["jump", test]

    constructors = []
    for operation, *values in rows:
        if operation == "dec":
            register, zero, positive = values
            row = f".dec {register} (some {zero}) (some {positive})"
        elif operation == "inc":
            register, next_control = values
            row = f".inc {register} (some {next_control})"
        elif operation == "jump":
            row = f".jump (some {values[0]})"
        else:
            assert operation == "halt" and not values
            row = ".halt"
        constructors.append(f"some ({row})")
    lines = ",\n".join("  " + ", ".join(constructors[i:i + 5]) for i in range(0, len(rows), 5))

    program = f"PA194M{coefficient}Program"
    (out / f"{program}.lean").write_text(f"""import PA194ProgramDrain
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {program}
open PA194ProgramDrain
/-- The source instruction list pinned by SHA-256 {source_pins[coefficient]}. -/
def program : Program := [
{lines}
]

theorem programLength : program.length = {count} := by decide +kernel

end {program}
""")

    loop = f"PA194M{coefficient}Constructor"
    trace = f"(.jump {first+coefficient} (by decide +kernel) (by decide +kernel))"
    for control in range(first + coefficient - 1, first - 1, -1):
        trace = f"(.inc {control} {control+1} 1 _ (by decide +kernel) (by decide +kernel)\n    {trace})"

    (out / f"{loop}.lean").write_text(f"""import {program}
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace {loop}
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramDrain PA194SchedulerFetchPositive
open {program}

theorem loopRows : Increments program {test} {first} (List.replicate {coefficient} (1 : Fin 9)) :=
    {trace}

section models
variable {{M : Type}} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem firstMultiply (args : Fin 11 → M) (tail : M) :
    ReachesPositive program (sourceState {test} args tail)
      (sourceState {end}
        (Function.update (Function.update args 1 (args 1+modelNumeral M {coefficient} * args 7)) 7 0)
        tail) :=
  multiply program {test} {first} {end} {coefficient} (by decide +kernel) (by decide +kernel)
    loopRows args tail

#print axioms loopRows
#print axioms firstMultiply
end models
end {loop}
""")
