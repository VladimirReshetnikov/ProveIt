"""Bind all 61 delivered constructor occurrences for one radix."""

from hashlib import sha256
from pathlib import Path
import json
import sys

repo, out = map(Path, sys.argv[1:3])
coefficient = int(sys.argv[3]) if len(sys.argv) == 4 else 5
pins = {
    5: ("a75d3c991682ea4ee5a55243303d97764bc72ac71fb6e41a2aa2e4b0818f10d9",
        "34375509c46552ff7f5c84e24d265cdf56ecd97b41fad3da14787232aa601ca4"),
    6: ("cd20b1488a6bbb9f2c144771325aa162c3d313415e7621a348ca75b8a020a65e",
        "03afe51960fe2345637a0e3ea25987a8544612124ad728874cbc45ef1de9126d"),
}
packet = repo / "Computability/BusyBeaver/Research/PA/docs/pa194_radix_family_2026-11-13/machines" / str(coefficient)
binding = (packet / "source_binding.json").read_bytes()
source = (packet / "instructions.json").read_bytes()
binding_pin, source_pin = pins[coefficient]
assert sha256(binding).hexdigest() == binding_pin
assert sha256(source).hexdigest() == source_pin

data = json.loads(binding)
assert data["factor"] == coefficient
entries = sorted(body["cons_entry_new"] for body in data["bodies"])
assert len(entries) == len(set(entries)) == 61
span = 23 + coefficient
assert all(body["cons_exit_new"] - body["cons_entry_new"] == span for body in data["bodies"])
assert len(json.loads(source)) == 3673 + 61 * (coefficient - 4)

variant = f"PA194M{coefficient}"
module = f"{variant}ConsSites"
(out / f"{module}.lean").write_text(f"""import PA194ProgramConsCertificate
import {variant}Program

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace {module}
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramDrain PA194SchedulerFetchPositive PA194ProgramCons {variant}Program
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def entries : List Nat := [{", ".join(map(str, entries))}]
def site (index : Fin 61) : Nat := entries.getD index.val 0

theorem checked : ∀ index : Fin 61, CertifiedSlice program (site index) {coefficient} := by decide +kernel

theorem rows (index : Fin 61) : Rows program (site index) {coefficient} :=
  (checked index).certified.rows

section models
variable {{M : Type}} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem constructors (index : Fin 61) (args : Fin 11 → M) (tail left rest : M)
    (hx : args 6 = 0) (hy : args 7 = 0) (hstack : args 2 = cantor left rest) :
    ReachesPositive program (sourceState (site index) args tail)
      (sourceState (site index+{span}) (output {coefficient} args left rest) tail) :=
  execute program (site index) {coefficient} (rows index) args tail left rest hx hy hstack

#print axioms checked
#print axioms constructors
end models
end {module}
""")
