"""Bind the source-site list for all 61 delivered M5 constructor occurrences."""

from hashlib import sha256
from pathlib import Path
import json
import sys

repo, out = map(Path, sys.argv[1:])
packet = repo / "Computability/BusyBeaver/Research/PA/docs/pa194_radix_family_2026-11-13/machines/5"
binding = (packet / "source_binding.json").read_bytes()
source = (packet / "instructions.json").read_bytes()
assert sha256(binding).hexdigest() == "a75d3c991682ea4ee5a55243303d97764bc72ac71fb6e41a2aa2e4b0818f10d9"
assert sha256(source).hexdigest() == "34375509c46552ff7f5c84e24d265cdf56ecd97b41fad3da14787232aa601ca4"

data = json.loads(binding)
assert data["factor"] == 5
entries = sorted(body["cons_entry_new"] for body in data["bodies"])
assert len(entries) == len(set(entries)) == 61
assert all(body["cons_exit_new"] - body["cons_entry_new"] == 28 for body in data["bodies"])
assert len(json.loads(source)) == 3734

(out / "PA194M5ConsSites.lean").write_text(f"""import PA194ProgramConsCertificate
import PA194M5Program

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PA194M5ConsSites
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194ProgramDrain PA194SchedulerFetchPositive PA194ProgramCons PA194M5Program
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def entries : List Nat := [{", ".join(map(str, entries))}]
def site (index : Fin 61) : Nat := entries.getD index.val 0

theorem checked : ∀ index : Fin 61, CertifiedSlice program (site index) 5 := by decide +kernel

theorem rows (index : Fin 61) : Rows program (site index) 5 :=
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
      (sourceState (site index+28) (output 5 args left rest) tail) :=
  execute program (site index) 5 (rows index) args tail left rest hx hy hstack

#print axioms checked
#print axioms constructors
end models
end PA194M5ConsSites
""")
