import BusyBeaver.ZFC.L2Root219
import BusyBeaver.ZFC.Seed222

/-!
The program layer of the 219 from the boot registers.

The enumerator and its seed start are independent of the structured program (`Enum222.seed_iff`
from `Seed222`); `L2Q.iter_iff` relates them to `dag219`, so `dag219`, iterated from the boot
registers (`nextproof = 3`, `param1 = 3`), halts iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Q

open RMDag Dag219 Code254

theorem enc_seed : enc (toAS Enum222.seed) = L2K.bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp [enc, toAS, Enum222.seed, L2K.bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dag219` halts iff the code 1 is derivable. -/
theorem dag219_seed_iff : IterHalts dag219 L2K.bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact Enum222.seed_iff

#print axioms dag219_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Q
