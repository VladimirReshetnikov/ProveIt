import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.Seed222

/-!
The seed start of the 217's enumerator, and the program layer from the boot registers.

The K-family machines boot into Elliot Glazer's seed state (candidate 3, parameter counter 3:
registers `np = 3`, `param1 = 3`, the boot registers `L2K.bootRegs`), a state between candidates
whose registers hold derivable codes, so `EnumDom.halts_iff` applies.

`dagDom_seed_iff`: the structured program `dagDom`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumDom

open SetTheory.BusyBeaver.ZFC.KCode222

/-- Elliot Glazer's seed: candidate 3, parameter counter 3. -/
def seed : St := ⟨0, 3, 0, 0, 3, 0⟩

theorem seed_iff : HaltsFrom seed ↔ C222 Code254.F :=
  halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩

end SetTheory.BusyBeaver.ZFC.EnumDom

namespace SetTheory.BusyBeaver.ZFC.L2Dom

open RMDag DagDom
open Code254 (F)
open L2K (enc bootRegs)

theorem enc_seed : enc (toAS EnumDom.seed) = bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumDom.seed, bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dagDom` halts iff the code 1 is derivable. -/
theorem dagDom_seed_iff : IterHalts dagDom bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumDom.seed_iff

#print axioms dagDom_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Dom
