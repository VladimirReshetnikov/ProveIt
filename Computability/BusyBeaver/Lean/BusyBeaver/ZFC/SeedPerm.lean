import BusyBeaver.ZFC.L2RootPerm

/-!
The seed start of the 215's enumerator, and the program layer from its boot registers.

The 215 boots into the root with `nextproof = 4` and every other register zero: a state between
candidates whose registers hold derivable codes, so `EnumPerm.halts_iff` applies.

`dagPerm_seed_iff`: the structured program `dagPerm`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

open SetTheory.BusyBeaver.ZFC.KCode222

/-- The 215's seed: candidate 4, every other register zero. -/
def seed : St := ⟨0, 4, 0, 0, 0, 0⟩

theorem seed_iff : HaltsFrom seed ↔ C222 Code254.F :=
  halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩

end SetTheory.BusyBeaver.ZFC.EnumPerm

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm
open Code254 (F)
open L2K (enc)

/-- The 215's boot registers: `nextproof = 4`. -/
def bootRegs : Regs := upd (fun _ => 0) 0 4

theorem enc_seed : enc (toAS EnumPerm.seed) = bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumPerm.seed, bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dagPerm` halts iff the code 1 is derivable. -/
theorem dagPerm_seed_iff : IterHalts dagPerm bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumPerm.seed_iff

#print axioms dagPerm_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Perm
