import ZF.Zf

/-! The exact power-set interface shared by semantic model constructions.
The declaration retains its original name and body from PSCCalibration. -/

namespace SetTheory.BusyBeaver.ZFC.PSCCalibration

universe u
variable {V : Type u}

def PowerSets (mem : V → V → Prop) : Prop :=
  ∀ a, ∃ p, ∀ y, mem y p ↔ SetTheory.Sub mem y a

end SetTheory.BusyBeaver.ZFC.PSCCalibration
