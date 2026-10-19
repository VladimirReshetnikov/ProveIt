import BusyBeaver.ZFC.TableRotation244

/-! Literal row facts required by the fresh Rotation244 runtime port.
The nineteen actions are checked against the exact table; this is no global
renaming or transport theorem for arbitrary machine executions.
-/
namespace SetTheory.BusyBeaver.ZFC

def dispatchRotation244 : Fin 244 := oldStateRotation244 96
theorem dispatchRotation244_eq : dispatchRotation244 = 87 := by decide +kernel

theorem rowRotation244_old109_false :
    machineRotation244.transition (oldStateRotation244 109) false =
      ⟨false, .right, some (oldStateRotation244 75)⟩ := by decide +kernel

theorem rowRotation244_old109_true :
    machineRotation244.transition (oldStateRotation244 109) true =
      ⟨false, .right, some (oldStateRotation244 95)⟩ := by decide +kernel

theorem rowRotation244_old112_false :
    machineRotation244.transition (oldStateRotation244 112) false =
      ⟨true, .left, some (oldStateRotation244 131)⟩ := by decide +kernel

theorem rowRotation244_old112_true :
    machineRotation244.transition (oldStateRotation244 112) true =
      ⟨true, .left, some (oldStateRotation244 112)⟩ := by decide +kernel

theorem rowRotation244_old131_false :
    machineRotation244.transition (oldStateRotation244 131) false =
      ⟨false, .left, some (oldStateRotation244 48)⟩ := by decide +kernel

theorem rowRotation244_old131_true :
    machineRotation244.transition (oldStateRotation244 131) true =
      ⟨false, .left, some (oldStateRotation244 112)⟩ := by decide +kernel

theorem rowRotation244_old255_false :
    machineRotation244.transition (oldStateRotation244 255) false =
      ⟨true, .left, some (oldStateRotation244 255)⟩ := by decide +kernel

theorem rowRotation244_old255_true :
    machineRotation244.transition (oldStateRotation244 255) true =
      ⟨true, .left, some (oldStateRotation244 131)⟩ := by decide +kernel

theorem rowRotation244_old48_true :
    machineRotation244.transition (oldStateRotation244 48) true =
      ⟨true, .left, some (oldStateRotation244 63)⟩ := by decide +kernel

theorem rowRotation244_old63_false :
    machineRotation244.transition (oldStateRotation244 63) false =
      ⟨false, .left, some (oldStateRotation244 48)⟩ := by decide +kernel

theorem rowRotation244_old63_true :
    machineRotation244.transition (oldStateRotation244 63) true =
      ⟨true, .left, some (oldStateRotation244 63)⟩ := by decide +kernel

theorem rowRotation244_old73_false :
    machineRotation244.transition (oldStateRotation244 73) false =
      ⟨false, .right, some (oldStateRotation244 83)⟩ := by decide +kernel

theorem rowRotation244_old73_true :
    machineRotation244.transition (oldStateRotation244 73) true =
      ⟨true, .right, some (oldStateRotation244 73)⟩ := by decide +kernel

theorem rowRotation244_old75_false :
    machineRotation244.transition (oldStateRotation244 75) false =
      ⟨true, .right, some (oldStateRotation244 255)⟩ := by decide +kernel

theorem rowRotation244_old75_true :
    machineRotation244.transition (oldStateRotation244 75) true =
      ⟨true, .left, some (oldStateRotation244 63)⟩ := by decide +kernel

theorem rowRotation244_old83_false :
    machineRotation244.transition (oldStateRotation244 83) false =
      ⟨true, .right, some (oldStateRotation244 95)⟩ := by decide +kernel

theorem rowRotation244_old83_true :
    machineRotation244.transition (oldStateRotation244 83) true =
      ⟨true, .right, some (oldStateRotation244 73)⟩ := by decide +kernel

theorem rowRotation244_old95_false :
    machineRotation244.transition (oldStateRotation244 95) false =
      ⟨true, .right, some (oldStateRotation244 109)⟩ := by decide +kernel

theorem rowRotation244_old95_true :
    machineRotation244.transition (oldStateRotation244 95) true =
      ⟨true, .right, some (oldStateRotation244 95)⟩ := by decide +kernel

end SetTheory.BusyBeaver.ZFC
