import BusyBeaver.ZFC.TableRotation240

/-! Literal row facts required by the fresh Rotation240 runtime port.
The nineteen actions are checked against the exact table; this is no global
renaming or transport theorem for arbitrary machine executions.
-/
namespace SetTheory.BusyBeaver.ZFC

def dispatchRotation240 : Fin 240 := oldStateRotation240 96
theorem dispatchRotation240_eq : dispatchRotation240 = 84 := by decide +kernel

theorem rowRotation240_old109_false :
    machineRotation240.transition (oldStateRotation240 109) false =
      ⟨false, .right, some (oldStateRotation240 75)⟩ := by decide +kernel

theorem rowRotation240_old109_true :
    machineRotation240.transition (oldStateRotation240 109) true =
      ⟨false, .right, some (oldStateRotation240 95)⟩ := by decide +kernel

theorem rowRotation240_old112_false :
    machineRotation240.transition (oldStateRotation240 112) false =
      ⟨true, .left, some (oldStateRotation240 131)⟩ := by decide +kernel

theorem rowRotation240_old112_true :
    machineRotation240.transition (oldStateRotation240 112) true =
      ⟨true, .left, some (oldStateRotation240 112)⟩ := by decide +kernel

theorem rowRotation240_old131_false :
    machineRotation240.transition (oldStateRotation240 131) false =
      ⟨false, .left, some (oldStateRotation240 48)⟩ := by decide +kernel

theorem rowRotation240_old131_true :
    machineRotation240.transition (oldStateRotation240 131) true =
      ⟨false, .left, some (oldStateRotation240 112)⟩ := by decide +kernel

theorem rowRotation240_old255_false :
    machineRotation240.transition (oldStateRotation240 255) false =
      ⟨true, .left, some (oldStateRotation240 255)⟩ := by decide +kernel

theorem rowRotation240_old255_true :
    machineRotation240.transition (oldStateRotation240 255) true =
      ⟨true, .left, some (oldStateRotation240 131)⟩ := by decide +kernel

theorem rowRotation240_old48_true :
    machineRotation240.transition (oldStateRotation240 48) true =
      ⟨true, .left, some (oldStateRotation240 63)⟩ := by decide +kernel

theorem rowRotation240_old63_false :
    machineRotation240.transition (oldStateRotation240 63) false =
      ⟨false, .left, some (oldStateRotation240 48)⟩ := by decide +kernel

theorem rowRotation240_old63_true :
    machineRotation240.transition (oldStateRotation240 63) true =
      ⟨true, .left, some (oldStateRotation240 63)⟩ := by decide +kernel

theorem rowRotation240_old73_false :
    machineRotation240.transition (oldStateRotation240 73) false =
      ⟨false, .right, some (oldStateRotation240 83)⟩ := by decide +kernel

theorem rowRotation240_old73_true :
    machineRotation240.transition (oldStateRotation240 73) true =
      ⟨true, .right, some (oldStateRotation240 73)⟩ := by decide +kernel

theorem rowRotation240_old75_false :
    machineRotation240.transition (oldStateRotation240 75) false =
      ⟨true, .right, some (oldStateRotation240 255)⟩ := by decide +kernel

theorem rowRotation240_old75_true :
    machineRotation240.transition (oldStateRotation240 75) true =
      ⟨true, .left, some (oldStateRotation240 63)⟩ := by decide +kernel

theorem rowRotation240_old83_false :
    machineRotation240.transition (oldStateRotation240 83) false =
      ⟨true, .right, some (oldStateRotation240 95)⟩ := by decide +kernel

theorem rowRotation240_old83_true :
    machineRotation240.transition (oldStateRotation240 83) true =
      ⟨true, .right, some (oldStateRotation240 73)⟩ := by decide +kernel

theorem rowRotation240_old95_false :
    machineRotation240.transition (oldStateRotation240 95) false =
      ⟨true, .right, some (oldStateRotation240 109)⟩ := by decide +kernel

theorem rowRotation240_old95_true :
    machineRotation240.transition (oldStateRotation240 95) true =
      ⟨true, .right, some (oldStateRotation240 95)⟩ := by decide +kernel

end SetTheory.BusyBeaver.ZFC
