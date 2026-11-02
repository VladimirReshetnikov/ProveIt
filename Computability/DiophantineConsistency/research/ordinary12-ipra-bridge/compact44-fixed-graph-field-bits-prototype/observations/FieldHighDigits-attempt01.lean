import DiophantineConsistency.FieldExactZero
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace FieldHighDigits
open CompactHighPopulation

theorem vertical (u : ℕ) (hu : u<9) : highDigits.getD (1013+u) 0=1 := by
  interval_cases u <;> decide +kernel

theorem horizontal (u : ℕ) (hu : u<8) : highDigits.getD (1065+u) 0=1 := by
  interval_cases u <;> decide +kernel
#print axioms FieldHighDigits.vertical
#print axioms FieldHighDigits.horizontal
end FieldHighDigits
