import BusyBeaver.ZFC.ModelBridge254
import BusyBeaver.ZFC.Enum254

/-!
The existing abstract six-register enumerator now has the same exact
native-equality CP/GIC model characterization in both directions.
This is not an execution theorem for Prog254 or a binary Turing machine.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumModelBridge254

open Code254Models ModelBridge254

theorem enum_halts_iff_no_decoded_model :
    Enum254.Halts ↔
      ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
        ModelsDecoded mem → (Nat → D) → False := by
  exact Enum254.enum_halts_iff.trans refutation_iff_no_decoded_model

theorem enum_halts_iff_no_native_model :
    Enum254.Halts ↔
      ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
        ModelsNativeCPGIC mem → (Nat → D) → False := by
  exact Enum254.enum_halts_iff.trans refutation_iff_no_native_model

end SetTheory.BusyBeaver.ZFC.EnumModelBridge254

#print axioms SetTheory.BusyBeaver.ZFC.EnumModelBridge254.enum_halts_iff_no_decoded_model
#print axioms SetTheory.BusyBeaver.ZFC.EnumModelBridge254.enum_halts_iff_no_native_model
