import BusyBeaver.ZFC.ModelBridge254

namespace SetTheory.BusyBeaver.ZFC.ModelBridge254Checks

open Code254Models ModelBridge254

universe u

-- Keep the enormous recursively paired bundle constants symbolic in callers.
attribute [local irreducible] Code254.dec Code254.bundle

/-- Truth code zero together with the gate-allowed collision a=b. -/
theorem zero_equal_labels {V : Type u} (mem : V → V → Prop)
    (hirr : ∀ x, ¬ mem x x) (h : ModelsEncodable mem) (env : Nat → V) :
    Tarski.Sat mem env (Code254.dec (Code254.bundle 1 1 0)) :=
  decoded_of_encodable mem hirr h 1 1 0 (by decide) (by decide) env

/-- Native equality Eq(1,2) has code35. Both original gates are retained. -/
theorem native_point {V : Type u} (mem : V → V → Prop)
    (hirr : ∀ x, ¬ mem x x) (h : ModelsEncodable mem) (env : Nat → V) :
    Tarski.Sat mem env (Code254.dec (Code254.bundle 0 1 35)) :=
  decoded_of_encodable mem hirr h 0 1 35 (by decide) (by decide) env

/-- The equivalence theorem needs no hidden inhabitant, even for Empty. -/
theorem empty_equivalence (mem : Empty → Empty → Prop) :
    ModelsDecoded mem ↔ ModelsEncodable mem :=
  modelsDecoded_iff_modelsEncodable mem (fun x => Empty.elim x)

end SetTheory.BusyBeaver.ZFC.ModelBridge254Checks

#print axioms SetTheory.BusyBeaver.ZFC.ModelBridge254Checks.zero_equal_labels
#print axioms SetTheory.BusyBeaver.ZFC.ModelBridge254Checks.native_point
#print axioms SetTheory.BusyBeaver.ZFC.ModelBridge254Checks.empty_equivalence
