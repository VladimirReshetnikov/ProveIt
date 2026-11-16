import IPRABridge.ScopedSequents

/-! Check reflection for a native order formula whose term contains a
positive-arity zero symbol. -/

set_option autoImplicit false

namespace IPRABridge.Checks

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder
open DiophantineConsistency
open IPRAStandardTheory (standardTheory)
open IPRATheoryHilbertBridge (extended)
open PRAFiniteFunctionCodes (Code)

local notation "L" => PRALanguage.language

local instance scopedNativeDecidableEq : PRALanguage.language.DecidableEq where
  func k := by
    change DecidableEq (Code k)
    infer_instance
  rel k := by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

private def parameter : Fin 1 ↪ ℕ :=
  ⟨fun _ => 13, fun _ _ _ => Subsingleton.elim _ _⟩

private def orderWithUnaryZero : Semisentenceᵢ L 1 :=
  .rel Language.ORing.Rel.lt ![.func (.zero 1) (fun _ => .bvar 0), .bvar 0]

private def orderWithNullaryZero : Semisentenceᵢ L 1 :=
  .rel Language.ORing.Rel.lt ![.func (.zero 0) Fin.elim0, .bvar 0]

/-- The conclusion and both assumptions use the original native order
syntax, with a free parameter at label 13. -/
theorem reflectNativeOrderSequent :
    [(orderWithUnaryZero 🡒 orderWithNullaryZero), orderWithUnaryZero].map (atLabels parameter)
      ⊢[extended standardTheory] atLabels parameter orderWithNullaryZero :=
  (scopedStandardSequent_iff parameter _ _).2 (.impE Prf.hyp0 Prf.hyp1)

#print axioms reflectNativeOrderSequent

end IPRABridge.Checks
