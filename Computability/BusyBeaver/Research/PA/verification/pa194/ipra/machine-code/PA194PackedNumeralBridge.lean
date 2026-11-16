import PA194StandardStepperBridge
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194PackedNumeralBridge
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHistoryPairCode
open TableDispatch PackedStandard PA194StandardCodeBridge PA194StandardStepperBridge

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

theorem modelNumeralPair (a b : Nat) :
    modelNumeral M (Nat.pair a b) = F pairCode ![modelNumeral M a,modelNumeral M b] := by
  have h := (modelStandardCode (M := M) pairCode) (![a,b] : Fin 2 → Nat)
  have hv : (fun i => modelNumeral M ((![a,b] : Fin 2 → Nat) i)) =
      ![modelNumeral M a,modelNumeral M b] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [hv] at h
  have hn : F pairCode ![a,b] = Nat.pair a b := by
    change PRAFiniteFunctionCodes.eval pairCode (List.Vector.ofFn (![a,b] : Fin 2 → Nat)) = _
    rw [PRALanguage.ofFn_two, evalPair]
    rfl
  rw [hn] at h
  exact h.symm

theorem modelNumeralPack (q l r : Nat) :
    modelNumeral M (pack (q,l,r)) =
      F pairCode ![modelNumeral M q,F pairCode ![modelNumeral M l,modelNumeral M r]] := by
  change modelNumeral M (Nat.pair q (Nat.pair l r)) = _
  rw [modelNumeralPair,modelNumeralPair]

/-- A fixed successful literal blank run, expressed as explicit model tape
halves at its endpoint. No model-length simulation is asserted. -/
theorem literalBlankRun_explicitEndpoint (n : Nat) (finish : M6.Zip.Conf)
    (h : M6.Zip.run PA194.Literal.machine n PA194Bounded.blankZip = some finish) :
    F PA194Stepper.stepper ![modelNumeral M n,modelNumeral M 0] =
      F pairCode ![modelNumeral M finish.q,
        F pairCode ![modelNumeral M (PA194Bounded.bits finish.l),
          modelNumeral M (PA194Bounded.bits finish.r)]] := by
  have hrun := literalBlankRun_allModels (M := M) n finish h
  change F PA194Stepper.stepper ![modelNumeral M n,modelNumeral M 0] =
    modelNumeral M (pack (finish.q,PA194Bounded.bits finish.l,PA194Bounded.bits finish.r)) at hrun
  rw [modelNumeralPack] at hrun
  exact hrun
#print axioms modelNumeralPair
#print axioms modelNumeralPack
#print axioms literalBlankRun_explicitEndpoint
end models
end PA194PackedNumeralBridge
