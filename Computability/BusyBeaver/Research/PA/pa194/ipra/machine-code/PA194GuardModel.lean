import DiophantineConsistency.PRAIsZero
set_option autoImplicit false
namespace PA194GuardModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory
open PRAIsZero PRAExhaustion PRAMultiplication
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
theorem guardEqual (x a b : M)
    (h : x = F (Code.zero 0) Fin.elim0 → a = b) :
    F mulCode ![a,F isZeroCode (fun _ => x)] =
      F mulCode ![b,F isZeroCode (fun _ => x)] := by
  rcases modelZeroOrSuccPred x with hx | hs
  · rw [h hx]
  · have hz : F isZeroCode (fun _ => x) = F (Code.zero 0) Fin.elim0 := by
      rw [←hs]
      exact modelIsZeroSucc _
    rw [hz,modelMulZero,modelMulZero]
#print axioms guardEqual
end models
end PA194GuardModel
