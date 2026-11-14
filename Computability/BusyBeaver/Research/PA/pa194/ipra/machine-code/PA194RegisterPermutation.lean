import PA194RegisterFile
import M6.Source.PhysicalRegisters
import DiophantineConsistency.PRATermCompilation
set_option autoImplicit false
namespace PA194RegisterPermutation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PA194RegisterFile

/-- Physical slots 0..8 in terms of logical register slots, followed by the
physical spare and the numeric tape suffix. -/
def inputOrder : Fin 11 → Fin 11 := ![2,8,1,4,3,7,0,5,6,9,10]
def sourceFileCode : Code 11 := .comp (fileCode 10) (pack 11 (fun i => .proj (inputOrder i)))

theorem inversePhysical (r : Fin 9) :
    inputOrder ⟨M6.Source.physicalRegister r, by have h := M6.Source.physicalRegister_lt r; omega⟩ =
      ⟨r.val, by have h := r.isLt; omega⟩ := by
  have h : ∀ r : Fin 9,
      inputOrder ⟨M6.Source.physicalRegister r, by have h := M6.Source.physicalRegister_lt r; omega⟩ =
        ⟨r.val, by have h := r.isLt; omega⟩ := by decide
  exact h r

theorem spare : inputOrder 9 = 9 := rfl
theorem suffix : inputOrder 10 = 10 := rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
def physicalArgs (e : Fin 11 → M) : Fin 11 → M := fun i => e (inputOrder i)

theorem modelSourceFile (e : Fin 11 → M) :
    F sourceFileCode e = F (fileCode 10) (physicalArgs e) := by
  rw [sourceFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact modelProjection (inputOrder i) e

omit [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem sourceRegisterAt (e : Fin 11 → M) (r : Fin 9) :
    physicalArgs e ⟨M6.Source.physicalRegister r, by have h := M6.Source.physicalRegister_lt r; omega⟩ =
      e ⟨r.val, by have h := r.isLt; omega⟩ := by
  simp only [physicalArgs,inversePhysical]

omit [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem sourceSpareAt (e : Fin 11 → M) : physicalArgs e 9 = e 9 := rfl
omit [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem sourceSuffixAt (e : Fin 11 → M) : physicalArgs e 10 = e 10 := rfl
#print axioms modelSourceFile
#print axioms sourceRegisterAt
end models
#print axioms inversePhysical
end PA194RegisterPermutation
