import PA194RegisterPermutation
set_option autoImplicit false
namespace PA194RegisterUpdate
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194RegisterPermutation

def logicalIndex (r : Fin 9) : Fin 11 := ⟨r.val, by have h := r.isLt; omega⟩
def physicalIndex (r : Fin 9) : Fin 11 := ⟨M6.Source.physicalRegister r, by have h := M6.Source.physicalRegister_lt r; omega⟩

theorem order_injective : Function.Injective inputOrder := by
  have h : ∀ i j : Fin 11, inputOrder i = inputOrder j → i = j := by decide
  exact h

theorem physicalIndex_ne_spare (r : Fin 9) : physicalIndex r ≠ 9 := by
  have h := M6.Source.physicalRegister_lt r
  intro eq
  have hc := congrArg Fin.val eq
  simp only [physicalIndex] at hc
  omega

theorem physicalIndex_ne_suffix (r : Fin 9) : physicalIndex r ≠ 10 := by
  have h := M6.Source.physicalRegister_lt r
  intro eq
  have hc := congrArg Fin.val eq
  simp only [physicalIndex] at hc
  omega

theorem update_commutes {M : Type} (e : Fin 11 → M) (r : Fin 9) (v : M) :
    physicalArgs (Function.update e (logicalIndex r) v) = Function.update (physicalArgs e) (physicalIndex r) v := by
  funext i
  by_cases hi : i = physicalIndex r
  · subst i
    simp [physicalArgs,logicalIndex,physicalIndex,inversePhysical]
  · have hne : inputOrder i ≠ logicalIndex r := by
      intro h
      have hh : inputOrder i = inputOrder (physicalIndex r) := by
        simpa only [physicalIndex,logicalIndex,inversePhysical] using h
      exact hi (order_injective hh)
    simp [physicalArgs,hi,hne]
def sourceView {M : Type} (e : Fin 11 → M) : Fin 9 → M := fun r => e (logicalIndex r)

theorem logicalIndex_injective : Function.Injective logicalIndex := by
  intro r s h
  apply Fin.ext
  simpa only [logicalIndex] using congrArg (fun x : Fin 11 => x.val) h

theorem sourceView_update {M : Type} (e : Fin 11 → M) (r : Fin 9) (v : M) :
    sourceView (Function.update e (logicalIndex r) v) =
      (fun s => if s = r then v else sourceView e s) := by
  funext s
  by_cases h : s = r
  · subst s
    simp [sourceView]
  · have hs : logicalIndex s ≠ logicalIndex r := fun he => h (logicalIndex_injective he)
    simp [sourceView,h,hs]

theorem actualSourceWrite (e : Fin 11 → Nat) (r : Fin 9) (v : Nat) :
    sourceView (Function.update e (logicalIndex r) v) = M6.Source.write (sourceView e) r v := by
  rw [sourceView_update]
  rfl
section models
open PRAFiniteFunctionCodes PRALanguage PRATheory PA194RegisterFile
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)

theorem modelSourceWrite (e : Fin 11 → M) (r : Fin 9) (v : M) :
    F sourceFileCode (Function.update e (logicalIndex r) v) =
      F (fileCode 10) (Function.update (physicalArgs e) (physicalIndex r) v) := by
  rw [modelSourceFile,update_commutes]
#print axioms modelSourceWrite
end models
#print axioms actualSourceWrite
#print axioms update_commutes
end PA194RegisterUpdate
