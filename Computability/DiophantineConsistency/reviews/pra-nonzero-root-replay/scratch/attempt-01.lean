import DiophantineConsistency.PRAMultiplication

/-! Candidate PRA derivations of the represented nonzero-bit recursion. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRANonzero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAMultiplication

def nonzeroZeroSentence : Sentence language :=
  equalClosure (n := 0)
    (applyCode nonzeroCode (fun _ => applyCode (.zero 0) Fin.elim0))
    (applyCode (.zero 0) Fin.elim0)

def nonzeroSuccSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode nonzeroCode (fun _ => applyCode Code.succ (fun _ => .bvar 0)))
    (applyCode oneCode Fin.elim0)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelNonzeroZero :
    Structure.func (L := language) nonzeroCode
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0)
    (Code.comp Code.succ (.cons (.zero 2) (.nil 2))) (Fin.elim0 : Fin 0 → M)
  simpa [nonzeroCode, Matrix.fun_eq_vec_one] using h

theorem modelNonzeroSucc (x : M) :
    Structure.func (L := language) nonzeroCode
      (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) =
      Structure.func (L := language) oneCode Fin.elim0 := by
  have hs := modelStep (M := M) (Code.zero 0)
    (Code.comp Code.succ (.cons (.zero 2) (.nil 2))) ![x]
  have hg := modelComposition (M := M) Code.succ (.cons (.zero 2) (.nil 2))
    ![x, Structure.func (L := language) nonzeroCode ![x]]
  have ho := modelComposition (M := M) Code.succ (.cons (.zero 0) (.nil 0))
    (Fin.elim0 : Fin 0 → M)
  have hgArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.zero 2) (.nil 2)) i)
      ![x, Structure.func (L := language) nonzeroCode ![x]]) =
      fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelZero _
  have hoArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.zero 0) (.nil 0)) i) (Fin.elim0 : Fin 0 → M)) =
      fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [hgArg] at hg
  rw [hoArg] at ho
  change Structure.func (L := language) nonzeroCode
      (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) =
    Structure.func (L := language) (Code.comp Code.succ (.cons (.zero 2) (.nil 2)))
      ![x, Structure.func (L := language) nonzeroCode ![x]] at hs
  change Structure.func (L := language) oneCode Fin.elim0 = _ at ho
  exact hs.trans (hg.trans ho.symm)

end models
end DiophantineConsistency.PRANonzero
