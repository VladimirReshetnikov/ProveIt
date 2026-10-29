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
    (Structure.func (L := language) nonzeroCode
      (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) : M) =
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
  have hvL : Fin.cases (Structure.func (L := language) Code.succ (fun _ => (![x] : Fin 1 → M) 0))
      (fun i => (![x] : Fin 1 → M) i.succ) =
      (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  have hvR : Fin.cases ((![x] : Fin 1 → M) 0)
      (Fin.cases (Structure.func (L := language) nonzeroCode ![x]) (fun i => (![x] : Fin 1 → M) i.succ)) =
      ![x, Structure.func (L := language) nonzeroCode ![x]] := rfl
  change Structure.func (L := language) nonzeroCode _ =
    Structure.func (L := language) (Code.comp Code.succ (.cons (.zero 2) (.nil 2)))
      (Fin.cases ((![x] : Fin 1 → M) 0)
        (Fin.cases (Structure.func (L := language) nonzeroCode ![x])
          (fun i => (![x] : Fin 1 → M) i.succ))) at hs
  rw [hvL, hvR] at hs
  change Structure.func (L := language) oneCode Fin.elim0 = _ at ho
  exact hs.trans (hg.trans ho.symm)


theorem modelNonzeroZeroSentence : M↓[language] ⊧ nonzeroZeroSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have ha : (Semiterm.val e Empty.elim ∘ fun _ : Fin 1 =>
      applyCode (.zero 0) Fin.elim0) =
      fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) (Code.zero 0)
      (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 0)) = _
    rw [hz]
  simp only [applyCode] at ha
  rw [ha, hz]
  exact modelNonzeroZero

theorem modelNonzeroSuccSentence : M↓[language] ⊧ nonzeroSuccSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have ha : (Semiterm.val e Empty.elim ∘ fun _ : Fin 1 =>
      applyCode Code.succ (fun _ => .bvar 0)) =
      fun _ => Structure.func (L := language) Code.succ (fun _ => e 0) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    rfl
  simp only [applyCode] at ha
  rw [ha, hz]
  exact modelNonzeroSucc (e 0)

end models

/-- Candidate PRA proves nonzero(0)=0. -/
theorem PRA_proves_nonzeroZero : PRA ⊢ nonzeroZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelNonzeroZeroSentence

/-- Candidate PRA proves nonzero(succ(x))=1. -/
theorem PRA_proves_nonzeroSucc : PRA ⊢ nonzeroSuccSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelNonzeroSuccSentence
end DiophantineConsistency.PRANonzero
