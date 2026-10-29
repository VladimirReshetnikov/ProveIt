import DiophantineConsistency.PRAOpenInduction
import DiophantineConsistency.PRAAddition

/-! Addition laws derived by open induction in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAdditionZeroLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAOpenInduction

def zeroLeftBody : Semiformula language ℕ 1 :=
  Semiformula.rel Language.ORing.Rel.eq
    ![.func addCode ![.func (.zero 0) Fin.elim0, .bvar 0], .bvar 0]

def zeroLeftSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode addCode ![applyCode (.zero 0) Fin.elim0, .bvar 0]) (.bvar 0)

theorem zeroLeftBody_open : zeroLeftBody.Open := by
  simp [zeroLeftBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem zeroLeftBody_eval (x : M) (e : ℕ → M) : zeroLeftBody.Eval ![x] e ↔
    Structure.func (L := language) addCode
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] = x := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![x] zeroLeftBody ↔ _
  dsimp only [zeroLeftBody, Semiformula.EvalAux]
  rw [eqRel]
  have hz : (Semiterm.val ![x] e ∘ (Fin.elim0 : Fin 0 → Semiterm language ℕ 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val ![x] e ∘ ![(.func (Code.zero 0) Fin.elim0 : Semiterm language ℕ 1), .bvar 0]) =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := by
    simpa only [Semiterm.val_func, Semiterm.val_bvar, Matrix.cons_val_zero, hz] using
      val_pair ![x] e (.func (Code.zero 0) Fin.elim0) (.bvar 0)
  change Structure.func (L := language) addCode
    (Semiterm.val ![x] e ∘ ![(.func (Code.zero 0) Fin.elim0 : Semiterm language ℕ 1), .bvar 0]) = x ↔ _
  rw [hv]

theorem modelZeroLeft (x : M) :
    Structure.func (L := language) addCode
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] = x := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let s : M → M := fun x => Structure.func (L := language) Code.succ (fun _ => x)
  let e : ℕ → M := fun _ => x
  apply (zeroLeftBody_eval x e).mp
  apply modelOpenInduction (M := M) zeroLeftBody zeroLeftBody_open e
  · apply (zeroLeftBody_eval z e).mpr
    exact modelAddZero z
  · intro y hy
    apply (zeroLeftBody_eval (s y) e).mpr
    change Structure.func (L := language) addCode ![z, s y] = s y
    rw [modelAddSucc, (zeroLeftBody_eval y e).mp hy]

theorem modelZeroLeftSentence : M↓[language] ⊧ zeroLeftSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ ![applyCode (.zero 0) Fin.elim0, .bvar 0]) =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, e 0] := by
    simpa only [applyCode, Semiterm.val_func, Semiterm.val_bvar, hz] using
      val_term_pair e (applyCode (.zero 0) Fin.elim0) (.bvar 0)
  simp only [applyCode] at hv
  rw [hv]
  exact modelZeroLeft (e 0)

end models

/-- A closed candidate-PRA derivation of left zero for addition. -/
theorem PRA_proves_zeroLeft : PRA ⊢ zeroLeftSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelZeroLeftSentence
end DiophantineConsistency.PRAAdditionZeroLeft
