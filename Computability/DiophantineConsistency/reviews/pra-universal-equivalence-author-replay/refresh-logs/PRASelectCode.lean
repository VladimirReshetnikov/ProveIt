import DiophantineConsistency.PRACharacteristicBit

/-! Primitive-recursive selection with theory-verified defining equations. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASelectCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABooleanOps

/-- `selectCode b yes no` returns `no` at zero and `yes` at any successor. -/
def selectCode : Code 3 := .prec (.proj (1 : Fin 2)) (.proj (2 : Fin 4))

def selectAmong {n : ℕ} (test yes no : Code n) : Code n :=
  .comp selectCode (.cons test (.cons yes (.cons no (.nil n))))

def selectZeroSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode selectCode ![applyCode (Code.zero 0) Fin.elim0, .bvar 0, .bvar 1]) (.bvar 1)

def selectSuccSentence : Sentence language :=
  equalClosure (n := 3)
    (applyCode selectCode ![applyCode Code.succ (fun _ => .bvar 0), .bvar 1, .bvar 2]) (.bvar 1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSelectZero (a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0,a,b] = b := by
  have h := modelBase (M := M) (.proj (1 : Fin 2)) (.proj (2 : Fin 4)) ![a,b]
  rw [modelProjection] at h
  exact h

theorem modelSelectSucc (x a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) Code.succ (fun _ => x), a,b] = a := by
  have h := modelStep (M := M) (.proj (1 : Fin 2)) (.proj (2 : Fin 4)) ![x,a,b]
  rw [modelProjection] at h
  exact h

theorem modelSelectAmong {n : ℕ} (test yes no : Code n) (e : Fin n → M) :
    Structure.func (L := language) (selectAmong test yes no) e =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) test e, Structure.func (L := language) yes e,
          Structure.func (L := language) no e] := by
  rw [selectAmong, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun l => Fin.elim0 l) k

theorem modelSelectOne (a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) oneCode Fin.elim0,a,b] = a := by
  rw [modelOneSuccZero]
  exact modelSelectSucc _ _ _

theorem modelSelectZeroSentence : M↓[language] ⊧ selectZeroSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ ![applyCode (Code.zero 0) Fin.elim0, .bvar 0, .bvar 1]) =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, e 0,e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Structure.func (L := language) (Code.zero 0)
        (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 2)) = _
      rw [hz]
      rfl
    · refine Fin.cases rfl (fun k => ?_) j
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
  simp only [applyCode] at hv
  rw [hv]
  exact modelSelectZero (e 0) (e 1)

theorem modelSelectSuccSentence : M↓[language] ⊧ selectSuccSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hv : (Semiterm.val e Empty.elim ∘ ![applyCode Code.succ (fun _ => .bvar 0), .bvar 1, .bvar 2]) =
      ![Structure.func (L := language) Code.succ (fun _ => e 0), e 1,e 2] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun l => Fin.elim0 l) k
  simp only [applyCode] at hv
  rw [hv]
  exact modelSelectSucc (e 0) (e 1) (e 2)

end models

theorem PRA_proves_selectZero : PRA ⊢ selectZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSelectZeroSentence

theorem PRA_proves_selectSucc : PRA ⊢ selectSuccSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSelectSuccSentence
end DiophantineConsistency.PRASelectCode
