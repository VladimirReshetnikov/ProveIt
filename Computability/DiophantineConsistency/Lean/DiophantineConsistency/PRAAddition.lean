import DiophantineConsistency.PRAAddOne

/-! The addition zero and successor equations in the candidate PRA theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAddition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

def addZeroSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode addCode ![.bvar 0, applyCode (.zero 0) Fin.elim0]) (.bvar 0)

def addSuccSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode addCode ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)])
    (applyCode Code.succ (fun _ => applyCode addCode ![.bvar 0, .bvar 1]))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelAddExpand (x y : M) :
    Structure.func (L := language) addCode ![x,y] =
      Structure.func (L := language) addCore ![y,x] :=
  modelSwapComposition addCore x y

theorem modelAddZero (x : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) (Code.zero 0) Fin.elim0] = x := by
  rw [modelAddExpand]
  have h := modelBase (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![x]
  rw [modelProjection] at h
  have hv : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) ![x] =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := rfl
  rw [hv] at h
  exact h

theorem modelAddSucc (x y : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) Code.succ (fun _ => y)] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![x,y]) := by
  rw [modelAddExpand, modelAddExpand]
  have hs := modelStep (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![y,x]
  have hg := modelComposition (M := M) Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))
    ![y, Structure.func (L := language) addCore ![y,x], x]
  have hgArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.proj (1 : Fin 3)) (.nil 3)) i)
      ![y, Structure.func (L := language) addCore ![y,x], x]) =
      fun _ => Structure.func (L := language) addCore ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelProjection (M := M) 1 _
  rw [hgArg] at hg
  change Structure.func (L := language) addCore
      ![Structure.func (L := language) Code.succ (fun _ => y), x] =
    Structure.func (L := language) (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3)))
      ![y, Structure.func (L := language) addCore ![y,x], x] at hs
  exact hs.trans hg


theorem modelAddZeroSentence : M↓[language] ⊧ addZeroSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode (.zero 0) Fin.elim0]) =
      ![e 0, Structure.func (L := language) (Code.zero 0) Fin.elim0] := by
    have hz' : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 1)) =
        (Fin.elim0 : Fin 0 → M) := hz
    simpa [applyCode, Function.comp_def, hz'] using
      val_term_pair e (.bvar 0) (applyCode (.zero 0) Fin.elim0)
  simp only [applyCode] at hv
  rw [hv]
  exact modelAddZero (e 0)

theorem modelAddSuccSentence : M↓[language] ⊧ addSuccSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hpair : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    simpa only [Semiterm.val_bvar] using val_term_pair e (.bvar 0) (.bvar 1)
  have hleft : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)]) =
      ![e 0, Structure.func (L := language) Code.succ (fun _ => e 1)] := by
    simpa [applyCode, Function.comp_def] using
      val_term_pair e (.bvar 0) (applyCode Code.succ (fun _ => .bvar 1))
  have hright : (Semiterm.val e Empty.elim ∘ fun _ : Fin 1 => applyCode addCode ![.bvar 0, .bvar 1]) =
      fun _ => Structure.func (L := language) addCode ![e 0, e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) addCode
      (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = _
    rw [hpair]
  simp only [applyCode] at hleft hright
  rw [hleft, hright]
  exact modelAddSucc (e 0) (e 1)

end models

/-- The candidate PRA derives the zero clause of addition. -/
theorem PRA_proves_addZero : PRA ⊢ addZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelAddZeroSentence

/-- The candidate PRA derives the successor clause of addition. -/
theorem PRA_proves_addSucc : PRA ⊢ addSuccSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelAddSuccSentence

end DiophantineConsistency.PRAAddition
