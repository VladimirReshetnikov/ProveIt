import DiophantineConsistency.PRAAddOne

/-! Multiplication's primitive-recursion equations in the candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAMultiplication
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

def mulZeroSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode mulCode ![.bvar 0, applyCode (.zero 0) Fin.elim0])
    (applyCode (.zero 0) Fin.elim0)

def mulSuccSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode mulCode ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)])
    (applyCode addCode ![applyCode mulCode ![.bvar 0, .bvar 1], .bvar 0])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]


theorem modelZero {n : ℕ} (v : Fin n → M) :
    Structure.func (L := language) (Code.zero n) v =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelDefiningEquation (M := M) (DefiningEquation.zero n)
  simp only [models_iff, zeroEquation, equalClosure, Semiformula.eval_allClosure,
    Semiformula.eval_rel] at h
  have h' := (eqRel _).mp (h v)
  have hz : (fun i : Fin 0 => Semiterm.val v Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simpa [applyCode, vars, Function.comp_def, hz] using h'

theorem modelMulExpand (x y : M) :
    Structure.func (L := language) mulCode ![x,y] =
      Structure.func (L := language) mulCore ![y,x] :=
  modelSwapComposition mulCore x y

theorem modelMulZero (x : M) :
    Structure.func (L := language) mulCode
      ![x, Structure.func (L := language) (Code.zero 0) Fin.elim0] =
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  rw [modelMulExpand]
  have h := modelBase (M := M) (Code.zero 1)
    (Code.comp addCode (.cons (.proj (1 : Fin 3)) (.cons (.proj (2 : Fin 3)) (.nil 3)))) ![x]
  have hv : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) ![x] =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := rfl
  rw [hv] at h
  exact h.trans (modelZero ![x])

theorem modelMulSucc (x y : M) :
    Structure.func (L := language) mulCode
      ![x, Structure.func (L := language) Code.succ (fun _ => y)] =
    Structure.func (L := language) addCode
      ![Structure.func (L := language) mulCode ![x,y], x] := by
  rw [modelMulExpand, modelMulExpand]
  have hs := modelStep (M := M) (Code.zero 1)
    (Code.comp addCode (.cons (.proj (1 : Fin 3)) (.cons (.proj (2 : Fin 3)) (.nil 3)))) ![y,x]
  have hg := modelComposition (M := M) addCode
    (.cons (.proj (1 : Fin 3)) (.cons (.proj (2 : Fin 3)) (.nil 3)))
    ![y, Structure.func (L := language) mulCore ![y,x], x]
  have hgArg : (fun i => Structure.func (L := language)
      (getCode (.cons (.proj (1 : Fin 3)) (.cons (.proj (2 : Fin 3)) (.nil 3))) i)
      ![y, Structure.func (L := language) mulCore ![y,x], x]) =
      ![Structure.func (L := language) mulCore ![y,x], x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 1 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 2 _
  rw [hgArg] at hg
  change Structure.func (L := language) mulCore
      ![Structure.func (L := language) Code.succ (fun _ => y), x] =
    Structure.func (L := language)
      (Code.comp addCode (.cons (.proj (1 : Fin 3)) (.cons (.proj (2 : Fin 3)) (.nil 3))))
      ![y, Structure.func (L := language) mulCore ![y,x], x] at hs
  exact hs.trans hg

theorem modelMulZeroSentence : M↓[language] ⊧ mulZeroSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode (.zero 0) Fin.elim0]) =
      ![e 0, Structure.func (L := language) (Code.zero 0) Fin.elim0] := by
    have hz' : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 1)) =
        (Fin.elim0 : Fin 0 → M) := hz
    simpa [applyCode, Function.comp_def, hz'] using
      val_term_pair e (.bvar 0) (applyCode (.zero 0) Fin.elim0)
  simp only [applyCode] at hv
  rw [hv, hz]
  exact modelMulZero (e 0)

theorem modelMulSuccSentence : M↓[language] ⊧ mulSuccSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hpair : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    simpa only [Semiterm.val_bvar] using val_term_pair e (.bvar 0) (.bvar 1)
  have hleft : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)]) =
      ![e 0, Structure.func (L := language) Code.succ (fun _ => e 1)] := by
    simpa [applyCode, Function.comp_def] using
      val_term_pair e (.bvar 0) (applyCode Code.succ (fun _ => .bvar 1))
  have hright : (Semiterm.val e Empty.elim ∘ ![applyCode mulCode ![.bvar 0, .bvar 1], .bvar 0]) =
      ![Structure.func (L := language) mulCode ![e 0, e 1], e 0] := by
    simpa only [applyCode, Semiterm.val_func, Semiterm.val_bvar, hpair] using
      val_term_pair e (applyCode mulCode ![.bvar 0, .bvar 1]) (.bvar 0)
  simp only [applyCode] at hleft hright
  rw [hleft, hright]
  exact modelMulSucc (e 0) (e 1)

end models

/-- The candidate PRA derives the zero clause of multiplication. -/
theorem PRA_proves_mulZero : PRA ⊢ mulZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelMulZeroSentence

/-- The candidate PRA derives the successor clause of multiplication. -/
theorem PRA_proves_mulSucc : PRA ⊢ mulSuccSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelMulSuccSentence

end DiophantineConsistency.PRAMultiplication
