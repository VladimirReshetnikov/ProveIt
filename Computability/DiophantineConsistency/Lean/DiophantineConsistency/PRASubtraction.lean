import DiophantineConsistency.PRAExhaustion

/-! Candidate PRA derivations of truncated-subtraction recursion. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion

def subZeroSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode subCode ![.bvar 0, applyCode (.zero 0) Fin.elim0]) (.bvar 0)

def subSuccSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode subCode ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)])
    (applyCode predCode (fun _ => applyCode subCode ![.bvar 0, .bvar 1]))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSubExpand (x y : M) :
    Structure.func (L := language) subCode ![x,y] =
      Structure.func (L := language) subCore ![y,x] := by
  have h := modelComposition (M := M) subCore
    (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) ![x,y]
  have harg : (fun i => Structure.func (L := language)
      (getCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) i) ![x,y]) = ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 1 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 0 _
  change Structure.func (L := language) subCode ![x,y] = _ at h
  rw [harg] at h
  exact h

theorem modelSubZero (x : M) :
    Structure.func (L := language) subCode
      ![x, Structure.func (L := language) (Code.zero 0) Fin.elim0] = x := by
  rw [modelSubExpand]
  have h := modelBase (M := M) (Code.proj (0 : Fin 1))
    (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3))) ![x]
  have hv : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) ![x] =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := rfl
  rw [hv, modelProjection] at h
  exact h

theorem modelSubSucc (x y : M) :
    Structure.func (L := language) subCode
      ![x, Structure.func (L := language) Code.succ (fun _ => y)] =
    Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) subCode ![x,y]) := by
  rw [modelSubExpand, modelSubExpand]
  have hs := modelStep (M := M) (Code.proj (0 : Fin 1))
    (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3))) ![y,x]
  have hg := modelComposition (M := M) predCode (.cons (.proj (1 : Fin 3)) (.nil 3))
    ![y, Structure.func (L := language) subCore ![y,x], x]
  have hgArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.proj (1 : Fin 3)) (.nil 3)) i)
      ![y, Structure.func (L := language) subCore ![y,x], x]) =
      fun _ => Structure.func (L := language) subCore ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelProjection (M := M) 1 _
  rw [hgArg] at hg
  change Structure.func (L := language) subCore
      ![Structure.func (L := language) Code.succ (fun _ => y), x] =
    Structure.func (L := language) (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3)))
      ![y, Structure.func (L := language) subCore ![y,x], x] at hs
  exact hs.trans hg

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem eqRel (v : Fin 2 → M) :
    Structure.rel (L := language) Language.ORing.Rel.eq v ↔ v 0 = v 1 := by
  change Structure.rel (L := language) Language.Eq.eq v ↔ _
  exact Structure.eq_lang

omit [M↓[language] ⊧* PRA] in
private theorem eqClosureModels {n : ℕ} (a b : TermN n) :
    (M↓[language] ⊧ equalClosure a b) ↔
      ∀ e : Fin n → M, Semiterm.val e Empty.elim a = Semiterm.val e Empty.elim b := by
  simp only [models_iff, equalClosure, Semiformula.eval_allClosure, Semiformula.eval_rel]
  constructor
  · intro h e
    have h' := (eqRel _).mp (h e)
    simpa [Function.comp_def] using h'
  · intro h e
    apply (eqRel _).mpr
    simpa [Function.comp_def] using h e

theorem modelSubZeroSentence : M↓[language] ⊧ subZeroSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func, Semiterm.val_bvar]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode (.zero 0) Fin.elim0]) =
      ![e 0, Structure.func (L := language) (Code.zero 0) Fin.elim0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      change Structure.func (L := language) (Code.zero 0)
        (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN 1)) = _
      rw [hz]
      rfl
  simp only [applyCode] at hv
  rw [hv]
  exact modelSubZero (e 0)

theorem modelSubSuccSentence : M↓[language] ⊧ subSuccSentence := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hpair : (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = ![e 0, e 1] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  have hleft : (Semiterm.val e Empty.elim ∘ ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)]) =
      ![e 0, Structure.func (L := language) Code.succ (fun _ => e 1)] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl
  have hright : (Semiterm.val e Empty.elim ∘ fun _ : Fin 1 => applyCode subCode ![.bvar 0, .bvar 1]) =
      fun _ => Structure.func (L := language) subCode ![e 0, e 1] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    change Structure.func (L := language) subCode
      (Semiterm.val e Empty.elim ∘ ![(.bvar 0 : TermN 2), .bvar 1]) = _
    rw [hpair]
  simp only [applyCode] at hleft hright
  rw [hleft, hright]
  exact modelSubSucc (e 0) (e 1)


end models

/-- Candidate PRA proves x−0=x. -/
theorem PRA_proves_subZero : PRA ⊢ subZeroSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelSubZeroSentence

/-- Candidate PRA proves x−succ(y)=pred(x−y). -/
theorem PRA_proves_subSucc : PRA ⊢ subSuccSentence := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact modelSubSuccSentence

end DiophantineConsistency.PRASubtraction
