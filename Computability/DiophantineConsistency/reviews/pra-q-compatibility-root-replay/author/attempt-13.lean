import DiophantineConsistency.PRAAddition
import DiophantineConsistency.PRAMultiplication
import DiophantineConsistency.PRAExhaustion
import Foundation.FirstOrder.Arithmetic.Q.Basic

/-! Compatibility of the candidate PRA with exact ordered-ring Robinson Q
axioms. This module does not assume conservation or identify the theories. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAQCompatibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAMultiplication PRAExhaustion

def qSuccNeZero : Sentence ℒₒᵣ := “∀ a, a + 1 ≠ 0”
def qSuccInj : Sentence ℒₒᵣ := “∀ a b, a + 1 = b + 1 → a = b”
def qZeroOrSucc : Sentence ℒₒᵣ := “∀ a, a = 0 ∨ ∃ b, a = b + 1”

def qAddZero : Sentence ℒₒᵣ := “∀ a, a + 0 = a”
def qAddSucc : Sentence ℒₒᵣ := “∀ a b, a + (b + 1) = (a + b) + 1”
def qMulZero : Sentence ℒₒᵣ := “∀ a, a * 0 = 0”
def qMulSucc : Sentence ℒₒᵣ := “∀ a b, a * (b + 1) = a * b + a”

theorem qSuccNeZero_mem : qSuccNeZero ∈ RobinsonQ := RobinsonQ.succNeZero
theorem qSuccInj_mem : qSuccInj ∈ RobinsonQ := RobinsonQ.succInj
theorem qZeroOrSucc_mem : qZeroOrSucc ∈ RobinsonQ := RobinsonQ.zeroOrSucc

theorem qAddZero_mem : qAddZero ∈ RobinsonQ := RobinsonQ.addZero
theorem qAddSucc_mem : qAddSucc ∈ RobinsonQ := RobinsonQ.addSucc
theorem qMulZero_mem : qMulZero ∈ RobinsonQ := RobinsonQ.mulZero
theorem qMulSucc_mem : qMulSucc ∈ RobinsonQ := RobinsonQ.mulSucc

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem reduct_eq :
    (inferInstance : Structure language M).lMap embedding = Arithmetic.standardModel M := by
  apply Structure.ext
  · funext k f v
    cases f with
    | zero =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | one =>
      have hv : v = Fin.elim0 := Subsingleton.elim _ _
      rw [hv]
      rfl
    | add =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
    | mul =>
      rw [Matrix.fun_eq_vec_two v]
      rfl
  · funext k r v
    cases r with
    | eq =>
      apply propext
      change Structure.rel (L := language) Language.Eq.eq v ↔ v 0 = v 1
      exact Structure.eq_lang
    | lt =>
      rw [Matrix.fun_eq_vec_two v]
      rfl

omit [Nonempty M] [M↓[language] ⊧* PRA] in
private theorem eqRel (v : Fin 2 → M) :
    Structure.rel (L := language) Language.ORing.Rel.eq v ↔ v 0 = v 1 := by
  change Structure.rel (L := language) Language.Eq.eq v ↔ _
  exact Structure.eq_lang

theorem modelSuccNeZero (x : M) :
    Structure.func (L := language) Code.succ (fun _ => x) ≠
      Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := Theory.models (T := PRA) M (Or.inr BasicAxiom.succNonzero)
  simp [models_iff, succNonzero, Semiformula.eval_allClosure] at h
  have hh := h ![x]
  rw [eqRel] at hh
  have hz : (fun i : Fin 0 => Semiterm.val ![x] Empty.elim (Fin.elim0 i : TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simpa [applyCode, Function.comp_def, hz] using hh

theorem modelSuccInj (x y : M) :
    Structure.func (L := language) Code.succ (fun _ => x) =
      Structure.func (L := language) Code.succ (fun _ => y) → x = y := by
  have h := Theory.models (T := PRA) M (Or.inr BasicAxiom.succInjective)
  simp [models_iff, succInjective, Semiformula.eval_allClosure] at h
  have hh := h ![x,y]
  simp only [eqRel] at hh
  simpa [applyCode, Function.comp_def] using hh

theorem model_qSuccNeZero : M↓[language] ⊧ Semiformula.lMap embedding qSuccNeZero := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qSuccNeZero := by
    simp [qSuccNeZero]
    intro x
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] ≠
        Structure.func (L := language) (Code.zero 0) Fin.elim0
    rw [modelAddOne]
    exact modelSuccNeZero x
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qSuccNeZero
  rw [reduct_eq]
  exact h

theorem model_qSuccInj : M↓[language] ⊧ Semiformula.lMap embedding qSuccInj := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qSuccInj := by
    simp [qSuccInj]
    intro x y
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] =
        Structure.func (L := language) addCode
          ![y, Structure.func (L := language) oneCode Fin.elim0] → x = y
    rw [modelAddOne, modelAddOne]
    exact modelSuccInj x y
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qSuccInj
  rw [reduct_eq]
  exact h

theorem model_qZeroOrSucc : M↓[language] ⊧ Semiformula.lMap embedding qZeroOrSucc := by
  have hEx := modelExhaustion (M := M)
  simp only [models_iff, exhaustionSentence, Semiformula.eval_univCl, Semiformula.eval_all] at hEx
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qZeroOrSucc := by
    simp [qZeroOrSucc]
    intro x
    have hb := (body_eval x (fun _ => x)).mp (hEx (fun _ => x) x)
    rcases hb with hz | hs
    · exact Or.inl hz
    · right
      refine ⟨Structure.func (L := language) predCode (fun _ => x), ?_⟩
      change x = Structure.func (L := language) addCode
        ![Structure.func (L := language) predCode (fun _ => x),
          Structure.func (L := language) oneCode Fin.elim0]
      rw [modelAddOne]
      exact hs.symm
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qZeroOrSucc
  rw [reduct_eq]
  exact h

theorem model_qAddZero : M↓[language] ⊧ Semiformula.lMap embedding qAddZero := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qAddZero := by
    simp [qAddZero]
    intro x
    exact modelAddZero x
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qAddZero
  rw [reduct_eq]
  exact h

theorem model_qAddSucc : M↓[language] ⊧ Semiformula.lMap embedding qAddSucc := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qAddSucc := by
    simp [qAddSucc]
    intro x y
    change Structure.func (L := language) addCode
        ![x, Structure.func (L := language) addCode ![y, Structure.func (L := language) oneCode Fin.elim0]] =
      Structure.func (L := language) addCode
        ![Structure.func (L := language) addCode ![x,y], Structure.func (L := language) oneCode Fin.elim0]
    rw [modelAddOne, modelAddOne]
    exact modelAddSucc x y
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qAddSucc
  rw [reduct_eq]
  exact h

theorem model_qMulZero : M↓[language] ⊧ Semiformula.lMap embedding qMulZero := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qMulZero := by
    simp [qMulZero]
    intro x
    exact modelMulZero x
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qMulZero
  rw [reduct_eq]
  exact h

theorem model_qMulSucc : M↓[language] ⊧ Semiformula.lMap embedding qMulSucc := by
  have h : Semiformula.Eval (s := Arithmetic.standardModel M) ![] Empty.elim qMulSucc := by
    simp [qMulSucc]
    intro x y
    change Structure.func (L := language) mulCode
        ![x, Structure.func (L := language) addCode ![y, Structure.func (L := language) oneCode Fin.elim0]] =
      Structure.func (L := language) addCode ![Structure.func (L := language) mulCode ![x,y], x]
    rw [modelAddOne]
    exact modelMulSucc x y
  simp only [models_iff, Semiformula.eval_lMap]
  change Semiformula.Eval (s := (inferInstance : Structure language M).lMap embedding) ![] Empty.elim qMulSucc
  rw [reduct_eq]
  exact h
end models

theorem PRA_proves_qSuccNeZero : PRA ⊢ Semiformula.lMap embedding qSuccNeZero := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qSuccNeZero

theorem PRA_proves_qSuccInj : PRA ⊢ Semiformula.lMap embedding qSuccInj := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qSuccInj

theorem PRA_proves_qZeroOrSucc : PRA ⊢ Semiformula.lMap embedding qZeroOrSucc := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qZeroOrSucc

theorem PRA_proves_qAddZero : PRA ⊢ Semiformula.lMap embedding qAddZero := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qAddZero

theorem PRA_proves_qAddSucc : PRA ⊢ Semiformula.lMap embedding qAddSucc := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qAddSucc

theorem PRA_proves_qMulZero : PRA ⊢ Semiformula.lMap embedding qMulZero := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qMulZero

theorem PRA_proves_qMulSucc : PRA ⊢ Semiformula.lMap embedding qMulSucc := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ _
  exact model_qMulSucc
end DiophantineConsistency.PRAQCompatibility
