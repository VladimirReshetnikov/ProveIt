import DiophantineConsistency.PRAExhaustion

/-! Parameterized open induction in arbitrary equality models of candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAOpenInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Structure.Zero language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.Zero.zero, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]
  rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]
  rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

/-- Open induction with arbitrary free-variable parameters and primitive successor. -/
theorem modelOpenInduction (φ : Semiformula language ℕ 1) (hOpen : φ.Open) (e : ℕ → M)
    (hZero : φ.Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e)
    (hSucc : ∀ x, φ.Eval ![x] e →
      φ.Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) :
    ∀ x, φ.Eval ![x] e := by
  have hInd : M↓[language] ⊧ (succInd φ).univCl :=
    Theory.models (T := PRA) M (Or.inl (Or.inr ⟨φ, hOpen, rfl⟩))
  have inductionRule : φ.Eval ![(0 : M)] e →
      (∀ x, φ.Eval ![x] e → φ.Eval ![x+1] e) → ∀ x, φ.Eval ![x] e := by
    have h := hInd
    simp [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs] at h
    simpa [Semiterm.Operator.numeral_zero, Semiterm.Operator.numeral_one,
      Structure.Zero.zero, Structure.One.one] using h e
  apply inductionRule hZero
  intro x hx
  change φ.Eval ![Structure.func (L := language) addCode
    ![x, Structure.func (L := language) oneCode Fin.elim0]] e
  rw [modelAddOne]
  exact hSucc x hx

end models
end DiophantineConsistency.PRAOpenInduction
