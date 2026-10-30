import DiophantineConsistency.PRAPositiveCode
import DiophantineConsistency.PRAJoostenWitnessedRule
import DiophantineConsistency.ParsonsPositiveComparison
import DiophantineConsistency.ParsonsMapInduction
/-! Semantic adapters for the positive coded induction-rule client. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveRuleSemantics
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation
  PRAJoostenWitnessedRule HerbrandParameterizedWitness HerbrandContextualTreeSelection
  ParsonsRule ParsonsMapInduction

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
  rw [h]; rfl⟩
local instance : Structure.One language M := ⟨by
  simp only [Semiterm.Operator.val, Semiterm.Operator.One.one, Semiterm.val_func]
  have h : (Semiterm.val ![] Empty.elim ∘ (![] : Fin 0 → Semiterm language Empty 0)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [h]; rfl⟩
local instance : Structure.Add language M := ⟨fun _ _ => rfl⟩

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelMappedBase (φ : ArithmeticSemiformula ℕ 1) (e : ℕ → M) :
    (Semiformula.lMap embedding (base φ)).Eval ![] e ↔
      (Semiformula.lMap embedding φ).Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e := by
  simp [base, Semiformula.lMap_subst, map_zero, Semiformula.eval_substs,
    Semiterm.Operator.numeral_zero, Structure.Zero.zero]
  rfl

theorem modelMappedStep (φ : ArithmeticSemiformula ℕ 1) (e : ℕ → M) :
    (Semiformula.lMap embedding (step φ)).Eval ![] e ↔
      ∀ x : M, (Semiformula.lMap embedding φ).Eval ![x] e →
        (Semiformula.lMap embedding φ).Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e := by
  simp [step, Semiformula.lMap_subst, map_add_one, Semiformula.eval_substs,
    Semiterm.Operator.numeral_one, Structure.One.one]
  change (∀ x : M, (Semiformula.lMap embedding φ).Eval ![x] e →
    (Semiformula.lMap embedding φ).Eval ![x+1] e) ↔ _
  have hs (x : M) : x+1 = Structure.func (L := language) Code.succ (fun _ => x) := by
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] = _
    exact modelAddOne x
  simp only [hs]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelParameterSideAll {n : ℕ} (side : Semisentence language n) (e : ℕ → M) :
    (parameterSide side).Eval ![] e ↔ side.Eval (fun i => e i.val) Empty.elim := by
  unfold parameterSide
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![] e ∘
      Rew.embSubsts (fun i : Fin n => .fvar i.val) ∘ Semiterm.bvar) = (fun i : Fin n => e i.val) := by
    funext i; rfl
  have hf : (Semiterm.val (L := language) ![] e ∘
      Rew.embSubsts (fun i : Fin n => .fvar i.val) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* PRA] in
theorem modelParameterMatrixAll {n : ℕ} (C : Semisentence language (n+1)) (w : M) (e : ℕ → M) :
    (parameterMatrix C).Eval ![w] e ↔ C.Eval (Fin.cases w (fun i => e i.val)) Empty.elim := by
  unfold parameterMatrix
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![w] e ∘
      Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) ∘ Semiterm.bvar) =
      Fin.cases w (fun i => e i.val) := by
    funext i; exact Fin.cases rfl (fun _ => rfl) i
  have hf : (Semiterm.val (L := language) ![w] e ∘
      Rew.embSubsts (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val)) ∘ Semiterm.fvar) =
      (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hb,hf]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelExistentialBody {n : ℕ} (pred : Code (n+2)) (x : M) (e : ℕ → M) :
    (existentialBody pred).Eval ![x] e ↔
      ∃ y : M, Structure.func (L := language) pred
        (Fin.cases x (Fin.cases y (fun i : Fin n => e i.val))) =
          Structure.func (L := language) oneCode Fin.elim0 := by
  change (∃⁰ Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val))),
      .func oneCode Fin.elim0] : Semiproposition language 1).Eval ![x] e ↔ _
  simp only [Semiformula.eval_ex, Semiformula.eval_rel, eqRel]
  apply exists_congr
  intro y
  change Structure.func (L := language) pred (Semiterm.val ![y,x] e ∘
    Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val))) =
      Structure.func (L := language) oneCode (Semiterm.val ![y,x] e ∘ Fin.elim0) ↔ _
  have hz : (Semiterm.val (L := language) ![y,x] e ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val (L := language) ![y,x] e ∘
      Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (fun i : Fin n => .fvar i.val))) =
      Fin.cases x (Fin.cases y (fun i : Fin n => e i.val)) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun _ => rfl) j
  rw [hv,hz]
end models
end DiophantineConsistency.PRAPositiveRuleSemantics
