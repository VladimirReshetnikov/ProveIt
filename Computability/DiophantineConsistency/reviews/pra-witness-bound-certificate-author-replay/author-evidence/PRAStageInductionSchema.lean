import DiophantineConsistency.PRAStageCodedInduction
import DiophantineConsistency.PRABoundedInduction
/-! Relate the explicit coded counterexample to Foundation successor induction. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageInductionSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRAStageCodedInduction

/-- An explicit Σ₁ predicate, with c in free variable n and the remaining
parameters in free variables below n. -/
def codedSigma {n : ℕ} (pred : Code (n+3)) : Semiproposition language 1 :=
  ∃⁰ (Semiformula.rel Language.ORing.Rel.eq
    ![.func pred (Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (Fin.cases (.fvar n)
      (fun i : Fin n => .fvar i.val)))), .func oneCode Fin.elim0])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelCodedSigma {n : ℕ} (pred : Code (n+3)) (e : ℕ → M) (x : M) :
    (codedSigma pred).Eval ![x] e ↔ ∃ y,
      Structure.func (L := language) pred (Fin.cases x (Fin.cases y
        (Fin.cases (e n) (fun i : Fin n => e i.val)))) =
          Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [codedSigma, Semiformula.eval_ex, Semiformula.eval_rel, eqRel]
  change (∃ y, Structure.func (L := language) pred (Semiterm.val ![y,x] e ∘
    Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (Fin.cases (.fvar n) (fun i : Fin n => .fvar i.val)))) =
    Structure.func (L := language) oneCode (Semiterm.val ![y,x] e ∘ Fin.elim0)) ↔ _
  have hv (y : M) : (Semiterm.val (L := language) ![y,x] e ∘
      Fin.cases (.bvar 1) (Fin.cases (.bvar 0) (Fin.cases (.fvar n) (fun i : Fin n => .fvar i.val)))) =
      Fin.cases x (Fin.cases y (Fin.cases (e n) (fun i : Fin n => e i.val))) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun _ => rfl) k
  have hz (y : M) : (Semiterm.val (L := language) ![y,x] e ∘ Fin.elim0) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp only [hv, hz]

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

theorem modelCodedSuccInd {n : ℕ} (pred : Code (n+3)) (e : ℕ → M) :
    (succInd (codedSigma pred)).Eval ![] e ↔
      ((codedSigma pred).Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e →
       (∀ x : M, (codedSigma pred).Eval ![x] e →
         (codedSigma pred).Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e) →
       ∀ x : M, (codedSigma pred).Eval ![x] e) := by
  simp [succInd, Semiformula.eval_substs, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.numeral_one, Structure.Zero.zero, Structure.One.one]
  change ((codedSigma pred).Eval ![(0 : M)] e →
    (∀ x : M, (codedSigma pred).Eval ![x] e → (codedSigma pred).Eval ![x+1] e) →
      ∀ x : M, (codedSigma pred).Eval ![x] e) ↔ _
  have hz : (0 : M) = Structure.func (L := language) (Code.zero 0) Fin.elim0 := rfl
  have hs (x : M) : x+1 = Structure.func (L := language) Code.succ (fun _ => x) := by
    change Structure.func (L := language) addCode
      ![x, Structure.func (L := language) oneCode Fin.elim0] = _
    exact modelAddOne x
  simp only [hz, hs]


/-- With no external predicate parameters, the χ-dual's universal closure
is exactly Foundation successor induction for the explicit coded Σ₁ formula. -/
theorem modelClosedInduction_iff (pred : Code 3) :
    M↓[language] ⊧ (inductionFormula pred).univCl ↔
      M↓[language] ⊧ (succInd (codedSigma pred)).univCl := by
  simp only [models_iff, Semiformula.eval_univCl]
  constructor
  · intro h e
    apply (modelCodedSuccInd pred e).mpr
    intro hb hs z
    have hi := (modelInductionFormula pred e).mp (h e)
    have hbase := (modelCodedSigma pred e _).mp hb
    have hstep (x : M) (hx : ∃ y,
        Structure.func (L := language) pred (Fin.cases x (Fin.cases y
          (Fin.cases (e 0) (fun i : Fin 0 => e i.val)))) = Structure.func (L := language) oneCode Fin.elim0) :=
      (modelCodedSigma pred e _).mp (hs x ((modelCodedSigma pred e x).mpr hx))
    exact (modelCodedSigma pred e z).mpr (hi (e 0) z ⟨hbase,hstep⟩)
  · intro h e
    apply (modelInductionFormula pred e).mpr
    intro c z
    dsimp only
    intro ⟨hbase,hstep⟩
    let e' : ℕ → M := Function.update e 0 c
    have hi := (modelCodedSuccInd pred e').mp (h e')
    have hb : (codedSigma pred).Eval ![Structure.func (L := language) (Code.zero 0) Fin.elim0] e' := by
      apply (modelCodedSigma pred e' _).mpr
      simpa [e'] using hbase
    have hs : ∀ x : M, (codedSigma pred).Eval ![x] e' →
        (codedSigma pred).Eval ![Structure.func (L := language) Code.succ (fun _ => x)] e' := by
      intro x hx
      apply (modelCodedSigma pred e' _).mpr
      have h' := (modelCodedSigma pred e' x).mp hx
      have hx' := hstep x (by simpa [e'] using h')
      simpa [e'] using hx'
    have hz := (modelCodedSigma pred e' z).mp (hi hb hs z)
    simpa [e'] using hz
end models
/-- Candidate PRA proves both directions between the concrete coded induction
axiom and Foundation's actual successor-induction schema instance. -/
theorem PRA_proves_inductionFormula_to_succInd (pred : Code 3) :
    PRA ⊢ ((inductionFormula pred).univCl 🡒 (succInd (codedSigma pred)).univCl) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have h := (modelClosedInduction_iff (M := M) pred).mp
  simpa [models_iff] using h

theorem PRA_proves_succInd_to_inductionFormula (pred : Code 3) :
    PRA ⊢ ((succInd (codedSigma pred)).univCl 🡒 (inductionFormula pred).univCl) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have h := (modelClosedInduction_iff (M := M) pred).mpr
  simpa [models_iff] using h
end DiophantineConsistency.PRAStageInductionSchema
