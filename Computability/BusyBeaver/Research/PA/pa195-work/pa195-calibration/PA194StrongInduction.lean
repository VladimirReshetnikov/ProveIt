import DiophantineConsistency.PRABoundedInduction
import DiophantineConsistency.PRAModelIOpenPairing

/-! Strong induction for any fixed binary PR characteristic code in arbitrary
candidate-PRA models, including nonstandard indices. This is a generic
prerequisite for numeric decoder occurrence, not the occurrence constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA194StrongInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABoundedInduction

def belowBody (f : Code 2) : Semiproposition language 1 :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0,#1])]
    (Semiformula.rel Language.ORing.Rel.eq ![.func f ![#0,&0], .func oneCode Fin.elim0])

theorem belowBody_bounded (f : Code 2) : Hierarchy 𝚺 0 (belowBody f) := by
  unfold belowBody
  apply Hierarchy.ball
  · simp [Semiterm.Positive]
  · exact Hierarchy.rel _ _ _ _

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
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

def value (f : Code 2) (i v : M) : M := Structure.func (L := language) f ![i,v]

theorem belowBody_eval (f : Code 2) (n v : M) :
    (belowBody f).Eval ![n] (fun _ => v) ↔ ∀ i < n, value f i v = 1 := by
  have hz (x : M) : (Semiterm.val (L := language) ![x,n] (fun _ : ℕ => v) ∘
      (Fin.elim0 : Fin 0 → Semiterm language ℕ 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [belowBody, Semiformula.eval_ball, Semiformula.eval_rel, eqRel, value, Semiterm.val_func, hz]
  rfl

/-- Strong induction for a fixed PR code and arbitrary model parameter v. -/
theorem modelStrongCode (f : Code 2) (v : M)
    (step : ∀ n : M, (∀ i < n, value f i v = 1) → value f n v = 1) :
    ∀ n : M, value f n v = 1 := by
  have hInd : (belowBody f).Eval ![(0 : M)] (fun _ => v) →
      (∀ n : M, (belowBody f).Eval ![n] (fun _ => v) →
        (belowBody f).Eval ![n+1] (fun _ => v)) →
      ∀ n : M, (belowBody f).Eval ![n] (fun _ => v) := by
    have h := modelBoundedInductionAxiom (M := M) (belowBody f) (belowBody_bounded f)
    simp [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs] at h
    simpa [Semiterm.Operator.numeral_zero, Semiterm.Operator.numeral_one,
      Structure.Zero.zero, Structure.One.one] using h (fun _ => v)
  have hbase : (belowBody f).Eval ![(0 : M)] (fun _ => v) := by
    apply (belowBody_eval f 0 v).mpr
    intro i hi
    exact False.elim (not_lt_zero hi)
  have hstep (n : M) (hn : (belowBody f).Eval ![n] (fun _ => v)) :
      (belowBody f).Eval ![n+1] (fun _ => v) := by
    apply (belowBody_eval f (n+1) v).mpr
    intro i hi
    have hle : i ≤ n := lt_succ_iff_le.mp hi
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (belowBody_eval f n v).mp hn i hlt
    · subst i
      exact step n ((belowBody_eval f n v).mp hn)
  have hall : ∀ n : M, (belowBody f).Eval ![n] (fun _ => v) := hInd hbase hstep
  intro n
  apply step n
  exact (belowBody_eval f n v).mp (hall n)
end models
#print axioms modelStrongCode
end PA194StrongInduction
