import PA194BitTemplate
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding

/-! Internal Foundation substitution for model-valued source labels. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
namespace PA194TemplateInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA194BitTemplate

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := DiophantineConsistency.PRAModelIOpenPairing.standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def substEnv (a b : M) : (d : Nat) → SemitermVec M ℒₒᵣ (d+2) d
  | 0 => ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar b]
  | d+1 => (substEnv a b d).q

theorem substEnv_var (a b : M) (d : Nat) (i : Fin (d+2)) :
    substEnv a b d i =
      if h : i.val < d then Bootstrapping.Semiterm.bvar ⟨i.val,h⟩
      else if i.val = d then Bootstrapping.Semiterm.fvar a else Bootstrapping.Semiterm.fvar b := by
  induction d with
  | zero =>
    cases i using Fin.cases with
    | zero => simp [substEnv]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [substEnv]
      | succ k => exact Fin.elim0 k
  | succ d ih =>
    cases i using Fin.cases with
    | zero => simp [substEnv]
    | succ j =>
      rw [substEnv, SemitermVec.q_succ, ih j]
      split <;> split <;> simp_all


theorem termExpected_internal (d : Nat) (t : ClosedSemiterm ℒₒᵣ (d+2)) (a b : M) :
    termExpected d t a b =
      (Bootstrapping.Semiterm.subst (substEnv a b d)
        (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiterm M ℒₒᵣ (d+2))).val := by
  induction t with
  | bvar i =>
    rw [termExpected]
    simp only [Rew.emb_bvar, Semiterm.typed_quote_bvar, Bootstrapping.Semiterm.substs_bvar, substEnv_var]
    split
    · simp [Bootstrapping.Semiterm.bvar,qqBvar]
    · split <;> simp [Bootstrapping.Semiterm.fvar,qqFvar]
  | fvar z => exact Empty.elim z
  | @func k f v ih =>
    rw [termExpected]
    simp only [Rew.func, Semiterm.typed_quote_func, Bootstrapping.Semiterm.substs_func]
    simp only [Bootstrapping.Semiterm.func,qqFunc]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact ih i


theorem formulaExpected_internal (d : Nat) (φ : ArithmeticSemisentence (d+2)) (a b : M) :
    formulaExpected d φ a b =
      (Bootstrapping.Semiformula.subst (substEnv a b d)
        (⌜(Rew.emb ▹ φ : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).val := by
  cases φ with
  | verum =>
    rw [formulaExpected]
    change pair 2 0 + 1 = ((⊤ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)).subst (substEnv a b d)).val
    simp [Bootstrapping.Semiformula.substs_verum, Bootstrapping.Semiformula.val_verum, qqVerum]
  | falsum =>
    rw [formulaExpected]
    change pair 3 0 + 1 = ((⊥ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)).subst (substEnv a b d)).val
    simp [Bootstrapping.Semiformula.substs_falsum, Bootstrapping.Semiformula.val_falsum, qqFalsum]
  | rel r v =>
    rw [formulaExpected, Semiformula.rew_rel, Semiformula.typed_quote_rel, Bootstrapping.Semiformula.substs_rel]
    simp only [Bootstrapping.Semiformula.rel,qqRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_internal d (v i) a b
  | nrel r v =>
    rw [formulaExpected, Semiformula.rew_nrel, Semiformula.typed_quote_nrel, Bootstrapping.Semiformula.substs_nrel]
    simp only [Bootstrapping.Semiformula.nrel,qqNRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_internal d (v i) a b
  | and p q =>
    rw [formulaExpected]
    change pair 4 (pair (formulaExpected d p a b) (formulaExpected d q a b)) + 1 =
      (((⌜(Rew.emb ▹ p : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)) ⋏
        (⌜(Rew.emb ▹ q : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).subst (substEnv a b d)).val
    rw [Bootstrapping.Semiformula.substs_and]
    change pair 4 (pair (formulaExpected d p a b) (formulaExpected d q a b)) + 1 =
      pair 4 (pair _ _) + 1
    rw [formulaExpected_internal d p a b, formulaExpected_internal d q a b]
  | or p q =>
    rw [formulaExpected]
    change pair 5 (pair (formulaExpected d p a b) (formulaExpected d q a b)) + 1 =
      (((⌜(Rew.emb ▹ p : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)) ⋎
        (⌜(Rew.emb ▹ q : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).subst (substEnv a b d)).val
    rw [Bootstrapping.Semiformula.substs_or]
    change pair 5 (pair (formulaExpected d p a b) (formulaExpected d q a b)) + 1 =
      pair 5 (pair _ _) + 1
    rw [formulaExpected_internal d p a b, formulaExpected_internal d q a b]
  | all p =>
    rw [formulaExpected]
    change pair 6 (formulaExpected (d+1) p a b) + 1 =
      ((∀⁰ (⌜((Rew.emb : Rew ℒₒᵣ Empty (d+2) Nat (d+2)).q ▹ p : Semiproposition ℒₒᵣ ((d+1)+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ ((d+1)+2))).subst (substEnv a b d)).val
    simp only [Rew.q_emb]
    rw [Bootstrapping.Semiformula.substs_all]
    change pair 6 (formulaExpected (d+1) p a b) + 1 = pair 6 _ + 1
    rw [←substEnv, formulaExpected_internal (d+1) p a b]
  | exs p =>
    rw [formulaExpected]
    change pair 7 (formulaExpected (d+1) p a b) + 1 =
      ((∃⁰ (⌜((Rew.emb : Rew ℒₒᵣ Empty (d+2) Nat (d+2)).q ▹ p : Semiproposition ℒₒᵣ ((d+1)+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ ((d+1)+2))).subst (substEnv a b d)).val
    simp only [Rew.q_emb]
    rw [Bootstrapping.Semiformula.substs_ex]
    change pair 7 (formulaExpected (d+1) p a b) + 1 = pair 7 _ + 1
    rw [←substEnv, formulaExpected_internal (d+1) p a b]
termination_by φ.complexity


/-- Internal substitution theorem for arbitrary model labels, including
nonstandard values; the model's arithmetic reduct must satisfy IΣ₁. -/
theorem modelBitTemplate_internal (a b : M) :
    Structure.func (L := language) bitTemplateCode ![a,b] =
      (Bootstrapping.Semiformula.subst (substEnv a b 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  exact (modelFormulaCode 0 bitDef.val a b).trans (formulaExpected_internal 0 bitDef.val a b)

#print axioms modelBitTemplate_internal
#print axioms formulaExpected_internal
#print axioms termExpected_internal
#print axioms substEnv_var
end models
end PA194TemplateInternal
