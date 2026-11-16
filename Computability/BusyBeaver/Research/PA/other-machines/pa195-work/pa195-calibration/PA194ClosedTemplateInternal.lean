import PA194ClosedTemplate
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding

/-! Internal substitution corresponding to a fixed closed template after one
source label is closed. Labels may be arbitrary model values. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
namespace PA194ClosedTemplateInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA194ClosedTemplate

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : DecidableEq M := Classical.decEq M

noncomputable def closedSubstEnv (label a b : M) : (d : Nat) → SemitermVec M ℒₒᵣ (d+2) (d+1)
  | 0 => ![if label = a then Bootstrapping.Semiterm.bvar 0 else Bootstrapping.Semiterm.fvar a,
           if label = b then Bootstrapping.Semiterm.bvar 0 else Bootstrapping.Semiterm.fvar b]
  | d+1 => (closedSubstEnv label a b d).q

theorem closedSubstEnv_var (label a b : M) (d : Nat) (i : Fin (d+2)) :
    closedSubstEnv label a b d i =
      if h : i.val < d then Bootstrapping.Semiterm.bvar ⟨i.val,Nat.lt_succ_of_lt h⟩
      else if i.val = d then (if label = a then Bootstrapping.Semiterm.bvar ⟨d,Nat.lt_succ_self d⟩ else Bootstrapping.Semiterm.fvar a)
      else (if label = b then Bootstrapping.Semiterm.bvar ⟨d,Nat.lt_succ_self d⟩ else Bootstrapping.Semiterm.fvar b) := by
  induction d with
  | zero =>
    cases i using Fin.cases with
    | zero => simp [closedSubstEnv]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [closedSubstEnv]
      | succ k => exact Fin.elim0 k
  | succ d ih =>
    cases i using Fin.cases with
    | zero => simp [closedSubstEnv]
    | succ j =>
      rw [closedSubstEnv, SemitermVec.q_succ, ih j]
      split <;> split <;> (try split) <;> simp_all

theorem termExpected_internal (d : Nat) (t : ClosedSemiterm ℒₒᵣ (d+2)) (label a b : M) :
    termExpected d t label a b =
      (Bootstrapping.Semiterm.subst (closedSubstEnv label a b d)
        (⌜(Rew.emb t : SyntacticSemiterm ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiterm M ℒₒᵣ (d+2))).val := by
  induction t with
  | bvar i =>
    rw [termExpected]
    simp only [Rew.emb_bvar, Semiterm.typed_quote_bvar, Bootstrapping.Semiterm.substs_bvar, closedSubstEnv_var]
    split
    · simp [Bootstrapping.Semiterm.bvar,qqBvar]
    · split <;> split <;> simp [Bootstrapping.Semiterm.bvar, Bootstrapping.Semiterm.fvar,qqBvar,qqFvar]
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

theorem formulaExpected_internal (d : Nat) (φ : ArithmeticSemisentence (d+2)) (label a b : M) :
    formulaExpected d φ label a b =
      (Bootstrapping.Semiformula.subst (closedSubstEnv label a b d)
        (⌜(Rew.emb ▹ φ : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).val := by
  cases φ with
  | verum =>
    rw [formulaExpected]
    change pair 2 0 + 1 = ((⊤ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)).subst (closedSubstEnv label a b d)).val
    simp [Bootstrapping.Semiformula.substs_verum, Bootstrapping.Semiformula.val_verum, qqVerum]
  | falsum =>
    rw [formulaExpected]
    change pair 3 0 + 1 = ((⊥ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)).subst (closedSubstEnv label a b d)).val
    simp [Bootstrapping.Semiformula.substs_falsum, Bootstrapping.Semiformula.val_falsum, qqFalsum]
  | rel r v =>
    rw [formulaExpected, Semiformula.rew_rel, Semiformula.typed_quote_rel, Bootstrapping.Semiformula.substs_rel]
    simp only [Bootstrapping.Semiformula.rel,qqRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_internal d (v i) label a b
  | nrel r v =>
    rw [formulaExpected, Semiformula.rew_nrel, Semiformula.typed_quote_nrel, Bootstrapping.Semiformula.substs_nrel]
    simp only [Bootstrapping.Semiformula.nrel,qqNRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_internal d (v i) label a b
  | and p q =>
    rw [formulaExpected]
    change pair 4 (pair (formulaExpected d p label a b) (formulaExpected d q label a b)) + 1 =
      (((⌜(Rew.emb ▹ p : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)) ⋏
        (⌜(Rew.emb ▹ q : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).subst (closedSubstEnv label a b d)).val
    rw [Bootstrapping.Semiformula.substs_and]
    change pair 4 (pair (formulaExpected d p label a b) (formulaExpected d q label a b)) + 1 =
      pair 4 (pair _ _) + 1
    rw [formulaExpected_internal d p label a b, formulaExpected_internal d q label a b]
  | or p q =>
    rw [formulaExpected]
    change pair 5 (pair (formulaExpected d p label a b) (formulaExpected d q label a b)) + 1 =
      (((⌜(Rew.emb ▹ p : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2)) ⋎
        (⌜(Rew.emb ▹ q : Semiproposition ℒₒᵣ (d+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ (d+2))).subst (closedSubstEnv label a b d)).val
    rw [Bootstrapping.Semiformula.substs_or]
    change pair 5 (pair (formulaExpected d p label a b) (formulaExpected d q label a b)) + 1 =
      pair 5 (pair _ _) + 1
    rw [formulaExpected_internal d p label a b, formulaExpected_internal d q label a b]
  | all p =>
    rw [formulaExpected]
    change pair 6 (formulaExpected (d+1) p label a b) + 1 =
      ((∀⁰ (⌜((Rew.emb : Rew ℒₒᵣ Empty (d+2) Nat (d+2)).q ▹ p : Semiproposition ℒₒᵣ ((d+1)+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ ((d+1)+2))).subst (closedSubstEnv label a b d)).val
    simp only [Rew.q_emb]
    rw [Bootstrapping.Semiformula.substs_all]
    change pair 6 (formulaExpected (d+1) p label a b) + 1 = pair 6 _ + 1
    rw [←closedSubstEnv, formulaExpected_internal (d+1) p label a b]
  | exs p =>
    rw [formulaExpected]
    change pair 7 (formulaExpected (d+1) p label a b) + 1 =
      ((∃⁰ (⌜((Rew.emb : Rew ℒₒᵣ Empty (d+2) Nat (d+2)).q ▹ p : Semiproposition ℒₒᵣ ((d+1)+2))⌝ : Bootstrapping.Semiformula M ℒₒᵣ ((d+1)+2))).subst (closedSubstEnv label a b d)).val
    simp only [Rew.q_emb]
    rw [Bootstrapping.Semiformula.substs_ex]
    change pair 7 (formulaExpected (d+1) p label a b) + 1 = pair 7 _ + 1
    rw [←closedSubstEnv, formulaExpected_internal (d+1) p label a b]
termination_by φ.complexity


/-- Internal Foundation substitution of the exact positive bit template.
The three source labels may be nonstandard model elements. -/
theorem modelBitCloseInternal (label a b : M) :
    Structure.func (L := language) bitCloseCode ![label,a,b] =
      (Bootstrapping.Semiformula.subst (closedSubstEnv label a b 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  exact (modelFormulaCode 0 bitDef.val label a b).trans (formulaExpected_internal 0 bitDef.val label a b)

/-- Internal substitution of the exact negative bit template. -/
theorem modelNegativeBitCloseInternal (label a b : M) :
    Structure.func (L := language) negativeBitCloseCode ![label,a,b] =
      (Bootstrapping.Semiformula.subst (closedSubstEnv label a b 0)
        (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  exact (modelFormulaCode 0 (∼bitDef.val) label a b).trans (formulaExpected_internal 0 (∼bitDef.val) label a b)

#print axioms modelBitCloseInternal
#print axioms modelNegativeBitCloseInternal
#print axioms formulaExpected_internal
#print axioms termExpected_internal
#print axioms closedSubstEnv_var
end models
end PA194ClosedTemplateInternal
