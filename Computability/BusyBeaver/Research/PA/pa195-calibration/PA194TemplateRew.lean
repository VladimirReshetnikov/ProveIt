import PA194BitTemplate
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Coding

/-! Capture-avoiding lift of the two source-label substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194TemplateRew
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

def outerRew (a b : Nat) : Rew ℒₒᵣ Empty 2 Nat 0 :=
  Rew.embSubsts ![&a,&b]

def depthRew (a b : Nat) : (d : Nat) → Rew ℒₒᵣ Empty (d+2) Nat d
  | 0 => outerRew a b
  | d+1 => (depthRew a b d).q

theorem depthRew_var (a b d : Nat) (i : Fin (d+2)) :
    depthRew a b d #i =
      if h : i.val < d then #⟨i.val,h⟩
      else if i.val = d then &a else &b := by
  induction d with
  | zero =>
    cases i using Fin.cases with
    | zero => simp [depthRew, outerRew]
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [depthRew, outerRew]
      | succ k => exact Fin.elim0 k
  | succ d ih =>
    cases i using Fin.cases with
    | zero => simp [depthRew]
    | succ j =>
      rw [depthRew, Rew.q_bvar_succ]
      have h := ih j
      rw [h]
      split <;> split <;> simp_all

section models
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA194BitTemplate
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := DiophantineConsistency.PRAModelIOpenPairing.standardModelIOpen

theorem termExpected_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Nat) (t : ClosedSemiterm ℒₒᵣ (d+2)) (a b : Nat) :
    termExpected d t (a : M) (b : M) = (⌜(depthRew a b d) t⌝ : M) := by
  induction t with
  | bvar i =>
    rw [termExpected,depthRew_var]
    split
    · simp [Semiterm.quote_bvar,qqBvar]
    · split <;> simp [Semiterm.quote_fvar,qqFvar]
  | fvar z => exact Empty.elim z
  | @func k f v ih =>
    rw [termExpected, Rew.func, Semiterm.quote_func]
    simp only [qqFunc]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact ih i

theorem formulaExpected_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Nat) (φ : ArithmeticSemisentence (d+2)) (a b : Nat) :
    formulaExpected d φ (a : M) (b : M) = (⌜depthRew a b d ▹ φ⌝ : M) := by
  cases φ with
  | verum =>
    rw [formulaExpected]
    change pair 2 0 + 1 = (⌜(⊤ : Semiproposition ℒₒᵣ d)⌝ : M)
    simp [Semiformula.quote_verum, qqVerum]
  | falsum =>
    rw [formulaExpected]
    change pair 3 0 + 1 = (⌜(⊥ : Semiproposition ℒₒᵣ d)⌝ : M)
    simp [Semiformula.quote_falsum, qqFalsum]
  | rel r v =>
    rw [formulaExpected, Semiformula.rew_rel, Semiformula.quote_rel]
    simp only [qqRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_quote d (v i) a b
  | nrel r v =>
    rw [formulaExpected, Semiformula.rew_nrel, Semiformula.quote_nrel]
    simp only [qqNRel]
    congr 4
    simp only [SemitermVec.val,matrixToVec,adjoin_def]
    congr 1
    funext i
    exact termExpected_quote d (v i) a b
  | and p q =>
    rw [formulaExpected]
    change pair 4 (pair (formulaExpected d p (a : M) (b : M)) (formulaExpected d q (a : M) (b : M))) + 1 =
      (⌜(depthRew a b d ▹ p) ⋏ (depthRew a b d ▹ q)⌝ : M)
    rw [Semiformula.quote_and]
    change pair 4 (pair (formulaExpected d p (a : M) (b : M)) (formulaExpected d q (a : M) (b : M))) + 1 =
      pair 4 (pair (⌜depthRew a b d ▹ p⌝ : M) (⌜depthRew a b d ▹ q⌝ : M)) + 1
    rw [formulaExpected_quote d p a b, formulaExpected_quote d q a b]
  | or p q =>
    rw [formulaExpected]
    change pair 5 (pair (formulaExpected d p (a : M) (b : M)) (formulaExpected d q (a : M) (b : M))) + 1 =
      (⌜(depthRew a b d ▹ p) ⋎ (depthRew a b d ▹ q)⌝ : M)
    rw [Semiformula.quote_or]
    change pair 5 (pair (formulaExpected d p (a : M) (b : M)) (formulaExpected d q (a : M) (b : M))) + 1 =
      pair 5 (pair (⌜depthRew a b d ▹ p⌝ : M) (⌜depthRew a b d ▹ q⌝ : M)) + 1
    rw [formulaExpected_quote d p a b, formulaExpected_quote d q a b]
  | all p =>
    rw [formulaExpected]
    change pair 6 (formulaExpected (d+1) p (a : M) (b : M)) + 1 =
      (⌜∀⁰ (depthRew a b (d+1) ▹ p)⌝ : M)
    rw [Semiformula.quote_all]
    change pair 6 (formulaExpected (d+1) p (a : M) (b : M)) + 1 =
      pair 6 (⌜depthRew a b (d+1) ▹ p⌝ : M) + 1
    rw [formulaExpected_quote (d+1) p a b]
  | exs p =>
    rw [formulaExpected]
    change pair 7 (formulaExpected (d+1) p (a : M) (b : M)) + 1 =
      (⌜∃⁰ (depthRew a b (d+1) ▹ p)⌝ : M)
    rw [Semiformula.quote_ex]
    change pair 7 (formulaExpected (d+1) p (a : M) (b : M)) + 1 =
      pair 7 (⌜depthRew a b (d+1) ▹ p⌝ : M) + 1
    rw [formulaExpected_quote (d+1) p a b]
termination_by φ.complexity

/-- For standard source labels in an IΣ₁ model, the generated PR code is
the Foundation quote of the actual capture-avoiding template substitution. -/
theorem modelTemplateCode_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (d : Nat) (φ : ArithmeticSemisentence (d+2)) (a b : Nat) :
    Structure.func (L := language) (formulaCode d φ) ![(a : M),(b : M)] =
      (⌜depthRew a b d ▹ φ⌝ : M) := by
  rw [modelFormulaCode]
  exact formulaExpected_quote d φ a b

/-- Concrete membership compiler: the PR-code value is the quoted exact
bounded bit formula after capture-avoiding substitution of the source labels. -/
theorem modelBitTemplateCode_quote [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (a b : Nat) :
    Structure.func (L := language) bitTemplateCode ![(a : M),(b : M)] =
      (⌜outerRew a b ▹ bitDef.val⌝ : M) := by
  exact modelTemplateCode_quote 0 bitDef.val a b

end models
#print axioms modelTemplateCode_quote
#print axioms modelBitTemplateCode_quote
#print axioms formulaExpected_quote
#print axioms termExpected_quote
#print axioms depthRew_var
end PA194TemplateRew
