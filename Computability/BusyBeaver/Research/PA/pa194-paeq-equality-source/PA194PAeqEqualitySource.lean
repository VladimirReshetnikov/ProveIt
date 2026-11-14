import PA194PAeqFormulaQuote
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeqEqualitySource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem arithmetic_symm_mem : Theory.Eq.symm ℒₒᵣ ∈ PeanoMinus :=
  PeanoMinus.equal _ Theory.eqAxiom.symm

theorem arithmetic_trans_mem : Theory.Eq.trans ℒₒᵣ ∈ PeanoMinus :=
  PeanoMinus.equal _ Theory.eqAxiom.trans

local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl

theorem symm_formula : PA194PAeq.formula (Rewriting.emb (Theory.Eq.symm ℒₒᵣ) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb PA194PAeq.symmetry.univCl : Semiproposition PA194PAeq.language 0) := by
  have hclosed : PA194PAeq.symmetry.freeVariables = ∅ := by decide
  change PA194PAeq.formula (Rewriting.emb (Theory.Eq.symm ℒₒᵣ) : ArithmeticSemiformula ℕ 0) =
    (PA194PAeq.symmetry.univCl : Proposition PA194PAeq.language)
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of _ hclosed]
  rfl

theorem symm_translation : formulaCode (0:V) (⌜Theory.Eq.symm ℒₒᵣ⌝ : V) =
    (⌜PA194PAeq.symmetry.univCl⌝ : V) := by
  rw [Sentence.quote_def, Sentence.quote_def, formulaCode_quote, symm_formula]

theorem trans_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.trans ℒₒᵣ) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb PA194PAeq.transitivity.univCl : Semiproposition PA194PAeq.language 0) := by
  have hclosed : PA194PAeq.transitivity.freeVariables = ∅ := by decide
  change PA194PAeq.formula (Rewriting.emb (Theory.Eq.trans ℒₒᵣ) : ArithmeticSemiformula ℕ 0) =
    (PA194PAeq.transitivity.univCl : Proposition PA194PAeq.language)
  rw [Semiformula.coe_univCl_eq_univCl', Semiformula.univCl'_eq_self_of _ hclosed]
  rfl

theorem trans_translation : formulaCode (0:V) (⌜Theory.Eq.trans ℒₒᵣ⌝ : V) =
    (⌜PA194PAeq.transitivity.univCl⌝ : V) := by
  rw [Sentence.quote_def, Sentence.quote_def, formulaCode_quote, trans_formula]

theorem symm_mem : PA194PAeq.symmetry.univCl ∈ PA194PAeq.targetFixedTheory := by
  change PA194PAeq.symmetry.univCl ∈ PA194PAeq.targetFixedSentences
  exact List.mem_map.mpr ⟨_, by simp [PA194PAeq.fixedAxioms], rfl⟩

theorem trans_mem : PA194PAeq.transitivity.univCl ∈ PA194PAeq.targetFixedTheory := by
  change PA194PAeq.transitivity.univCl ∈ PA194PAeq.targetFixedSentences
  exact List.mem_map.mpr ⟨_, by simp [PA194PAeq.fixedAxioms], rfl⟩

theorem symm_witness :
    Proof PA194PAeq.targetFixedTheory
      (Bootstrapping.axm {⌜PA194PAeq.symmetry.univCl⌝} ⌜PA194PAeq.symmetry.univCl⌝ : V)
      (formulaCode 0 (⌜Theory.Eq.symm ℒₒᵣ⌝ : V)) := by
  rw [symm_translation]
  exact PA194PAeq.target_axiom_witness PA194PAeq.targetFixedTheory _ symm_mem

theorem trans_witness :
    Proof PA194PAeq.targetFixedTheory
      (Bootstrapping.axm {⌜PA194PAeq.transitivity.univCl⌝} ⌜PA194PAeq.transitivity.univCl⌝ : V)
      (formulaCode 0 (⌜Theory.Eq.trans ℒₒᵣ⌝ : V)) := by
  rw [trans_translation]
  exact PA194PAeq.target_axiom_witness PA194PAeq.targetFixedTheory _ trans_mem

#print axioms symm_formula
#print axioms arithmetic_symm_mem
#print axioms arithmetic_trans_mem
#print axioms symm_translation
#print axioms trans_formula
#print axioms trans_translation
#print axioms symm_witness
#print axioms trans_witness
end PA194PAeqEqualitySource
