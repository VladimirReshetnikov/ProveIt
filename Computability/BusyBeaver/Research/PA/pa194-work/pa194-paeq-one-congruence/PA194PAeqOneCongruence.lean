import PA194PAeqNDSingle
import PA194PAeqQuoteProof
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option synthInstance.maxHeartbeats 2000
namespace PA194PAeq.OneCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

noncomputable def oneRefl : ND.Proof [reflexivity] (eq (succ zero) (succ zero)) := by
  have h : ND.Proof [reflexivity] reflexivity := ND.assumption (by simp)
  have e := ND.allElim _ (succ zero) h
  convert e using 1
  change @Semiformula.rel language Nat 0 2 Rel.eq _ = @Semiformula.rel language Nat 0 2 Rel.eq _
  apply congrArg (@Semiformula.rel language Nat 0 2 Rel.eq)
  funext i; fin_cases i <;> rfl

def oneExtSentence : Sentence language :=
  (implies (⊤ : Proposition language) (eq (succ zero) (succ zero))).univCl

theorem oneExt_closed : (implies (⊤ : Proposition language) (eq (succ zero) (succ zero))).freeVariables = ∅ := by decide

theorem oneExt_coe : (oneExtSentence : Proposition language) = implies ⊤ (eq (succ zero) (succ zero)) := by
  unfold oneExtSentence
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ oneExt_closed

theorem refl_coe : (reflexivity.univCl : Proposition language) = reflexivity := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

noncomputable def oneExtCertificate : ND.Proof [reflexivity] (implies ⊤ (eq (succ zero) (succ zero))) := by
  change ND.Proof [reflexivity] ((∼(⊤ : Proposition language)) ⋎ (eq (succ zero) (succ zero)))
  exact ND.orRight oneRefl

noncomputable def oneExtProof : targetFixedTheory.Proof oneExtSentence := by
  apply ND.singleTheoryProof (φ := reflexivity.univCl)
  · simpa only [refl_coe,oneExt_coe] using oneExtCertificate
  · change reflexivity.univCl ∈ targetFixedSentences
    exact List.mem_map.mpr ⟨_, by simp [fixedAxioms], rfl⟩

theorem oneExt_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt Language.ORing.Func.one) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb oneExtSentence : Semiproposition language 0) := by
  change PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt Language.ORing.Func.one) : ArithmeticSemiformula ℕ 0) =
    (oneExtSentence : Proposition language)
  rw [oneExt_coe]
  rfl

theorem source_oneExt_mem : Theory.Eq.funcExt Language.ORing.Func.one ∈ PeanoMinus :=
  PeanoMinus.equal _ (Theory.eqAxiom.funcExt _)

#print axioms oneExtProof
#print axioms oneExt_formula
#print axioms source_oneExt_mem

#print axioms oneRefl
end PA194PAeq.OneCongruence
