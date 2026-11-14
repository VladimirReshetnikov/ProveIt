import PA194PAeqNDSingle
import PA194PAeqQuoteProof
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
set_option synthInstance.maxHeartbeats 2000
namespace PA194PAeq.ZeroCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

noncomputable def zeroRefl : ND.Proof [reflexivity] (eq zero zero) := by
  have h : ND.Proof [reflexivity] reflexivity := ND.assumption (by simp)
  have e := ND.allElim _ zero h
  convert e using 1
  change @Semiformula.rel language Nat 0 2 Rel.eq _ = @Semiformula.rel language Nat 0 2 Rel.eq _
  apply congrArg (@Semiformula.rel language Nat 0 2 Rel.eq)
  funext i; fin_cases i <;> rfl

def zeroExtSentence : Sentence language :=
  (implies (⊤ : Proposition language) (eq zero zero)).univCl

theorem zeroExt_closed : (implies (⊤ : Proposition language) (eq zero zero)).freeVariables = ∅ := by decide

theorem zeroExt_coe : (zeroExtSentence : Proposition language) = implies ⊤ (eq zero zero) := by
  unfold zeroExtSentence
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ zeroExt_closed

theorem refl_coe : (reflexivity.univCl : Proposition language) = reflexivity := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

noncomputable def zeroExtCertificate : ND.Proof [reflexivity] (implies ⊤ (eq zero zero)) := by
  change ND.Proof [reflexivity] ((∼(⊤ : Proposition language)) ⋎ (eq zero zero))
  exact ND.orRight zeroRefl

noncomputable def zeroExtProof : targetFixedTheory.Proof zeroExtSentence := by
  apply ND.singleTheoryProof (φ := reflexivity.univCl)
  · simpa only [refl_coe,zeroExt_coe] using zeroExtCertificate
  · change reflexivity.univCl ∈ targetFixedSentences
    exact List.mem_map.mpr ⟨_, by simp [fixedAxioms], rfl⟩

theorem zeroExt_formula : PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt Language.ORing.Func.zero) : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb zeroExtSentence : Semiproposition language 0) := by
  change PA194PAeq.formula
    (Rewriting.emb (Theory.Eq.funcExt Language.ORing.Func.zero) : ArithmeticSemiformula ℕ 0) =
    (zeroExtSentence : Proposition language)
  rw [zeroExt_coe]
  rfl

theorem source_zeroExt_mem : Theory.Eq.funcExt Language.ORing.Func.zero ∈ PeanoMinus :=
  PeanoMinus.equal _ (Theory.eqAxiom.funcExt _)

#print axioms zeroExtProof
#print axioms zeroExt_formula
#print axioms source_zeroExt_mem

#print axioms zeroRefl
end PA194PAeq.ZeroCongruence
