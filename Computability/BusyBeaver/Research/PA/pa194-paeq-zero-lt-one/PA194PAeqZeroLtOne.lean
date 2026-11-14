import PA194PAeqNDSingle
import PA194PAeqQuoteProof
import PA194PAeqTargetAxiom
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unnecessarySeqFocus false
namespace PA194PAeq.ZeroLtOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194PAeqTermBlueprint

macro "targetSyntax" : tactic => `(tactic|
  repeat' first
    | rfl
    | (change @Semiformula.rel language Nat 0 2 Rel.eq _ = @Semiformula.rel language Nat 0 2 Rel.eq _;
        apply congrArg (@Semiformula.rel language Nat 0 2 Rel.eq))
    | (change @Semiterm.func language Nat 0 0 Func.zero _ = @Semiterm.func language Nat 0 0 Func.zero _;
        apply congrArg (@Semiterm.func language Nat 0 0 Func.zero))
    | (change @Semiterm.func language Nat 0 1 Func.succ _ = @Semiterm.func language Nat 0 1 Func.succ _;
        apply congrArg (@Semiterm.func language Nat 0 1 Func.succ))
    | (change @Semiterm.func language Nat 0 2 Func.add _ = @Semiterm.func language Nat 0 2 Func.add _;
        apply congrArg (@Semiterm.func language Nat 0 2 Func.add))
    | (funext i; fin_cases i))

noncomputable def addZeroAtOne : ND.Proof [addZero] (eq (add zero (succ zero)) (succ zero)) := by
  have h : ND.Proof [addZero] addZero := ND.assumption (by simp)
  have e := ND.allElim _ (succ zero) h
  convert e using 1 <;> dsimp [addZero] <;> targetSyntax

noncomputable def zeroLtOneCertificate : ND.Proof [addZero] (less zero (succ zero)) := by
  unfold less
  apply ND.exsIntro _ zero
  convert addZeroAtOne using 1 <;> targetSyntax

def zeroLtOneSentence : Sentence language := (less zero (succ zero)).univCl

theorem zeroLtOne_coe : (zeroLtOneSentence : Proposition language) = less zero (succ zero) := by
  unfold zeroLtOneSentence
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

theorem addZero_coe : (addZero.univCl : Proposition language) = addZero := by
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ (by decide)

noncomputable def zeroLtOneProof : targetFixedTheory.Proof zeroLtOneSentence := by
  apply ND.singleTheoryProof (φ := addZero.univCl)
  · simpa only [addZero_coe,zeroLtOne_coe] using zeroLtOneCertificate
  · change addZero.univCl ∈ targetFixedSentences
    exact List.mem_map.mpr ⟨_, by simp [fixedAxioms], rfl⟩

theorem zeroLtOne_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.zeroLtOne : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb zeroLtOneSentence : Semiproposition language 0) := by
  change PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.zeroLtOne : ArithmeticSemiformula ℕ 0) =
    (zeroLtOneSentence : Proposition language)
  rw [zeroLtOne_coe]
  rfl

theorem source_zeroLtOne_mem : PeanoMinus.Axiom.zeroLtOne ∈ PeanoMinus := PeanoMinus.zeroLtOne

#print axioms addZeroAtOne
#print axioms zeroLtOneCertificate
#print axioms zeroLtOneProof
#print axioms zeroLtOne_formula
#print axioms source_zeroLtOne_mem
end PA194PAeq.ZeroLtOne
