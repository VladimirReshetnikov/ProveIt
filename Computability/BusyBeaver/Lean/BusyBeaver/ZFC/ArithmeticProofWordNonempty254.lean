import BusyBeaver.ZFC.ArithmeticProofWord254

/-!
All-internal shifted-word positivity and the exact public invalidity gate.
The proofs use append's checked internal zero law and fixed shifted cons
constructors. They require neither validator acceptance nor standardness of
the proof code. No internal execution or consistency endpoint is asserted.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandAppend254 ArithmeticCommandBlocks254
open ArithmeticProofWordRow254 ArithmeticProofWord254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma consMp_ne_zero (x rest : Circuit) (a b c u : V) :
    (Circuit.consMp x rest).eval a b c u ≠ 0 := by
  simp [Circuit.consMp, Circuit.eval]

lemma consDrop_ne_zero (x rest : Circuit) (a b c u : V) :
    (Circuit.consDrop x rest).eval a b c u ≠ 0 := by
  simp [Circuit.consDrop, Circuit.eval]

lemma consAx_ne_zero (i x y z rest : Circuit) (a b c u : V) :
    (Circuit.consAx i x y z rest).eval a b c u ≠ 0 := by
  simp [Circuit.consAx, Circuit.eval]

lemma discard_ne_zero (a b c u : V) : Circuit.discard.eval a b c u ≠ 0 :=
  consMp_ne_zero _ _ a b c u

lemma leaf_ne_zero (j : Nat) (x y z w : Circuit) (a b c u : V) :
    (Circuit.leaf j x y z w).eval a b c u ≠ 0 := by
  intro h
  exact discard_ne_zero a b c u
    ((appendValue_eq_zero _ _).mp h).1

lemma bundle_ne_zero (x y z : Circuit) (a b c u : V) :
    (Circuit.bundleLeaf x y z).eval a b c u ≠ 0 := by
  intro h
  exact discard_ne_zero a b c u ((appendValue_eq_zero _ _).mp h).1

lemma gen_ne_zero (i p : Circuit) (a b c u : V) :
    (Circuit.genBlock i p).eval a b c u ≠ 0 := by
  intro h
  exact consDrop_ne_zero _ _ a b c u ((appendValue_eq_zero _ _).mp h).2

lemma mp_ne_zero (b p q : Circuit) (a d c u : V) :
    (Circuit.mpBlock b p q).eval a d c u ≠ 0 := by
  intro h
  exact consDrop_ne_zero _ _ a d c u ((appendValue_eq_zero _ _).mp h).2

lemma rowValue_ne_zero (tag payload u v : V) (ht : tag < 12) :
    rowValue tag payload u v ≠ 0 := by
  have htn : tag < ORingStructure.numeral 12 := by simpa [numeral_eq_natCast] using ht
  obtain ⟨i, rfl⟩ := lt_numeral_iff.mp htn
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 ∨
      i.val = 9 ∨ i.val = 10 ∨ i.val = 11 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    simp [numeral_eq_natCast, h, rowValue, mpCircuit, genCircuit, bundleCircuit,
      Circuit.leaf1, Circuit.leaf2, Circuit.leaf3, Circuit.leaf4,
      Circuit.leaf5, Circuit.leaf6, Circuit.leaf7, Circuit.leaf8,
      discard_ne_zero, mp_ne_zero, gen_ne_zero, leaf_ne_zero, bundle_ne_zero]

lemma rawWord_succ_ne_zero (raw : V) : rawWord (raw+1) ≠ 0 := by
  rw [rawWord_succ]
  exact rowValue_ne_zero _ _ _ _ (mod_lt raw (by simp))

theorem rawWord_eq_zero (code : V) : rawWord code = 0 ↔ code = 0 := by
  rcases zero_or_succ code with (rfl | ⟨raw, rfl⟩)
  · simp
  · simp [rawWord_succ_ne_zero]

theorem compiledWord_eq_zero (code : V) :
    compiledWord code = 0 ↔ ArithmeticHistory254.value code = 0 := by
  classical
  by_cases h : ArithmeticHistory254.value code = 0
  · simp [compiledWord, h]
  · have hc : code ≠ 0 := by
      intro hz
      subst code
      exact h (by simp)
    simp [compiledWord, h, rawWord_eq_zero, hc]

end SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254
