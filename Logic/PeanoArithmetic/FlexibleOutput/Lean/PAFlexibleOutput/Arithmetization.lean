import PAFlexibleOutput.Statement
import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic

/-!
# The halting formula: partial recursiveness, standard semantics and provability

This module discharges four of the obligations named in `PAFlexibleOutput.Statement`:

* `universalEvalPartrec`: the universal evaluator `universalEval` is partial recursive;
* `universalGraphSigmaOne`: the halting formula `universalGraph` is `𝚺₁`;
* `standardCorrectness`: in the standard model, `haltSentence c x y` says exactly
  `y ∈ Nat.Partrec.Code.eval c x`;
* `finiteProofAdequacy`: every real halting computation is verified by `𝗣𝗔`
  (`𝚺₁`-completeness).

It also introduces `divergeSentence c x`, the sentence "program `c` has no output on input `x`",
and reads both sentences in an arbitrary structure.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- The universal evaluator is partial recursive. -/
theorem universalEvalPartrec : UniversalEvalPartrec := by
  have h1 : Computable fun v : List.Vector ℕ 2 =>
      Denumerable.ofNat Nat.Partrec.Code (v.get 0) :=
    (Computable.ofNat Nat.Partrec.Code).comp
      (Computable.vector_get.comp Computable.id (Computable.const 0))
  have h2 : Computable fun v : List.Vector ℕ 2 => v.get 1 :=
    Computable.vector_get.comp Computable.id (Computable.const 1)
  have h : Partrec fun v : List.Vector ℕ 2 =>
      Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code (v.get 0)) (v.get 1) :=
    Nat.Partrec.Code.eval_part.comp h1 h2
  show Nat.Partrec' universalEval
  exact Nat.Partrec'.of_part (h.of_eq fun v => rfl)

/-- The halting formula is `𝚺₁`. -/
theorem universalGraphSigmaOne : UniversalGraphSigmaOne := by
  simp [UniversalGraphSigmaOne, universalGraph, codeOfPartrec']

/-- The halting formula at natural numbers: it holds iff the program really produces that
output. -/
theorem universalGraph_nat (c : Code) (x y : ℕ) :
    (ℕ ⊧/![y, Encodable.encode c, x] universalGraph) ↔ y ∈ Nat.Partrec.Code.eval c x := by
  have h := codeOfPartrec'_spec universalEvalPartrec (y := y) (v := ![Encodable.encode c, x])
  have hc : Nat.Partrec.Code.ofNatCode (Encodable.encode c) = c := Denumerable.ofNat_encode c
  have he : universalEval (List.Vector.ofFn ![Encodable.encode c, x])
      = Nat.Partrec.Code.eval c x := by
    simp [universalEval, hc]
  rw [he] at h
  exact h

/-- Reading of `haltSentence` in an arbitrary structure. -/
theorem models_haltSentence {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (c : Code) (x y : ℕ) :
    (M↓[ℒₒᵣ] ⊧ haltSentence c x y) ↔
      (M ⊧/![(y : M), ((Encodable.encode c : ℕ) : M), (x : M)] universalGraph) := by
  simp [haltSentence, models_iff, Semiformula.eval_substs, numeral_eq_natCast_app]

/-- In the standard model the halting sentence says that the program really halts with the
given output. -/
theorem standardCorrectness : StandardCorrectness := by
  intro c x y
  rw [models_haltSentence]
  simpa using universalGraph_nat c x y

/-- Every halting sentence is `𝚺₁`. -/
theorem haltSentence_sigma_one (c : Code) (x y : ℕ) : Hierarchy 𝚺 1 (haltSentence c x y) := by
  simp [haltSentence, universalGraph, codeOfPartrec']

/-- `𝗣𝗔` verifies every real halting computation. -/
theorem finiteProofAdequacy : FiniteProofAdequacy := fun c x y h =>
  sigma_one_completeness (T := 𝗣𝗔) (haltSentence_sigma_one c x y)
    ((standardCorrectness c x y).mpr h)

/-- The sentence "program `c` has no output on input `x`". -/
noncomputable def divergeSentence (c : Code) (x : ℕ) : ArithmeticSentence :=
  ∼(∃⁰ (universalGraph/[#0, ↑(Encodable.encode c), ↑x] : ArithmeticSemisentence 1))

/-- Reading of `divergeSentence` in an arbitrary structure: no element of the structure is an
output. -/
theorem models_divergeSentence {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (c : Code) (x : ℕ) :
    (M↓[ℒₒᵣ] ⊧ divergeSentence c x) ↔
      ¬ ∃ y : M, (M ⊧/![y, ((Encodable.encode c : ℕ) : M), (x : M)] universalGraph) := by
  simp [divergeSentence, models_iff, Semiformula.eval_substs, numeral_eq_natCast_app]

/-- In the standard model the divergence sentence says that the program really diverges. -/
theorem standardDivergence (c : Code) (x : ℕ) :
    (ℕ↓[ℒₒᵣ] ⊧ divergeSentence c x) ↔ ¬ (Nat.Partrec.Code.eval c x).Dom := by
  rw [models_divergeSentence, Part.dom_iff_mem]
  simp [← universalGraph_nat]

#print axioms universalEvalPartrec
#print axioms standardCorrectness
#print axioms finiteProofAdequacy
#print axioms standardDivergence

end PAFlexibleOutput
