import PAFlexibleOutput.Functionality
import PAFlexibleOutput.Refutations
import PAFlexibleOutput.Search

/-!
# A divergent program whose every output is possible in a model of `𝗣𝗔`

`flexibleOutput`: there is a program `e` that diverges on every input, such that for every
input `x` and every `o : Option ℕ` there is a model of `𝗣𝗔` in which the value of `e` on input
`x` is `o` (`ValueIn M e x o`): the numeral `n` is the only output if `o = some n`, and there is
no output if `o = none`.

## Proof

The refuted outputs form a recursively enumerable relation (`refutationsRE`), so a partial
recursive `f` selects, for a program `c` and an input `x`, some `y` such that `𝗣𝗔` proves that
`c` does not halt on `x` with output `y`, whenever there is one (`exists_selector`). Kleene's
second recursion theorem gives a program `e` that on input `x` computes `f (e, x)`.

* `e` diverges. An output `m` of `e` on `x` would be refuted by `𝗣𝗔`, but the halting sentence
  for `m` is true in `ℕ`, and `ℕ` is a model of `𝗣𝗔`.
* Hence no output of `e` is refuted by `𝗣𝗔`, as a refuted output would make the selector, and
  with it `e`, halt. By the completeness theorem every halting sentence of `e` has a model, and
  in that model the output is unique (`valueIn_of_models`).
* `ℕ` is a model in which `e` has no value.
-/

set_option autoImplicit false

namespace PAFlexibleOutput

open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic

/-- **Main theorem.** There is a program `e` that diverges on every input, such that for every
input `x` and every `o`, a natural number or `none`, there is a model of `𝗣𝗔` in which the value
of `e` on input `x` is `o`. -/
theorem flexibleOutput :
    ∃ e : Code, (∀ x, Nat.Partrec.Code.eval e x = Part.none) ∧ ∀ (x : ℕ) (o : Option ℕ),
      ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔), ValueIn M e x o := by
  obtain ⟨f, hf, hsound, hfind⟩ := exists_selector refutationsRE
  obtain ⟨e, he⟩ := Nat.Partrec.Code.fixed_point₂ (f := fun c x => f (c, x)) hf
  replace he : ∀ x, Nat.Partrec.Code.eval e x = f (e, x) := congrFun he
  -- An output would be refuted by `𝗣𝗔`, but it is true in `ℕ`.
  have hdiv : ∀ x m, m ∉ Nat.Partrec.Code.eval e x := fun x m hm =>
    Semantics.Not.models_not.mp
      (models_of_provable (M := ℕ) inferInstance (hsound (e, x) m (he x ▸ hm)))
      ((standardCorrectness e x m).mpr hm)
  refine ⟨e, fun x => Part.eq_none_iff.2 (hdiv x), fun x o => ?_⟩
  cases o with
  | none => exact ⟨ℕ, inferInstance, inferInstance, fun y hy => hdiv x y (outputIn_nat.mp hy)⟩
  | some n =>
    by_contra hno
    -- No model has value `n`, so `𝗣𝗔` refutes the output `n`, and the selector halts.
    have hn : 𝗣𝗔 ⊢ ∼haltSentence e x n := Arithmetic.complete.{0} 𝗣𝗔 _ fun M _ hM =>
      Semantics.Not.models_not.mpr fun h =>
        haveI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) hM
        hno ⟨M, inferInstance, hM, valueIn_of_models h⟩
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (hfind (e, x) n hn)
    exact hdiv x m (he x ▸ hm)

/-- The sentence form: every halting sentence of the program is satisfiable together with
`𝗣𝗔`, although the program diverges. -/
theorem flexibleOutput_satisfiable :
    ∃ e : Code, (∀ x, Nat.Partrec.Code.eval e x = Part.none) ∧
      ∀ x n : ℕ, Satisfiable (insert (haltSentence e x n) 𝗣𝗔) := by
  obtain ⟨e, hdiv, h⟩ := flexibleOutput
  refine ⟨e, hdiv, fun x n => ?_⟩
  obtain ⟨M, _, hM, hn⟩ := h x (some n)
  exact satisfiable_intro M
    (Semantics.ModelsSet.insert_iff.mpr ⟨models_haltSentence.mpr ((hn _).mpr rfl), hM⟩)

/-- The theorem as usually stated: there is a partial recursive function `f : ℕ →. ℕ` such that
for every `o`, a natural number or `none`, the statement "`f 0 = o`" holds in some model of
`𝗣𝗔`. The statement is read inside the model through the halting formula of a program `e` of
`f`. -/
theorem exists_partrec_flexibleOutput :
    ∃ f : ℕ →. ℕ, Partrec f ∧ ∃ e : Code, Nat.Partrec.Code.eval e = f ∧ ∀ o : Option ℕ,
      ∃ (M : Type) (_ : ORingStructure M) (_ : M↓[ℒₒᵣ] ⊧* 𝗣𝗔), ValueIn M e 0 o := by
  obtain ⟨e, -, h⟩ := flexibleOutput
  exact ⟨_, Nat.Partrec.Code.eval_part.comp (.const e) .id, e, rfl, h 0⟩

#print axioms flexibleOutput
#print axioms flexibleOutput_satisfiable
#print axioms exists_partrec_flexibleOutput

end PAFlexibleOutput
