import PAFlexibleOutput.Halting
import PAFlexibleOutput.Provability
import PAFlexibleOutput.Search

/-!
# A divergent program whose every output is possible in a model of `𝗣𝗔`

`flexibleOutput`: there is a program `e` that diverges on every input, such that for every
input `x` and every `o : Option ℕ` there is a model of `𝗣𝗔` in which the value of `e` on input
`x` is `o` (`ValueIn M e x o`): the numeral `n` is the only output if `o = some n`, and there is
no output if `o = none`.

## Proof

Say that `𝗣𝗔` *refutes the value* `y` of a program `c` on an input `x` if it proves the negation
of the value sentence "`y` is the only output of `c` on `x`". The refuted values form a
recursively enumerable relation (`provable_substs_re`), so a partial recursive `f` selects, for
`c` and `x`, some refuted value whenever there is one (`exists_selector`). Kleene's second
recursion theorem gives a program `e` that on input `x` computes `f (e, x)`.

* `e` diverges. An output `m` of `e` on `x` would be a value refuted by `𝗣𝗔`. But `m` would be
  the only real output, so its value sentence would be true in `ℕ`, and `ℕ` is a model of `𝗣𝗔`.
* Hence `𝗣𝗔` refutes no value of `e`, as a refuted value would make the selector, and with it
  `e`, halt. By the completeness theorem every value sentence of `e` has a model, and that model
  computes the value (`models_not_valueGraph`).
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
  obtain ⟨f, hf, hsound, hfind⟩ := exists_selector (provable_substs_re (α := Code) (∼valueGraph))
  obtain ⟨e, he⟩ := Nat.Partrec.Code.fixed_point₂ hf.to₂
  -- An output would be a value refuted by `𝗣𝗔`, but it is the value in `ℕ`.
  have hdiv : ∀ x, Nat.Partrec.Code.eval e x = Part.none := fun x =>
    Part.eq_none_iff.2 fun m hm => models_not_valueGraph.mp
      (models_of_provable (M := ℕ) inferInstance (hsound (e, x) m (congrFun he x ▸ hm)))
      (valueIn_nat.mpr (Part.eq_some_iff.2 hm))
  refine ⟨e, hdiv, fun x o => ?_⟩
  cases o with
  | none => exact ⟨ℕ, inferInstance, inferInstance, valueIn_nat.mpr (hdiv x)⟩
  | some n =>
    by_contra hno
    -- No model has value `n`, so `𝗣𝗔` refutes the value `n`, and the selector halts.
    exact Part.eq_none_iff'.mp (congrFun he x ▸ hdiv x) <| hfind (e, x) n <|
      Arithmetic.complete.{0} 𝗣𝗔 _ fun M _ hM =>
        models_not_valueGraph.mpr fun h => hno ⟨M, inferInstance, hM, h⟩

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
#print axioms exists_partrec_flexibleOutput

end PAFlexibleOutput
