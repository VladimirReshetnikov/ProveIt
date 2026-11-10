import Mathlib.Computability.PartrecCode

/-!
# Assembly using Mathlib's actual Kleene recursion theorem

Unlike `ProofCore.lean`, this file does not assume the existence of a
self-referential program. It obtains a code by applying the existing theorem

  Nat.Partrec.Code.fixed_point₂

to an explicitly supplied partial-recursive proof-search operation.

What remains to implement for PA is deliberately visible:
* the arithmetical halting sentences and their finite-computation verification;
* consistency and the first-order completeness bridge;
* a uniform partial-recursive search through PA proofs, with its two elementary
  search specifications.

The search implementation is a parameter, not an axiom or an unfinished
proof. This file is therefore a conditional assembly theorem, not a completed
formalization of the concrete PA endpoint.

API inspection: `fixed_point₂` and `eval_part` were checked against
`Mathlib/Computability/PartrecCode.lean` at the Mathlib revision pinned by the
inspected ProveIt checkout. Validation status: source-reviewed, not locally
compiler-checked (the authoring environment had no Lean executable).
-/

namespace FlexibleOutputMathlib

universe u v

abbrev Code := Nat.Partrec.Code

/-- The arithmetic/logic bridge to be instantiated for first-order PA. -/
structure ArithmeticBridge where
  Sentence : Type u
  Model : Type v
  halts : Code → ℕ → ℕ → Sentence
  neg : Sentence → Sentence
  provable : Sentence → Prop
  isModel : Model → Prop
  realizes : Model → Sentence → Prop
  consistent : ∀ p, provable p → provable (neg p) → False
  finiteComputation : ∀ {e : Code} {x y : ℕ},
    y ∈ Nat.Partrec.Code.eval e x → provable (halts e x y)
  modelOfUnrefuted : ∀ p,
    (¬ provable (neg p)) → ∃ M, isModel M ∧ realizes M p

/--
The non-self-referential search operation. For a supplied code `c`, ignore
the ordinary input and enumerate proofs until finding one of
`¬ halts c 0 y`; return that `y`.

No fixed-point assumption appears here. The search takes the code to mention
as an ordinary parameter, so its effectivity is a direct composition of
proof enumeration, syntax construction, and unbounded search.
-/
structure SearchImplementation (A : ArithmeticBridge.{u, v}) where
  search : Code → ℕ →. ℕ
  partialRecursive : Partrec₂ search
  ignoresInput : ∀ c x, search c x = search c 0
  returnsRefutation : ∀ {c : Code} {x y : ℕ},
    y ∈ search c x → A.provable (A.neg (A.halts c 0 y))
  findsRefutation : ∀ {c : Code},
    (∃ n, A.provable (A.neg (A.halts c 0 n))) →
      ∃ m, m ∈ search c 0

variable {A : ArithmeticBridge.{u, v}}

/--
Kleene self-reference plus consistency gives a standard nowhere-defined
partial recursive program with every standard output possible in a model.

The output obtained from `findsRefutation` is allowed to be different from
the number in the proof that triggered the existence argument. This is
essential: proof search returns the first accepted proof.
-/
theorem exists_program_with_arbitrary_possible_output
    (S : SearchImplementation A) :
    ∃ e : Code,
      Partrec (Nat.Partrec.Code.eval e) ∧
      (∀ x y, ¬ y ∈ Nat.Partrec.Code.eval e x) ∧
      (∀ n, ∃ M, A.isModel M ∧ A.realizes M (A.halts e 0 n)) := by
  obtain ⟨e, he⟩ := Nat.Partrec.Code.fixed_point₂ S.partialRecursive
  -- `he : eval e = S.search e` is equality of actual partial functions.
  have noHalt : ∀ y, ¬ y ∈ Nat.Partrec.Code.eval e 0 := by
    intro y hy
    have hs : y ∈ S.search e 0 := by
      rw [← he]
      exact hy
    exact A.consistent (A.halts e 0 y)
      (A.finiteComputation hy) (S.returnsRefutation hs)
  have noRefutation : ∀ n,
      ¬ A.provable (A.neg (A.halts e 0 n)) := by
    intro n hn
    obtain ⟨m, hm⟩ := S.findsRefutation (Exists.intro n hn)
    apply noHalt m
    rw [he]
    exact hm
  refine ⟨e, ?_, ?_, ?_⟩
  · exact Nat.Partrec.Code.eval_part.comp (Computable.const e) Computable.id
  · intro x y hy
    have hx : Nat.Partrec.Code.eval e x = Nat.Partrec.Code.eval e 0 :=
      (congrFun he x).trans
        ((S.ignoresInput e x).trans (congrFun he 0).symm)
    apply noHalt y
    rw [← hx]
    exact hy
  · intro n
    exact A.modelOfUnrefuted (A.halts e 0 n) (noRefutation n)

/-- The same conclusion with the external partial function explicitly named. -/
theorem exists_partial_function_with_arbitrary_possible_output
    (S : SearchImplementation A) :
    ∃ (f : ℕ →. ℕ) (e : Code),
      f = Nat.Partrec.Code.eval e ∧
      Partrec f ∧
      (∀ x y, ¬ y ∈ f x) ∧
      (∀ n, ∃ M, A.isModel M ∧ A.realizes M (A.halts e 0 n)) := by
  obtain ⟨e, hrec, hdiv, hmodels⟩ :=
    exists_program_with_arbitrary_possible_output S
  exact ⟨Nat.Partrec.Code.eval e, e, rfl, hrec, hdiv, hmodels⟩

#print axioms exists_program_with_arbitrary_possible_output
#print axioms exists_partial_function_with_arbitrary_possible_output

end FlexibleOutputMathlib
