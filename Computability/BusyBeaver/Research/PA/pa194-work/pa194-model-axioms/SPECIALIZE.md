# Uniform contextual universal-specialization proof code

`contextSpecializeGraph` is one fixed parameter-free Σ₁ arithmetic formula defining the explicit function `contextSpecializeCode p t g d` in every covered candidate-PRA model whose induced ordered-ring arithmetic satisfies IΣ₁. It composes internal substitution, negation, quantifier, insertion, excluded-middle, existential-introduction, weakening, and cut code graphs.

For any internal Δ₁ source theory, well-formed arity-one internal formula p, internal term t, internal sequent Γ, and an actual derivation of ∀p under Γ, `contextSpecializeProof` constructs an actual derivation of p[t] under Γ. `contextSpecializeProof_val` proves the output code is definitionally the graph output. Formula, term, context, and input proof codes may be nonstandard model elements.

This is one contextual proof operation needed to make arbitrary-property induction-base and step applications uniform. It does not establish the main ordinal-induction sequent, a complete PA proof-code compiler, or a native iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-specialize.sh "$REPO" FRESH_OUTPUT` to recompile this source against the repository-replayed contextual-modus-ponens object and prebuilt transitive overlays listed in the checker. It verifies source and immediate dependency hashes and three axiom reports. Passing output `/dev/shm/pa194-context-specialize-code-replay`; log `/tmp/pa194-context-specialize-code-replay.log`.
