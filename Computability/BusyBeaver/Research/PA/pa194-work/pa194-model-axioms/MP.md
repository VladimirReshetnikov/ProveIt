# Uniform contextual modus ponens proof code

`contextMPGraph` is a fixed parameter-free Σ₁ arithmetic formula defining the explicit function `contextMPCode p q g di dp` in every covered candidate-PRA model with induced arithmetic IΣ₁. It composes source negation, disjunction, conjunction, insertion, weakening, excluded-middle, conjunction-introduction, and cut code graphs.

For any internal Δ₁ source theory, well-formed internal formulas p and q, internal sequent Γ, and actual derivations of p→q and p under Γ, `contextMPProof` constructs an actual derivation of q under Γ. `contextMPProof_val` verifies its code is definitionally the output of the fixed graph. Formula, sequent, and input proof codes may be nonstandard model elements.

This supplies one contextual proof operation needed to make arbitrary-property induction-base and step applications uniform. It does not establish the main ordinal-induction sequent, a complete PA proof-code compiler, or a native iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-mp.sh "$REPO" FRESH_OUTPUT` to recompile this source against the repository-replayed contextual-conjunction object and prebuilt transitive overlays listed in the checker. Source and immediate dependency hashes and three axiom reports are checked. Passing output `/dev/shm/pa194-context-mp-code-replay`; log `/tmp/pa194-context-mp-code-replay.log`.
