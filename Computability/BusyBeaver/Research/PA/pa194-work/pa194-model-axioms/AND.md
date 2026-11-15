# Uniform contextual conjunction proof code

`contextAndGraph` is one fixed parameter-free Σ₁ arithmetic formula defining the explicit function `contextAndCode p q g dp dq` in every covered candidate-PRA + induced-IΣ₁ model. It composes the internal conjunction, set insertion, weakening, and conjunction-introduction code graphs.

For an arbitrary internal Δ₁ source theory, well-formed internal formulas p and q, internal sequent Γ, and actual derivations of p and q under Γ, `contextAndProof` constructs an actual derivation of p ∧ q under Γ. `contextAndProof_val` proves the output is definitionally the code computed by the fixed graph. The formulas, Γ, and input proof codes may be nonstandard model elements.

This supplies one contextual proof operation needed by the arbitrary-property ordinal induction construction. It does not supply the main induction sequent, all required rule graphs, a general PA proof compiler, or a native iPRA theorem.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-context-and.sh "$REPO" FRESH_OUTPUT` to recompile against the repository-replayed contextual-shift object and prebuilt transitive overlays listed in the checker. It checks source and immediate dependency hashes and three axiom reports. Passing output `/dev/shm/pa194-context-conjunction-code-replay`; log `/tmp/pa194-context-conjunction-code-replay.log`.
