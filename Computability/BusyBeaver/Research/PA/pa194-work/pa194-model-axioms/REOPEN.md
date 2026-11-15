# Reopening internal source proofs

The section assumes a nonempty model `M` of the candidate PRA theory and IΣ₁ for its induced ordered-ring arithmetic, and an `InternalTheory M SourceL` (an arbitrary source theory with Foundation's uniform Δ₁ definition). The property and closure length are **model elements**, so these results apply to nonstandard codes and nonstandard closure lengths, provided the explicitly stated model-internal well-formedness and theory-membership hypotheses hold.

* `reopenProof` constructs an actual Foundation internal proof of a valid formula p from an internal proof of `closeOne p`: it shifts the universal proof, specializes at free variable 0, and uses `bindFormula_scope_open` to identify the result with p. It is a Lean function between proof structures; this theorem does not establish a uniform model-definable graph for that function.
* `reopen_provable` is its existential provability consequence.
* `reopen_iterated_provable` shows, via the model's Σ₁ induction, that `Provable T.theory (modelClose n p)` implies `Provable T.theory p` for any model-valued n. The induction predicate is model-definable; the conclusion is existence of an internal code, not a supplied uniform proof-code transformer.
* `separation_root_provable` applies this to `sepRoot p`: if p is internally valid and `fullyClosedSeparation p` is in the internal Δ₁-class of T, the unclosed separation root has an internal T-proof. The membership premise is essential; the result does not assert it for an arbitrary theory.

The replay uses the prior source-replayed inverse binding (`/dev/shm/pa194-general-separation-replay`), closure/history (`/dev/shm/pa194-model-closure-replay` and its closure-definability dependency), and full-separation closure (`/dev/shm/pa194-fully-closed-replay`) artifacts, plus the explicitly named Foundation and candidate PRA dependencies in `check-reopen.sh`. It checks hashes for the new source and three prerequisite oleans. The transitive dependencies are prebuilt; this add-on does not replay them from source.

Run `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-reopen.sh "$REPO" FRESH_OUTPUT`; the passing output is `/dev/shm/pa194-reopen-proof-replay` and log `/tmp/pa194-reopen-proof-replay.log`. All four printed axiom reports exclude `sorryAx`.

These are model-level proof-existence and single-step proof-structure results. They do not supply the general ordinal-induction proof, translate arbitrary PA proof codes, or establish a native iPRA consistency implication.
