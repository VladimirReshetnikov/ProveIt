# Canonical dual quantifier wrapper

`PA194CanonicalDualForall.lean` instantiates the previously parameterized
`dualForallCode` with the fixed certified projection codes and the canonical
formula closer. For arbitrary model-valued labels and arbitrary internally
well-formed depth-zero positive and negative arithmetic formula codes,
`canonical_equation` identifies the output with the pair of Foundation's
universal and existential constructors applied to the internal closing
traversal. `canonical_wellformed` proves both output components are internally
well formed at depth zero.

The file also fixes the same closer in the existing `dualQuantTranslation`
source traversal. This is the numerical named-source encoding used by the
PA194 separate-diagonal calculus: its implication and universal constructors
are `4 * pair a b` and `4 * pair body label + 2` in
`PA196.Commands.Code`. It is distinct from Foundation's internal
`M6.PA.RelationalSource` formula coding; relating the two still requires a
syntax and proof translation. `translation_universal` identifies that actual source
universal branch, assuming that its two recursively translated body components
are internally well formed and that the supplied source-tag and child decoder
codes have their respective candidate-PRA certificates. It does not prove
these hypotheses for every source formula, nor full compiler correctness.
All statements apply to nonstandard model elements in every nonempty
candidate-PRA model with an IΣ₁ arithmetic reduct and equality interpreted as
equality. Lean reports `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`, for the printed results. Neither machine/refutation implication is
proved here.

Run `check-canonical-dual-forall.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set; it builds the formula-closing and source
traversal dependencies in a fresh temporary overlay.

An independent fresh Linux replay of `check-canonical-dual-forall.sh` passed
using the audited overlays, rebuilding the local dependency chain and finding
no `sorryAx` in the displayed theorem dependencies.
