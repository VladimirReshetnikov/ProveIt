# Independent review of the conditional package-65 endpoint

Reviewed source: `P65IPRAHaltReverseAdapter.lean`, SHA-256
`42e1b330c1e8a879c003e0adebd4e20a854e0e9d8e82d0ac8d65feb0a688f962`.
This review did not rerun Lean or rebuild its captured providers.

`ReverseDirection` explicitly assumes, uniformly over every IΣ₁ model,
that a strictly positive internal zero of the fixed-port package-65 output
implies an internal machine-215 halt. The source does not prove this
hypothesis. Its graph expression is definitionally the same fixed-port graph
used by `P65CanonicalHaltConverse.halt_positive_zero`, the independently
reviewed halt-to-positive-zero direction.

The bridge proof handles both directions with the same expression. Given a
halt and the canonical positive tuple, it subtracts one coordinatewise to
obtain a natural zero of `positiveShift expression`; strict positivity proves
the subtraction/addition identity. Conversely, a zero of the shifted expression
gives a positive zero after adding one coordinatewise, to which the explicit
`ReverseDirection` hypothesis is applied. `classicalNoZero_iff` identifies
the semantic nonzero sentence and `internalZero_positiveShift` identifies
the shifted valuation. Thus the bridge has exactly the all-model no-zero versus
no-halt shape required by the generic endpoint theorem.

`native_equivalence`, `standard_equivalence`, and `reference_equivalence`
all retain `h : ReverseDirection` as an explicit hypothesis. They apply the
repository's generic iPRA transfer, standard-theory conversion, and
equality-only conversion, respectively. Their formulas use the repository's
mapped native refutation and negation, with the order-erased versions in the
reference endpoint. I found no mismatch in the expression, shift, implication
directions, or handling of the explicit hypothesis.

The conclusion remains conditional on the unproved all-model reverse
direction and on the captured-provider and source/object provenance boundary;
it is not itself an unconditional equivalence or a PDF correspondence proof.
This source review is not an independent audit of the imported generic iPRA
transfer machinery.
