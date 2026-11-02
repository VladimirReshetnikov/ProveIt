# AQ22 native transport: development drafts

This directory develops the 22-positive-variable degree-10 graph in
`../adaptive-square-sums22-degree10/candidate.json`. It is a candidate, not a
completed native PRA proof and not an independently replayed proof. The Lean
files under `draft-src` are not part of the regular Lean source tree.

`generate_model.py` derives the literal and 13-residual sum-of-squares draft
from the SHA-256-pinned candidate and the pinned AQ29 zero-decomposition
template. `check_literal.py` separately compares the complete sequence of
witnesses, ports, and all 114 operations in the Lean literal against that pinned
candidate. This is a spelling check, not a semantic equivalence proof. An
intentional `q := 2 + qm` mutation was rejected by the check.

The proposed reduction projects the AQ26 witness by removing coordinates
`c`, `qSquare`, `X*Y`, and `Q`. It reconstructs the first three using the
candidate's defining expressions and reconstructs `Q` as `(cSquare*i)^2`.
That last choice is positive under the positive-witness hypothesis. The
retained `g72` residual should identify the reconstructed value with
`delta*(f*f-1)` using signed-pair evaluation; this matters because subtracting
one directly in a model of natural arithmetic may truncate. The proposed
`extend_inputs`, `project_inputs`, and zero-transport theorems are intended to
check this in Lean, rather than assume it from the graph manipulation.

An exploratory single-thread development run against one previously
source-built author AQ26 provider compiled `AdaptiveAQ22Literal`,
`AdaptiveAQ22Zeros`, and `AdaptiveAQ22Maps`, including the positivity proof.
This is not an independently audited replay: the development overlay does not
have the guarded runner's output/provenance guarantees. The transport,
no-zero equivalence, and native endpoint sources remain drafts until compiled
and then replayed against a matched, source-verified dependency chain. No claim
is made that the endpoint or either direction of its equivalence has been
established by these drafts.
