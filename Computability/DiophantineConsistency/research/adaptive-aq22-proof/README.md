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

An exploratory single-thread development run against the single-author AQ26
provider in `/tmp/ipra-standard-aq26-combined-author-trial` compiled all of
`AdaptiveAQ22Literal`, `AdaptiveAQ22Zeros`, `AdaptiveAQ22Maps`,
`AdaptiveAQ22Transport`, `AdaptiveAQ22`, `IPRAAQ22Native`, and
`IPRAStandardAQ22`. Each module was compiled in a separate Lean process, in
that order, with the previous outputs in a fresh overlay and the parent
provider's package overlay. For the transport, model-equivalence, native, and
standard endpoint theorems, `#print axioms` reported `propext`,
`Classical.choice`, and `Quot.sound`, without `sorryAx`. The first transport
attempt failed on two signed-subtraction simplifications; the committed source
contains the successful correction.

The native endpoint derives an object-theory equivalence of the no-zero
sentence with the repository's mapped refutation predicate. The standard
presentation client also derives an equivalence with the embedded
Gödel–Gentzen translation of `FoundationZFCConsistencyNat.sourceSentence`.
That exact translated formula must not be silently identified with an
untranslated Con(ZFC); the required identification depends on the larger
project's interpretation and consistency bridges.

This is an exploratory compilation, **not** a guarded or independently
matched replay: the development overlay does not have the guarded runner's
input, output, and provenance guarantees, and the parent author build has not
yet been matched by its peer. It does not establish a current-source or
unconditional user-facing Con(ZFC) claim. A coherent guarded replay and
independent audit are required before promoting these sources.
