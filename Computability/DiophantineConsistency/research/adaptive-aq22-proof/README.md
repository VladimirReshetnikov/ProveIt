# AQ22 native transport: development drafts

**Promoted (3 November 2026).** The Lean files of this directory were copied byte for byte into `Lean/DiophantineConsistency/` and built there against current sources; see the [promotion record](../../reviews/aq22-28-current-source-promotion/README.md). The tree copies are now canonical; the copies here are retained as the audited historical inputs.

This directory develops the 22-positive-variable degree-10 graph in
`../adaptive-square-sums22-degree10/candidate.json`. A historical guarded
author run has compiled the native and standard iPRA endpoints and passed an
independent artifact audit. A later historical pair has matched all 37 added
modules and passed an independent artifact audit. The Lean files
under `draft-src` are not part of the regular Lean source tree.

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

This exploratory compilation is **not** a guarded or independently matched
replay: the development overlay does not have the guarded runner's input,
output, and provenance guarantees. It does not establish a current-source or
unconditional user-facing Con(ZFC) claim. The separately guarded author run
described below has since passed an independent artifact audit, and a later
historical paired run has completed.

`author-additions.json` is a static input for the guarded author-only runner in
`../author-only-extension/run.py`. It lists 37 modules: all 30 additions in the
previous combined AQ26/standard-theory author plan, followed by all seven AQ22
modules. The plan pins all source blobs to commit
`bd19027b68` and records their direct imports and exact requested axiom-report
names. The runner's source-verification routine accepted all 37 pinned blobs,
imports, and report policies. Manifest SHA-256:
`3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df`.

A subsequent guarded run compiled all 37 modules in one fresh author overlay
over the audited AQ29 parent, with the runner reporting `AUTHOR_ONLY_PASS` and
the terminal wrapper observing exit 0. The primary record is
`../../reviews/ipra-aq22-guarded-author/README.md`; its precise historical
scope and limitations apply. The run did not reuse objects from the separate
exploratory AQ26 extension. Its [independent artifact audit](../../reviews/ipra-aq22-guarded-author-independent-audit/README.md)
passed. A later [historical paired run](../../reviews/ipra-aq22-historical-pair-terminal/README.md)
matched the 37-module extension and passed an [independent artifact audit](../../reviews/ipra-aq22-historical-pair-independent-audit/README.md).
