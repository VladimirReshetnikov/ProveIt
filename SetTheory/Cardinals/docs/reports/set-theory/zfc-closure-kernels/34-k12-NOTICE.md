# Attribution and provenance

This package was prepared as a research contribution for the ProveIt
repository in response to Vladimir Reshetnikov's request of 16 October 2026.
The report identifies new local derivations and experiments separately from
existing constructions; it makes no claim of a new 253-state result or a
smaller established ZFC-consistency machine.

## Mathematical provenance

The finite assignment/class proposal adapts Harvey M. Friedman's
*Impossible Counting* (2 September 2017), Sections 4.1–4.2. Its fused
Separation/Collection interfaces, exact 28-clause payload, proof exposition,
and diagnostic reference implementation were developed for this report.
The finite-axiomatization idea itself is prior work. The source bibliography
and the independent mathematical review are included.

The full-ZFC wrapper composes pre-existing upstream theorems. An equivalent
composition is already retained in ProveIt's source20 intake; this package
provides a source-reviewed supplement with explicitly qualified Foundation
and pinned dependencies. It is not a new consistency reduction.

## Machine and software provenance

The public 254-state table is attributed in upstream to Mira-Cult, using the
Wade-style proof-search/compiler lineage with Jeff's Coq development. The
already public 253-state improvement is attributed to mira-emmy and the
upstream contributors. Their sources and CI are pinned in the audit.

The clean compiler modules and the 206/202-node input data are unchanged
copies from the identified ProveIt snapshot. Their original license files
and incoming-source notices are retained under `engineering/vendor/`.
The contiguous initializer and exact-quotient experiments are local work
described in `engineering/notes.md` and `engineering/NOTICE.md`.

Copied third-party files retain their original terms. This top-level notice
does not relicense the vendor snapshot or the original research sources.
Original attribution and source comments should be retained when integrating
the package into ProveIt.

## Verification status

The report, ordinary proofs, executed finite checks, inspected upstream
kernel evidence, and unimplemented formalization/compilation work are
distinguished explicitly. A source-only checker is not a Coq build, a
symbolic control is not a new compiler soundness theorem, and a finite
payload size is not a binary Turing-machine state bound.
