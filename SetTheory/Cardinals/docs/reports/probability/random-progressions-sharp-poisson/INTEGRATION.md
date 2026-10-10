# Integration note

Suggested new research directory:
`Combinatorics/Ramsey/Research/RandomProgressions/SharpPoisson/`.

The archive already uses that relative path. Copy or extract the directory
into a checkout, then run the checks and build from that directory. This
package does not require edits to existing Gowers, quasipolynomial,
van der Waerden, square-difference, or Lean files.

Suggested research-index entry:

> **Random progressions: sharp Poisson asymptotics.** An unrefereed written
> proof of a uniform second-order correction for the longest arithmetic
> progression in a fixed-density Bernoulli subset; a sharp
> Theta((log n)^2/n) error rate with explicit lattice-periodic coefficient;
> exact finite regression code. No Lean formalization or priority
> certification yet.

Keep this under `Research`, not in a catalogue of kernel-verified theorems.
Do not set existing global formalization-status flags based on the Python
checks. Proposed formalization units and their dependencies are documented
in `notes/formalization.md`.

The manuscript takes no theorem from the newly released OpenAI collection
as a black-box premise. The repository references explain topic choice and
context. The historical progression-head and pair-overlap ingredients are
attributed to the inspected primary literature.

The package does not include third-party PDFs, fonts, a vendored proof
assistant, or copied repository source. Apply the destination repository's
contribution and licensing policies during integration.
