# Proposed integration into ProveIt

This package is an **AI-assisted analytic contribution** prepared against commit
`c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4` (2026-10-11 00:52:39 UTC).
It supplies conventional analytic and algebraic proofs, exact finite symbolic
checks, and independent numerical diagnostics. It is not a proof-assistant
formalization or a claim of external peer review. The repository owner's name
does not imply authorship of this contribution. Statements about new results
are relative to the inspected source snapshot; global priority is not asserted.

## Placement and dependencies

The standalone article and ZIP can first be registered in `docs/incoming/`.
The following canonical destinations are proposals, not changes already made.
All chapter paths below are relative to
`Analysis/Polylogarithms/docs/manuscript/`.

| Package module | Proposed canonical destination | Dependencies to retain |
| --- | --- | --- |
| `sections/02_harmonic_parity.tex` | New `chapters/07-centered-harmonic-parity.tex` | Existing harmonic Dirichlet continuation and Bernoulli asymptotics; the formal case of Adamczewski–Dreyfus–Hardouin Theorem 1.2. |
| `sections/03_resolvent.tex` | New `chapters/08-stieltjes-resolvents.tex`, beside the existing Stieltjes contact chapters | Hurwitz Fourier continuation, the original-coordinate finite-part convention, classical Espinosa–Moll generalized polygamma and balanced primitives, and the Vardi Barnes identity. |
| `sections/04_harmonic_reduction.tex` | New `chapters/07-relative-harmonic-elimination.tex` | The entire relative harmonic interpolant from the incoming Independent Orders material, including its deconcatenation definition; classical Bernoulli and Lerch identities. |
| `sections/05_tornheim.tex` | New `chapters/07-tornheim-higher-directions.tex`, following `07-tornheim-evaluation.tex` | The exact polar remainder and its axis/Euler-plane identities from Independent Orders; retain those definitions and citations even if their original report has not yet been integrated. |

The numbered filenames are organizational suggestions. Import the required
definitions before adding cross-references, reconcile theorem environments and
macros with the canonical preamble, and add each new chapter to the manuscript
entry point. Preserve the package label prefixes `ghp:`, `res:`, `harm:`, and
`qtr:`. The exact claim-to-label mapping is in `CLAIM_LEDGER.json`.
The modular sources and bibliography are the integration sources; the flattened
TeX is a standalone deliverable, not a second chapter to include concurrently.

## New results and inherited material

The main additions are the necessary-and-sufficient centered harmonic parity
criterion; all centered trigamma-square even moments and their polylogarithmic
generator; the all-index Stieltjes resolvent with its complete endpoint
correction; continuous-order and balanced-primitive resolvents; arbitrary-depth
nonpositive-index elimination and its Lerch generator; and the quartic and
all-order formal Tornheim relation analysis.

Several inputs and consequences must retain their existing attribution:

- The polynomial Hurwitz/Stieltjes primitive mechanism in the harmonic module
  is a normalized restatement and endpoint extension of the canonical
  `07-integration.tex` material, especially `stieltjes:sec:moments`,
  `stieltjes:thm:transform`, and `stieltjes:thm:moment`, and of Espinosa–Moll's
  *On Some Integrals Involving the Hurwitz Zeta Function: Part 2*. Integrate it
  by cross-reference or as an explicitly normalized corollary.
- The Tornheim polar normalization, axis identities, Euler-plane relation,
  and general boundary Gamma-moment representation are inherited inputs.
  The displayed coordinate `U` specializes that existing representation.
- The value of the zeroth trigamma-square moment, `3 zeta(3)`, is classical.
  The incoming Mixed Spectral Identities theorem `dg:square` treats a different
  weighted square of shifted trigamma differences and should still be cited.
- The Espinosa–Moll and Barnes function definitions, and the Cauchy jump
  inversion, remain classical. The new claim concerns the stated resolvent
  families and their exact endpoint completion.

## Existing statuses to preserve

Keep S4 proved and retain its labels `s4proof:thm:s4`, `gaussian:thm:S4`, and the
historical compatibility alias `gaussian:conj:S4`.

Keep the current S6 candidate (`cycloquot:conj:S6`, `cycloquot:eq:S6`)
**conjectural**. Keep the revised S8 candidate (`s8new:conj:S8`,
`s8new:eq:formula`) **conjectural**. The earlier vector rejected under
`research:prop:S8-rejected` is distinct; its rejection must not be transferred
to the revised vector.

The inherited Cayley obstruction concerns its specified relation family.
The interrupted larger modular search is not an exhaustive rank or
nonmembership certificate. Neither supplies nonvanishing of an actual
numerical period. This package proves neither S6 nor the revised S8 and does
not change their status.

## Scope that must survive editing

The centered parity classification uses formal-series injectivity, not
arithmetic independence of numerical constants. Tornheim coordinate dimensions
and the fifth-order diagonal obstruction are relative to the explicitly named
symmetry, axis, and Euler-plane relations; they are not minimality or period
independence theorems modulo every possible identity.

The resolvent finite part uses the original endpoint coordinate `x`. Preserve
the full contact polynomial and the distinction between continued complex
order and pointwise integer-order finite parts. Rational closure is for
rational functions bounded at infinity with no real pole. The harmonic
elimination permits differentiation in surviving free orders, but does not
permit transverse differentiation of an index fixed at a nonpositive integer.
Individual cyclic Tornheim restrictions require the stated nonzero pairwise
direction sums, even though the completed cyclic germ has a larger domain.

## Reproducibility and review artifacts

`provenance/SOURCE_SNAPSHOT.json` records the pinned commit, all nine inspected
incoming archive hashes, and actual SHA256 and Git blob identifiers for the
selected canonical sources. `provenance/source_archives.json` preserves the
original archive manifest. No source archive, source PDF, or large source tree
has been copied into the package.

`provenance/VERIFICATION_RECORDS.json` maps the final verification programs to
their recorded outputs and checksums. Finite exact checks support the algebra;
the TeX proofs establish the infinite families. Floating-point checks have the
precisions and qualifications stated in the result files and are not interval
certificates. Rebuild and rerun instructions belong to the package README and
verification section.

`provenance/reviews/` contains independent targeted reviews of the harmonic
reduction, parity classification, and resolvent arguments. The source audit is
recorded in `provenance/source_audit.txt`. Preserve these scope statements with
the mathematical content, and update metadata if formulas, labels, or checked
programs are changed during integration.
