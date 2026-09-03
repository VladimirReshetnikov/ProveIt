# Corpus audit and non-duplication ledger

## Snapshot

- Repository: `VladimirReshetnikov/ProveIt`
- Requested subtree: `Analysis/FabiusFunction/docs`
- Pinned commit: `90b2d3587833dea1bc4a6bf0c36d92f7200396e6`
- Commit date used by the report: 30 August 2026
- Recursive GitHub code inventory: **119 LaTeX files** under the subtree

The documentation tree mixes current expositions, consolidated frontier
volumes, same-day incoming drafts, source-paper transcriptions, and frozen
historical predecessors. Counting every frozen predecessor as an independent
current claim would substantially overstate coverage. The audit therefore used
the repository's own `MANIFEST.md`, provenance blocks, coverage tables, and
archive relationships to identify canonical descendants.

## Directly inspected canonical descendants

The mathematical bodies, abstracts, scope sections, theorem ledgers, conclusions,
and provenance records of the following current families were inspected directly:

- `Fabius_Function_and_Rvachev_Up/Fabius_Function_and_Rvachev_Up.tex`
- `FabiusFunction_Mathematical_Glossary/` and the Lean walkthrough family
- `semi-formalized-research-frontiers/drafts/MANIFEST.md`
- `.../representations/Representation_Frontiers/Representation_Frontiers.tex`
- `.../spectra-and-arithmetic/Spectra_and_Arithmetic_Frontiers/Spectra_and_Arithmetic_Frontiers.tex`
- `.../exponents-and-q-series/Exponents_and_q_Series_Frontiers/Exponents_and_q_Series_Frontiers.tex`
- the canonical inverse-and-sampling frontier family
- the consolidated Thue–Morse, asymptotic, Fourier-decay, and digital-spectral
  frontier families identified by the manifest
- `.../frontier-compilations/Digital_Spectral_Geometry_and_Log_Periodic_Saddles/`
- `.../frontier-compilations/fabius_information_frontier/fabius_information_frontier.tex`
- the paper-transcription and historical archive lineages needed to verify that
  a result had not merely been moved or renamed

In addition, recursive code searches were run across all indexed LaTeX paths,
not merely the canonical files, so that terminology changes and surviving
historical formulations could be detected.

## Collision searches used before selecting the topic

Searches included exact phrases and close variants in the following families:

| Proposed frontier | Whole-tree collision terms |
|---|---|
| Matrix dilation | `matrix dilation`, `matrix-dilated`, `expansive matrix`, `self-affine matrix Fabius` |
| Convex support | `zonotope`, `zonoid`, `support function`, `rotating support`, `curvature measure` |
| Multivariate splines | `multivariate box spline`, `infinite box spline`, `matrix sinc product` |
| Tensor moment algebra | `tensor cumulant`, `tensor Bell`, `Lyapunov cumulant`, `matrix Appell`, `Kronecker resolvent` |
| Rotating q-series | `abs(sin(n theta))`, `rotation orbit`, `Abel shape`, `natural boundary` |
| Endpoint geometry | `cap distribution`, `support deficit`, `directional inverse Fabius`, `rotation cocycle` |

No definition equivalent to the report's matrix-dilated random series, no
rotating-zonoid area series, no tensor Prouhet derivative cube, and no
matrix-resolvent cumulant formula was found in the pinned corpus. The repository
does contain extensive scalar, base-b, q-deformed, spectral, Appell, Legendre,
and endpoint machinery; those results are treated as imported background rather
than relabeled as new.

## Status discipline

- **[repository input]**: already in the audited corpus or explicitly imported.
- **[proved here]**: proof supplied in the report and no equivalent statement
  located in the pinned repository.
- **[derived synthesis]**: useful recombination of standard ingredients.
- **[conjecture]**: deliberately unproved.
- **[numerical]**: reproducible diagnostic evidence only.

“New” always means *new to this repository snapshot under the displayed
normalization*. It is not an assertion that no equivalent result exists anywhere
in the mathematical literature.
