# Source and claim audit

Date: 10 October 2026.

## Observed repository reference

`dcd95baeb7c0e914b138bddef6829c5b1d52b726`

This is an observed reference, not a claim that every inspected response was fetched by that pinned SHA. The earlier reads used the repository default branch. Individual observed blob hashes are recorded below so that the relevant snapshots can be located.

| Source | Inspected scope | Observed blob SHA |
|---|---|---|
| `Analysis/Polylogarithms/docs/manuscript/polylogarithms.tex` | entry file and editorial conventions | `bbe0cc54da7520e0b41ab44c5d8679d3713e6cf8` |
| `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex` | first 240 source lines; Hurwitz/log-gamma and Stieltjes context | not retained |
| `Analysis/Polylogarithms/docs/manuscript/chapters/10-discovery.tex` | first 240 source lines; surviving research programme | `207c719ae6e7fb1639401f449216ae9b695afd40` |
| `docs/incoming/README.md` | first 100 source lines; delivery/intake scope | `9956ad83c5ddfa3c75e5f2946481a83082bc81e8` |
| `docs/incoming/` | six-archive inventory | directory API response |

## Direct antecedent

A Library copy named `Coincident_Point_Stieltjes_Calculus.tex` was inspected through the Files connector:

- file ID: `file_00000000ba4482308eb2a3d1ad56166a`, version 1;
- inspected source ranges: 80–379, 430–579, 743–862;
- relevant contents: definitions, periodic/source-variable normalization, scalar product kernel, all-index common-point completion, separated correlation, off-point collision expansion, and the explicit remaining distributional question.

The incoming archive `ProveIt_Coincident_Stieltjes_2026-10-10.zip` was separately observed with Git blob SHA `5507ddd612487e1602424061e2424f56681201c6`. The archive's binary contents were not compared with the Library source. Byte identity of these two routes is not asserted. The present delivery uses the actual equations read from the Library source and reconstructs the needed arguments self-containedly.

## Other observed incoming archives: inventory only

- Dougall Resonance: `e91c0904b720f01e38daf4c57d631e73f8de7255`.
- Endpoint Regularization: `1ac57775cfb4c9e450785e5093fbd570e37f45ac`.
- Exact Identities: `73b03ef745325f93adaef30e19cf6b565cf0fcf5`.
- Resonance Coordinate Transport: `3c8fa393b8f10534507b3a1561f11cfe04153457`.
- Twisted Stieltjes Harmonic Laurent: `ac867b08f88d59ffdd935e6d3a0b0545662fecb4`.

No mathematical audit or non-overlap claim is made for their contents.

## Attribution

The standard Hurwitz shift, derivative, Fourier and special-value identities are sourced to DLMF 25.11; gamma expansions to DLMF 5.7; polylogarithm conventions to DLMF 25.12. Espinosa and Moll's 2002 Hurwitz-integral paper is credited for the classical product-kernel context. Coffey's arXiv:0905.1111 is cited for the established Stieltjes-series literature. Public metadata and official reference pages were checked; this is not an exhaustive literature-priority search.

## Claim boundary

The specific completion is the fixed-convention comparison of two periodic distribution constructions and its all-index coefficient formula. The prior report explicitly left this comparison open. No false theorem was identified in the inspected preceding material. The correction examples concern tempting but invalid extensions: dropping delta terms, commuting coordinate finite parts with differentiation, or replacing Abel-limit distributions by pointwise rational polylogarithms.

The proofs are ordinary mathematics, with finite symbolic and floating-point diagnostics. They have not undergone independent peer review or proof-assistant formalization. The global novelty of every formula is not established. No repository write occurred.
