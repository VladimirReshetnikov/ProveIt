# Source provenance for Report 296

## Public inventory

The exact thirteen authored source/data files are:

- Report296.tex
- build.py
- README.md
- REPRODUCING.md
- SOURCES.md
- SOURCE_MANIFEST.json
- source_excerpts.json
- companion/__init__.py
- companion/README.md
- companion/exact_checks.py
- companion/certificate.json
- tests/test_build.py
- tests/test_companion.py

A frozen distribution additionally contains Report296.pdf and MANIFEST.sha256, for fifteen archive entries. The detached ZIP hash and replay logs are outside the archive. No earlier report, research notes, complete Lean source tree, environment credentials or build intermediates are required or included.

## Pinned upstream source

Repository: VladimirReshetnikov/ProveIt

Compared source revision:
https://github.com/VladimirReshetnikov/ProveIt/commit/af74fb522c24a6331886b11db76942642a6a0e42

Earlier old-interface introduction:
https://github.com/VladimirReshetnikov/ProveIt/commit/63da31b8ed538ddb575bc6f872470fc0044564b1

The comparison concerns both explicit definitions at the compared revision. Read-only historical cross-checks recorded identical Git blob IDs for five files between the two commits: Proofs13ExplicitFourierThreshold.lean, Proofs18CubicDiscrepancy.lean, Proofs18ExplicitCubicDiscrepancy.lean, Proofs18GeneralIteration.lean and Proofs18ExplicitFiveTerm.lean. This is not an assertion that all transitive dependencies are identical across commits, and the present proof needs no such assertion.

SOURCE_MANIFEST.json lists 34 complete-file identity records: 32 files from the supplied inspected comparison snapshot, plus directly retrieved Definitions.lean and LICENSE. For all 34, the preparation checked the complete raw UTF-8 bytes against the recorded SHA-256 and Git blob SHA-1 (including the Git blob header). The original 32 records came from the connected read-only source retrieval used for the comparison; the added two were retrieved through the connected GitHub read API at the same explicit commit. Full raw files and connector responses are not included in this small public package. The current offline checker therefore cannot recompute or independently authenticate those full-file hashes.

source_excerpts.json contains 48 exact excerpts totaling 133 lines. Each text is copied from the complete source with its original UTF-8 spelling and trailing newline, without ellipses inside an excerpt. Its inclusive line range, commit-specific URL and excerpt_sha256 identify that PARTIAL text. Complete-file identities and partial-excerpt hashes are deliberately separate. Hashes establish byte identity relative to a record, not a trusted signature or authorship.

The excerpts cover HasNatAP, the common polynomial/refinement and quadratic constants, the positive-power threshold, the common Fourier threshold definition, both local parameter families, both cubic starting thresholds, the interval parameter and iteration definitions, both five-term definitions, the complete short natural_five_term_fejer theorem body, and the upstream comment delimiting the existing comparison. Underlying common Fourier/geometric dependency formulas are retained by exact source reference in the article; the analytic argument permits any common finite real value for that branch.

## Source map

All Lean files are under Combinatorics/Ramsey/Lean/GowersSzemeredi/.

- Definitions.lean defines HasNatAP with positive natural-number step
- Section05.lean defines P_k and the squared Weyl starting threshold
- Proofs05Downstream.lean and Proofs18BoundaryRefinement.lean define L_k and B
- Proofs07SimultaneousLinearity.lean, Proofs18QuadraticDiscrepancy.lean and Proofs18QuadraticDichotomy.lean yield b, s and E
- Proofs18CubicCellModels.lean, Proofs18CubicTwistedDiscrepancy.lean and Proofs18CubicDiscrepancy.lean define the old local parameters
- Proofs18FejerCubicParameters.lean defines all corresponding Fejer parameters
- Proofs13ExplicitFourierThreshold.lean is shared verbatim by the old and Fejer odd-square threshold definitions
- Proofs18ExplicitCubicCellModels.lean and Proofs18FejerCubicCellModels.lean give the prime-model maximum with 256 and the factor 12
- Proofs18ExplicitCubicTwistedDiscrepancy.lean and Proofs18FejerCubicTwistedDiscrepancy.lean specialize the local threshold to max(4,E)
- Proofs18ExplicitCubicDiscrepancy.lean and Proofs18FejerCubicDiscrepancy.lean give the final cubic maximum with the phase-refinement power threshold
- Proofs18GeneralIntervalStopping.lean gives alpha=(delta^5/64000)^16 at k=5
- Proofs18GeneralIterationStep.lean, Proofs18GeneralIteration.lean and Proofs18DensityIterationGrowth.lean give S, c, n, A, Q and H
- Proofs18ExplicitFiveTerm.lean and Proofs18FejerFiveTerm.lean are the final two interfaces
- Proofs18FejerCubicImprovement.lean explicitly does not infer the full starting-threshold comparison at that revision

## Verification boundary

Report296.tex supplies the new universal analytic proof. It does not report an independent Lean kernel build. The progression implication is an inspected source statement and short proof application, not a complete independent audit of its imported combinatorial dependencies. No upstream code was run, no toolchain installed, no numerical threshold evaluated, and no source file edited.

This report does not compare with szemerediThreshold(delta,5), the paper's numerical five-term bound, general-length Section16 induction, or the best known bounds in the literature. The only source-status observation is the explicit unformalized full comparison in the pinned comment; no historical unresolvedness claim is made.

## Source license and attribution

The pinned repository license is MIT No Attribution (MIT-0), copyright 2026 ProveIt Contributors. Exact Lean excerpts are attributed to ProveIt Contributors and linked to their originating repository files. This source license statement is about the excerpted upstream material; it does not purport to assign an upstream license to the independent report prose.

Pinned license:
https://github.com/VladimirReshetnikov/ProveIt/blob/af74fb522c24a6331886b11db76942642a6a0e42/LICENSE

MIT No Attribution License

Copyright 2026 ProveIt Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy of this
software and associated documentation files (the "Software"), to deal in the Software
without restriction, including without limitation the rights to use, copy, modify,
merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF
CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR
THE USE OR OTHER DEALINGS IN THE SOFTWARE.

## Builder provenance

The guarded builder and its tests were adapted from frozen Report294. They are package infrastructure, not an upstream Lean dependency or a mathematical dependency on that report. Report296 uses distinct source, output, PDF and archive names. Exact allowlists and tests were updated for thirteen source files and fifteen public archive entries. No files from Reports1 through295 are modified by the build or required for replay.
