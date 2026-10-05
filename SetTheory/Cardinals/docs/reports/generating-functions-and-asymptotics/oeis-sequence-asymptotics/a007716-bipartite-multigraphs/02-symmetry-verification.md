# Verification and dependency scope

## Mathematical review

The proof was checked independently against the preceding A007716 report. The new arguments use that report's established weighted asymptotic estimates and exact marked-cycle formulas, as stated explicitly in Section 2. The original source ZIP is included unchanged; its SHA256 is

4c503e6ba487c5182891ff222b841442d949edf4edeac7cd084dc8db996abfeb

The review checked the following specific proof gates:

1. Edge-stabilizer fibers have the parallel-edge-kernel size; a single marked transposition counts individual twin-leaf transpositions with weight 1/|Aut|.
2. The positive residual separates the identity and single-leaf-transposition C2 from every other vertex automorphism group, using a uniform group gap of at least 1/6.
3. Two selected marks cost O(w^6/n^2), while the mixed Ewens factorial moments give the sharper O(w^7/n^2) error in the main symmetry law.
4. Endpoint convolution is derived from eventual convexity of the explicit smooth logarithmic model. Every finite index below the unknown onset is retained separately.
5. A graph without a component exceeding n/2 has a union of components with edge count in [n/4,n/2], making its count exponentially small. Only then is the unique-giant identity truncated and inverted.
6. All-order connected asymptotics use Taylor expansions of explicit smooth functions, never derivatives of uncontrolled remainders. The inverse result uses widened integer brackets, not an unconditional ceiling rule.
7. The explicit second disconnection coefficient and the transferred first two connected corrections were checked algebraically.

No new audit of every analytic estimate inside the preceding report is claimed. The result is an unrefereed mathematical proof with finite checks, not a formal Lean certificate.

## Runnable exact checks

- check_graphs.py: constructs 44,169 partition pairs through n=6 and obtains 438 distinct shore-preserving graph isomorphism types. It computes vertex groups, leaf transpositions, connectivity, isolated-edge components, the positive residual and the weighted vertex-count formula.
- check_kernel_and_giant.py: examines 226,342 edge permutations on those graph types. It checks every stabilizer fiber, the leaf-lift count L times the parallel-edge-kernel size, the unique-giant identity, and each possible finite-fragment size.
- check_cycles.py: checks 2,714 cycle types through n=20 with exact fractions, including A007716 values, weighted mass, marked leaf mass, the shifted Y identity, A007718 via the inverse Euler transform, and reciprocal coefficients. It independently compares its masses with the direct census through n=6.

All tests pass. The first reciprocal coefficients are 1, -1, -3, -3, -8, -8, -38. The connected zero convention in this package is c_0=0, distinct from the OEIS display convention; all positive-index values agree.

## Reproducibility and PDF inspection

The package was extracted into a clean temporary directory. Its manifest passed; all three exact JSON outputs were regenerated and compared byte for byte with the recorded outputs. The prior ZIP's integrity check passed. The PDF was rebuilt with a freshly generated local TeX format, and the build had no overfull boxes, underfull boxes or unresolved references. The final ten pages were rendered and visually inspected, including the final source-scope and references pages after revision. No clipping, overlapping equations or missing glyphs was found.

The checkers use only Python's standard library. LaTeX and fonts are external build dependencies. The PDF build fixes its source epoch and omits date and trailer identifiers to make same-toolchain clean rebuilds reproducible. Exact finite tests do not establish asymptotic bounds or effective numerical onset.

## Source and priority limits

OEIS A007716 and A007718, the classical connectedness references, and the 2025 regular-bipartite-multigraph paper were checked. The literature search is bounded. The paper distinguishes the uniform n-edge ensemble with varying vertex counts from fixed-shore-size regular ensembles and makes no exhaustive priority claim.
