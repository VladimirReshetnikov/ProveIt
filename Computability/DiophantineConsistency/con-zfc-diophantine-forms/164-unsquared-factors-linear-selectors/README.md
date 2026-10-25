# Unsquared factors and linear selectors for Diophantine consistency

Research iteration 20, prepared for Vladimir Reshetnikov, 25 October 2026.

Start with **report/main.pdf**, with editable LaTeX sources beside it. This package supplies literal polynomials, ordinary proofs, fixed coefficient data, inverse maps, independent checks and portable reconstruction. No remote repository was changed.

## Main results

All direct equations below are quartics. Domain is part of the theorem.

| Domain and profile | Variables | Quadratic rows | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| Nonnegative integers, dimension | 206 | 158 | 8,210 | 130,686,376 |
| Nonnegative integers, balanced | 207 | 159 | 5,278 | 69,238,087 |
| Nonnegative integers, sparse | 208 | 160 | 5,198 | 65,866,712 |
| Unrestricted integers, dimension | 239 | 175 | 12,658 | 6,144 |
| Unrestricted integers, balanced | 240 | 176 | 5,232 | 4,096 |
| Unrestricted integers, sparse | 240 | 176 | 4,927 | 7,596 |

The natural 206 point improves the matched prior 219/171/8267/130686428 point in every varying metric; sparse 208 similarly improves prior 221/173/5253/65867916. The integer 239 point improves the incoming Shared Factorial Error 240/177/21482/6144 point in dimension, rows and support at equal height. Sparse 240 improves the incoming factorial-free 242/178/5018/7968 point on all four varying measures. These are matched direct-family improvements, not global variable-count records.

Small-variable results:

- Ten strictly positive variables: exact degree 304, 85 binary operations, versus the incoming 87/304 construction. The 84/410 square-weight circuit is a dominated control.
- Thirteen unrestricted integers: exact degree 152, 119 operations, versus incoming 126 operations at the same degree. This retains a degree/cost tradeoff against the previous 156/117 form.

The positive circuit has a canonical whole radix67 tuple and a separately checked whole complemented-label radix47 specialization. The latter uses 207,214 raw bytes and a 415,904-bit largest port. The encoding/controller are credited prior work; this is not a new radix theorem or a claim of current repository adoption. All four ports change coherently, so these are distinct specialized polynomials.

## New mathematics

1. The natural Horn source is evaluated using an unsquared common product instead of separately squaring each factor. A canonical sequence of CRT lifts makes all new factors nonnegative while keeping the semantic anchor dominant. The local source polynomial is preserved exactly. Soundness is pointwise; completeness uses fresh canonical representatives and is not an arbitrary natural-coordinate bijection.
2. The factorial-free integer source uses the linear selector radius R=F instead of F², justified by an elementary classical lcm bound. A signed affine radix q=4z+1 replaces the odd square; its unit/negative branches are resolved in an explicit acyclic order. These are semantic zero-existence reductions followed by exact affine and row transformations.
3. An inverse Lucas correction evaluated at k reuses existing arithmetic and saves two multiplications. Full denominator recovery must wait until the exponential projection proves the radix dyadic. A premature cancellation at prime 3 is explicitly rejected. Direct bounds ensure the completed witnesses are strictly positive.
4. A partial integer carrier shear and exact square-completion identities shorten the degree 152 root norm. The full old-polynomial shear identity and the canceled degree 152 leading form are checked; the naive uncancelled DAG bound alone is not used as an exact degree certificate.

The immutable comparison snapshot is ProveIt `7a8da414376a80b90ecf799f37ceb26fb9ac674e`. `reviews/baseline.md` records actual incoming/placed/adopted distinctions and exact archive/metric bindings.

## Literal specifications

- `natural/`: selected 206/207/208 natural quartics, pre-basis controls, complete source edits, positive restoration certificates and all collected coefficients.
- `integer/ENDPOINTS.json`: selected 239/240 integer equations, semantic-stage controls, inverse row/coordinate certificates and full expansions.
- `positive/equation_bV.json`: principal ten-positive circuit; `equation_V2.json` is the dominated control. `positive/radix47/` contains the distinct whole47 specialization with its inherited native bridge and complete coefficients.
- `roots/integer13_degree 152_ops119.json`: the complete 13-integer DAG and its separate coherent six-port tuple.

A sparse term `[c,[i,j,...]]` means c times the product of coordinates with those zero-based indices; `[]` is the constant monomial. Every direct residual list defines one equation by summing its residual squares. DAGs use only fixed integers, quantified variables, addition, subtraction and multiplication. No variable exponent, factorial, floor, binomial primitive or existentially unspecified coefficient remains in a final polynomial.

## Offline replay

Python 3.10 or later and its standard library suffice:

    python3 -B verify.py

This authenticates the entire release inventory and runs the component checks and rebuilds in separate normal and optimized disposable copies. It verifies complete equations and expansions, all graph cuts/leading forms, coefficient reconstruction, source bindings, deliberate corruptions and unchanged sealed bytes. Each top-level stage contains the component's documented finer-grained checks; stage counts are not a mathematical strength comparison between reports.

Options:

    python3 -B verify.py --mode normal
    python3 -B verify.py --mode optimized --receipt /tmp/replay.json

For a standard TeX Live installation:

    sh build_report.sh

Rebuild in a working copy or use a fresh extraction for strict inventory replay, because TeX creates auxiliary files. The supplied integrated PDF was visually reviewed page by page. Source licenses and the exact inherited dependency boundaries are retained.

## Logical scope

Each ordinary theorem composes the new reductions with named inherited arithmetic/refutation calibrations to establish in ZFC that unsolvability in its stated domain is equivalent to Con(ZFC). This neither proves consistency nor asserts an equation's unsolvability separately.

The direct branches use the numerical C222 calculus rather than K215 simulation or Jones universality. The small-variable branches retain their explicit native ancestry. Finite tests are not substitutes for unbounded proofs. No new end-to-end Lean/Rocq certificate, encoded object-ZFC derivation, global simplicity minimum or literature-wide priority is claimed. Independent reviews are separate AI-assisted mathematical/artifact checks, not outside human endorsement.
