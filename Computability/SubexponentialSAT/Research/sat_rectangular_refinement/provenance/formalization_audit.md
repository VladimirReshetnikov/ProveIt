# Formalization status and boundaries

The pinned source is `anthropics/formal-math` commit
[`1a6eee293b9e00cb432eef6018a21f523623a9af`](https://github.com/anthropics/formal-math/tree/1a6eee293b9e00cb432eef6018a21f523623a9af/eth),
the revision requested in PR 31. Canonical source links, Git blob identifiers,
and CI URLs are in [formalization_status.json](formalization_status.json).

## What was inspected

`MainResults.lean` imports Mathlib and states an exact SAT-counting theorem
for one deterministic finite-alphabet Mathlib multi-stack Turing machine, with
one constant chosen uniformly before inputs. For width at most three, its
normalized-input bound is

    2^{O(min(m/sqrt(log m), n log log n/sqrt(log n)))}.

The displayed general theorem requires positive width, at least two clauses,
at least four variables, distinct clauses, and occurrence of every named
variable. The separate proved ETH wrapper handles the finite-size and
unused-variable cases. Raw repeated clauses require normalization; unused
variables contribute the corresponding power of two to a counting answer.

The inspected `Solution.lean` definitions and proofs are not placeholders.
No hidden oracle, empty input class, or semantic replacement of SAT was found
in the definition chain examined. The source audit also inspected the paper's
exact signed crossing decomposition, its two integer factorization orders,
polynomial number of pieces, coefficient/evaluation requirements, and the
recursion giving the logarithmic power one half. These interfaces are genuine
dependencies in subsequent improvements.

## Upstream verification evidence

The retrieved upstream `verify (eth)` job records successful compilation,
Lean default-kernel acceptance, nanoda-kernel acceptance, and Comparator
acceptance. Its configured allowed axioms are `propext`, `Quot.sound`, and
`Classical.choice`. The observed `sorry` warnings concern the deliberately
unproved comparison declarations in `Challenge.lean`; the inspected solution
does not import that file. Relevant exact log lines are retained in
[ci_verification_excerpt.txt](ci_verification_excerpt.txt).

**No independent local Lean rebuild was performed for this report.** The
upstream verification evidence supports the pinned original formalization.
It does not verify the new affine, pair, triple, or matrix-backend arguments
introduced by later research packets or by the present report. The present
finite exact Python checks also do not establish the entire imported SAT
framework or constitute an end-to-end SAT implementation.

## Space and interpretation

The reviewed OpenAI theorem supplies a polynomial-space result at the same
exponent orders. The inspected Anthropic proposition does not itself supply
that same space guarantee; it must not inherit it by citation. The present
cached contraction refinement uses subexponential space and explicitly keeps
separate the low-degree and polynomial-space alternatives.

For bounded clause density, the inherited order is `n/sqrt(log n)`. For
unrestricted 3-SAT it is `n log log n/sqrt(log n)`. This report improves stated
normalized-wire coefficients under its detailed premises; it does not claim a
new unrestricted logarithmic power or a new formal Lean verification.
