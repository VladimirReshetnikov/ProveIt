# Two reductions for Diophantine consistency

Prepared for Vladimir Reshetnikov, 24 October 2026. This packet contains
two explicit improvements on the ProveIt snapshot
`84e16e43092614bae262ca59651cb9d77e31a255`.

Read **report.pdf** for the complete manuscript, including both ordinary
proofs and the closed recipe for the four large coefficients. Its editable
source is **report.tex**, with **constant_recipe.tex** and
**direct_section.tex**. No external figure, bibliography or generated
LaTeX input is needed.

## Results

| Equation | Domain | Variables | Exact degree | Further metrics |
|---|---|---:|---:|---|
| New two-root equation | Strictly positive integers | 10 | 278 | 93 binary ring operations: 55 multiplications, 22 additions, 16 subtractions |
| Matched parent | Strictly positive integers | 10 | 368 | 99 binary ring operations |
| Explicit substitution companion | Unrestricted integers | 30 | 556 | 163 binary ring operations |
| New principal direct quartic | Unrestricted integers | 576 | 4 | 368 quadratic residuals; 7,172 monomials; height 2,445,790,974,704 |
| Matched principal parent | Unrestricted integers | 604 | 4 | 372 quadratic residuals; 9,676 monomials; same height |
| New smaller-coefficient quartic | Unrestricted integers | 582 | 4 | 374 quadratic residuals; 6,200 monomials; height 964,213 |
| Matched smaller-coefficient parent | Unrestricted integers | 609 | 4 | 377 quadratic residuals; 8,823 monomials; same height |

The operation count includes multiplication by small integer literals and
squaring. Named registers are polynomial abbreviations, not extra unknowns.
Coefficient height means the largest absolute coefficient after collecting
the complete expanded polynomial. Positive and unrestricted integer domains
are deliberately distinguished. None of these numbers establishes a global
minimum across all Diophantine representations.

## The consistency equivalence and its proof status

Each construction preserves existence of a finite refutation for the
repository's fixed syntactic ZFC proof predicate. Composing the new ordinary
equivalences with the named, inherited ordinary source calibrations gives

    ZFC proves: (the specified polynomial has no zeros in its stated domain)
                if and only if Con(ZFC).

This is a proof of an equivalence, not of ZFC's consistency. The new work
supplies ordinary unbounded mathematical arguments and exact executable
checks of the finite algebraic artifacts. It supplies no new end-to-end
Lean/Rocq theorem or sealed object-language ZFC proof object. The source
calibration and internal-ZFC formalization boundaries of the pinned
repository remain explicit in the report and dependency ledgers.

The ten-positive route inherits the K215/source-61 calibration. The direct
quartics inherit the independent C222 proof-certificate route and do not
use K215, Jones compression or Sun's integer reduction.

## What is new

1. In the ten-positive equation, saturate the strong Pell radicand with the
   first Pell radicand. Their product being a square then recovers both
   roots by coprimality. A modular obstruction rules out equal rational
   radicands, and an adjacent-coefficient descent recovers the remaining
   integral root. An upper polynomial center permits a shorter transport
   weight. Exact cancellation lowers the degree from 368 to 278 and the
   live circuit count from 99 to 93. Saturation itself is credited to the
   earlier nine-positive work; this adjacent-norm and transport construction
   is the new application.
2. In the direct route, replace selected linear terms of the dominating
   Pell frame by squares. Bounds on signed outputs then recover their true
   positive power values. Together with additional exact source consequences,
   this removes 12 nonnegativity predicates. Fresh private Pell completion
   is proved in both directions, since the new and old frames are different.
   Exact monic elimination then yields the complete 576/582-variable quartics.

## Contents and formats

* `ten_positive/equation.json`: all 93 arithmetic instructions, ten inputs,
  domain, degree data and coefficient bindings. A row
  `[name, op, left, right]` is a binary `+`, `-` or `*` instruction. String
  operands name earlier registers; integer operands are literals. Output: `N`.
* `ten_positive/coefficients/`: all four complete fixed integers, compressed
  as unsigned little-endian byte strings, with compressed and raw hashes.
  `SEED.txt` plus `rebuild_coefficients.py` reconstruct every payload from
  the closed 436-character recipe.
* `ten_positive/integer30.json`: the complete unrestricted-integer companion,
  replacing each positive input by `1+a*a+b*b+c*(c+1)`.
* `direct/variants/63/support32/`: the principal 576-variable equation.
* `direct/variants/63/support16_affine2/`: the 582-variable smaller-height
  companion.
* In either direct profile, `equation.json` lists every residual `R_j` and
  declares the equation `sum(R_j**2)=0`. `polynomial.json` lists the complete
  expanded polynomial. A term `[coefficient, indices]` means the coefficient
  times the product of the indexed variables; indices are zero-based and
  repetitions encode powers. For example `[7,[0,0,3]]` means `7*x0*x0*x3`;
  `[-2,[]]` means the constant `-2`. There are no missing coefficient ports.
* `projection.json` contains all monic eliminations and their integer
  restoration maps, not just a variable-count claim.
* Each branch includes ordinary proof notes, independently authored review,
  exact checks, normal/optimized receipts, pinned upstream dependencies and
  their licenses. `PROVENANCE.json` links the source ledgers.
* `METRICS.json`, `VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json` and
  `MANIFEST.sha256` supply machine-readable results and release integrity.

## Verify offline

Python 3.10 or later and its standard library suffice. From this directory:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

These commands replay the exact algebra, full coefficient construction,
independent source audit and every integer restoration/expanded coefficient.
They preserve optimized mode in child processes. Essential checks use
explicit exceptions rather than Python assertions. Results are deterministic;
there is no search for a contradiction or assumption that one exists.

To repeat the slower deterministic monic optimization as well:

```sh
python3 -B verify.py --rebuild-direct
```

To compile the manuscript with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

An ordinary proof is not replaced by these finite checks. The report states
the source hypotheses and explains why each unbounded reconstruction works.

## Suggested ProveIt integration

The complete directory can be retained as an incoming research packet.
After review, the ten-positive branch can become a new candidate beside
`ten-positive-zero-offset`, and the direct branch can become a new research
packet beside `factorial-radius-output-sign-profile`. The existing baselines
and their provenance should remain available. No remote repository changes
are part of this deliverable.
