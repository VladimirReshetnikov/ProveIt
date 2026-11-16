# Median mathematics in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 16 November 2026.

## Start here

- `paper/median_ipra.pdf` - the full human-readable manuscript.
- `paper/median_ipra.tex` - standalone LaTeX source.
- `THEOREM_LEDGER.md` - statement-by-statement coverage of the Wikipedia
  article, including corrected hypotheses and counterexamples.
- `lean/MedianFiniteBlueprint.lean` - ambient Lean definitions and proof
  obligations; no `sorry` and no theorem axiom.
- `lean/MedianObjectLanguageTarget.lean` - the actual `Prf PRAAx` endpoint.
- `lean/ROADMAP.md` - dependency-ordered path to a complete formalization.
- `code/median_ipra_reference.py` - exact integer/Fraction regression checker.
- `code/validation.json` - recorded successful run.
- `provenance/SOURCES.md` - source and trust inventory.

## Main results

The finite core uses the division-free balance predicate

```text
2 * #{x_i < t} <= n  and  2 * #{x_i > t} <= n.
```

For sorted data `x_0 <= ... <= x_(n-1)`, its solutions are exactly

```text
[x_floor((n-1)/2), x_floor(n/2)].
```

This single theorem yields the odd/even formulas, existence, uniqueness,
quantile identifications, order invariance, robust rank bounds, and the exact
set of minimizers of total absolute deviation. For even samples the report
uses `TwiceMedian = lowerMiddle + upperMiddle`, avoiding division inside the
arithmetic theory.

For a finite weighted law with total weight `W`, first and second raw moment
numerators `S,Q`, and doubled median `M`, the manuscript proves

```text
(2*S - M*W)^2 <= 4*(W*Q - S^2),
```

which is the denominator- and square-root-free form of
`|mean - median| <= standard deviation`.

The exact distribution of an odd sample median is proved by multinomial
counting, and its CDF is a binomial tail. This supplies the finite base for an
effective asymptotic-normality theorem using the existing finite CLT and
regular-name architecture.

## Constructive scope

Finite lists, finite rational laws, sorting, bounded counts, exact sample laws,
robustness, median filters, conditional medians, Theil-Sen slopes, Walsh
averages, and one-dimensional k-medians are primitive-recursive and admit
quantifier-free induction proofs.

Continuous distributions, logarithms, square roots, geometric medians, and
asymptotic claims are stated only for presentations carrying explicit
primitive-recursive interval evaluators and moduli. The packet does not turn a
qualitative classical existence theorem into an iPRA theorem by silently using
choice or arbitrary real numbers.

Several claims in the source page need restrictions. The packet supplies a
finite counterexample to the mean/median skew heuristic, a discrete
counterexample to an unrestricted reading of the sharper unimodal bound, the
non-collinearity condition for uniqueness of a geometric median, the correct
k-medians objective, and monotonicity rather than arbitrary injectivity for
transformation invariance.

## Lean status

The Lean files are blueprints, not completed kernel-checked derivations. The
repository already has a PA/I-Sigma-1 list-coding development with a
`TwiceMedian` relation and semantic proofs, but the requested endpoint is
stronger: each theorem must be a closed formula accompanied by a
`Prf PRAAx` derivation in the iPRA development. `lean/ROADMAP.md` gives the
construction order and exact audit criterion.

## Exact validation

Run from the archive root:

```sh
python3 code/median_ipra_reference.py --output code/validation.json
```

The recorded run passes 1,662,266 exact cases. Floating-point output is used
only to display the decimal form of `221/66`; every assertion uses integers or
`fractions.Fraction`.

## Build

```sh
./build.sh
```

The script reruns the exact checker and compiles the manuscript with
`latexmk` (or three `pdflatex` passes as a fallback).
