# Countable Information, Uncountably Many Boxes

**Sharp measurable prediction bounds, exact decision-tree enumeration, and an
all-orders asymptotic expansion**

Prepared for Vladimir Reshetnikov, October 3, 2026.

## Contents

- `article.pdf`: the typeset research article.
- `article.tex`: complete LaTeX source, including bibliography; no external
  figures, font files, or bibliography database are required.
- `verify_certificates.py`: exact finite enumerations and certificate checks.
- `certificates.json`: explicit four-box nonexecutable blind rule and legal
  three-box team with success probability 3/4 for a majority.
- `verification_report.json`: output of the executed finite checks.
- `formal_series.py`: exact rational formal-series computations.
- `formal_series_report.json`: coefficients through degree ten and test status.
- `Makefile`: build and verification commands.
- `SHA256SUMS`: checksums of the other distributed files.

## Mathematical results

The article proves the sharp worst-case score floor(m/q) for finite teams with
blind, cylinder-measurable outputs, without assuming measurable success events.
It constructs simultaneous fair probability extensions for countable teams,
and a continuous-output example whose success event has inner measure zero
and outer measure one. Every extension obtained by adjoining that example's
success event is classified by a measurable density.

For finite binary configurations, blind output maps correspond to labeled
perfect matchings of the hypercube. Executable maps correspond exactly to
recursively sliceable matchings. Their count F_n satisfies

    F_1 = 1
    F_n = sum((-1)^(k+1) binomial(n,k) F_(n-k)^(2^k), k=1,...,n-1).

The count begins 1, 2, 9, 232, 206065, 212181312096. All matchings and
sliceable matchings first differ at four boxes. The article proves an
all-orders inverse-power expansion on a doubly exponential growth scale,
an explicit doubly exponential rarity bound, sharp information inequalities,
and an effective extraction theorem with a Busy Beaver obstruction.

Twelve further research directions and a modular ProveIt formalization plan
are included.

## Reproduce the checks

Python 3.10 or newer is sufficient; neither script needs third-party packages.
Run from this directory, without Python's `-O` optimization option:

    python3 verify_certificates.py
    python3 verify_certificates.py --check certificates.json
    python3 formal_series.py --degree 10

The first and third commands regenerate their respective JSON reports. The
first also regenerates `certificates.json`. On Windows, use `python` when that
is the installed Python command.

Finite checks include exhaustive enumeration of matchings through dimension
four, an independent permanent dynamic program through dimension five, all
ordered teams of one through four of the eight blind two-box rules, 1,320
balanced-list examples, the recurrence through dimension twenty, and the
exact integer comparison in the rarity theorem.

The formal-series checker uses `fractions.Fraction` throughout. It checks the
truncated fixed-point identity for R, an exponential/logarithm round trip,
and the displayed asymptotic coefficients. The analytic remainder estimates
are proved in the article; they are not established by this computation.

The decimal logarithms in `verification_report.json` are explicitly labeled
rounded evaluations of proved symbolic bounds, not interval certificates.

## Build the PDF

A TeX installation with pdfLaTeX and the packages named in `article.tex` is
required. For example, a reasonably complete TeX Live installation supplies
newtxtext/newtxmath, amsthm, geometry, microtype, mathtools, booktabs, longtable,
enumitem, xcolor, fancyhdr, titlesec, tcolorbox, xurl, and hyperref.

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Or run `pdflatex article.tex` three times. The bibliography is inline.
The included PDF was compiled successfully and its pages were rendered and
visually reviewed. The successful build produced no overfull-box warnings.

With GNU Make:

    make pdf
    make verify

## Sources and status

The research anchor is Elliot Glazer's *A choiceless box game paradox*,
arXiv:2211.10474, particularly the continuum-box question in Section 5.
The relevant ProveIt files were inspected at commit
`6fef5383b126be343cccc9baf47081ef37ab5afe`:

- `Computability/BusyBeaver/Lean/BusyBeaver/Core.lean`
- `Logic/PeanoArithmetic/ListCoding/README.md`
- `SetTheory/ClosureAxiomatization/README.md`

The article credits classical ingredients and distinguishes its sliceable
matching count from the all-matching sequence OEIS A005271. Complete source
references and the limits of the priority search appear in the article.

**Historical priority is not established.** The note supplies full mathematical
proofs and executed finite checks, but no Lean/Rocq verification of the new
results. It does not resolve Glazer's unrestricted question about what ZF
proves, and it does not claim that this question remains open in all subsequent
literature. The infinite measure-theoretic results are developed in ordinary
classical mathematics, with ZFC as a sufficient ambient theory.

No repository files were changed, no repository-wide build was run, and no
endorsement or authorship by Elliot Glazer is implied.
