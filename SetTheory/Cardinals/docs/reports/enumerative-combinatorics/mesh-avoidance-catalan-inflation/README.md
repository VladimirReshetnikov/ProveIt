# A proof of the generating function for OEIS A289587

**Article:** *From Mesh Avoidance to Catalan Inflation*
**Date:** September 20, 2026
**Result:** The algebraic generating function marked conjectural in the
consulted OEIS entry is proved for every coefficient.

## Provenance

This package is the merger of two independently produced archives that proved
the same theorem by the same argument:

- `mesh-avoidance-catalan-inflation` — the base of this merge. It marks
  excedances, states the mesh statistic as an exact occurrence count, and
  carries the deeper literal-mesh verification.
- `mesh-pattern-algebraic-generating-function` — folded in here and no longer
  kept separately. It marks left-to-right maxima, and contributed the
  linear-arithmetic coefficient algorithm, the two polynomial certificates,
  the reciprocal-polynomial root localization, the Fibonacci-power expansion,
  the bivariate core equation with its alternating Narayana formula, the
  extension to index 1000, and its own complete verification program.

The two write-ups are *not* alternative proofs and are not presented as such.
They ran the same case analysis on a mesh occurrence, reached the same core
class, and inverted the same run-contraction substitution `u -> u/(1+x*u)`
applied to a Narayana-refined Catalan series. The only real differences were
the marked statistic and the order in which contraction and direct-sum
decomposition were performed. The merged article keeps one presentation of the
argument — the base's — and imports from the second archive only what is
genuinely additional. Where the two used different notation, the base's
notation won and the imported formulas were rewritten; see "Reconciled
notation" below. The two verification programs were *both* kept, because their
independence is the point.

## Read first

`article.pdf` is the 20-page mathematical article; `article.tex` is its complete
LaTeX source. It includes the mesh diagrams as native TikZ, so no external image
files are required. The proof is conventional mathematics, not a proof-assistant
formalization. Finite computation corroborates the proof but is not used to
extrapolate the generating function.

The sequence counts 321-avoiding permutations that also avoid the mesh pattern
(12,174), or equivalently, by inversion, (12,234). The mesh identifiers are
explicitly decoded in the article and in both programs; the numeric labels play
no arithmetic role in the proof. The equivalence of the two patterns is proved,
not inferred from agreement of initial terms.

## Main identities

For every 321-avoiding permutation, the number of (12,174) occurrences is

    choose(number of fixed points, 2)
      + sum over maximal upper runs U of choose(length(U), 2).

An upper run consists of adjacent consecutive increasing values, all strictly
above their positions. Thus avoidance is equivalent to having no adjacent upper
succession and at most one fixed point — equivalently, to having no upper bond
and at most one singleton direct-sum component.

With the formal square root having constant term 1,

    D = x^4 - 2*x^3 - 5*x^2 - 2*x + 1,
    P = x^4 + 4*x^3 + 11*x^2 + 10*x + 3,
    Q = x^2 + 5*x + 3,
    A = (P - Q*sqrt(D)) / (8*x*(1+x)^2).

The proof contracts maximal upper runs in the Narayana family, then separates
singleton direct-sum blocks. The article also provides fixed-point and excedance
refinements, a full mesh-occurrence generating function, the bivariate core
equation, positive finite sums, two polynomial certificates for the final
algebraic step, a coefficient algorithm of linear arithmetic cost, and the
asymptotic

    a(n) ~ K * gamma^n / n^(3/2) * (1 + c_1/n + O(n^-2)),
    gamma = (1 + 2*sqrt(2) + sqrt(5 + 4*sqrt(2))) / 2
          = 3.546455444684995244456761...,
    K     = 0.413931068036970644808821...,
    c_1   = -1.008253037811239547502410....

## Reconciled notation

The merge required three renamings and one index conversion. Anyone comparing
this article against the second source archive should know them.

| second archive | here | note |
|---|---|---|
| `R(x)`, `R(x,y)` (core series) | `I(x)`, `I(x,u)` | same series, same objects |
| `B(x) = Q/(8x(1+x)^2)` | `S(x)` | the base's `B(x)` is a *different* series, `(1+x-x^2-sqrt(D))/(2x)` |
| `kappa`, `alpha` | `delta`, `gamma` | same numbers |
| `N(n,k) = C(n,k)C(n,k-1)/n`, k = peaks = records | `nu(n,k) = C(n,k)C(n,k+1)/n`, k = valleys = excedances | `N(n,k) = nu(n,k-1)`; every imported refined formula was reindexed |

The index conversion matters. The imported alternating core formula reads
`r(n,k) = sum_d (-1)^d C(k-1,d) N(n-d-1,k-d)` in the second archive's peak
convention; in this article's valley convention it is

    i(n,k) = sum_d (-1)^d C(k-1,d) nu(n-d-1, k-d-1).

The second variable means the same thing in both: on the nontrivial
sum-indecomposable cores, left-to-right maxima and excedances coincide entry by
entry, because those permutations have no fixed points (Lemma 2.3(ii)). This is
also why the two archives' core series agreed. Both forms were checked against
direct enumeration through n = 10 before the formula was written down.

The article is explicit (Remark 3.4) that "upper succession" (excedance-based)
and "upper bond" (record-based) are **not** the same predicate — they disagree
on 31 of the 321-avoiders of length at most six, the smallest being 12 — and that
the two conjunctions cut out the same class only because of the "at most one
fixed point" condition. The two are not presented as interchangeable
definitions.

## Reproduce the exact checks

Requires Python 3.9 or later. Both verifiers use only the standard library.
Run from this directory, without Python's `-O` option (checks use assertions):

```sh
python3 code/verify.py
python3 code/verify_records.py --max-n 1000 --exhaustive 11
python3 code/cross_check.py
```

`code/verify.py` (excedance-based) performs:

* literal mesh tests for both patterns through length 12;
* structural enumeration, Narayana distributions, and all fixed-point
  refinements through length 13;
* core contraction/inflation and full occurrence checks through length 10;
* independent radical-versus-recurrence coefficient checks through degree 200;
* alternating Narayana coefficient checks through degree 60 and positive
  finite-sum checks through degree 45;
* comparison with all 17 initial values in the consulted OEIS entry.

`code/verify_records.py` (record-based, carried over from the second archive and
sharing no code with the first) performs:

* its own generator, cross-checked against a filter of all n! permutations
  through length 8;
* its own literal mesh predicate against the structural characterization, for
  both patterns, through length 11 (all 82,500 Catalan permutations);
* pointwise inversion of mesh occurrences through length 8;
* the record-to-Dyck bijection and the Narayana distribution of records
  through length 11;
* 23,713 contraction/inflation round trips on nontrivial indecomposables, plus
  102 independent inflations of small cores;
* the refined core formula and the full three-statistic refinement against
  joint counts through length 11;
* the linear-arithmetic O(N) algorithm against its own positive O(N^2)
  recurrences through index 1000.

`code/cross_check.py` compares all four coefficient algorithms — the base's
positive recurrences and radical expansion, and the second archive's positive
recurrences and linear-arithmetic recurrence — at every index through 1000, and
also compares the two packages' core series.

The executed runs passed every check. Output and machine-readable results are in
`data/`; see "Contents" for which file comes from which program. At length 12,
literal enumeration checked all 208012 Catalan permutations; at length 13,
structural enumeration checked all 742900. The recorded runs took about 22, 9
and 2 seconds respectively; runtime and memory use depend on the machine, and
enumeration grows rapidly with the length. Raising the exhaustive limit entails
Catalan growth and is unrelated to the linear cost of generating coefficients.

A smaller smoke test, writing to a separate directory, is:

```sh
python3 code/verify.py --direct-n 8 --fast-n 9 --series-n 100 --out smoke-data
python3 code/verify_records.py --max-n 100 --exhaustive 8 --outdir smoke-data
```

The optional algebra/asymptotics checks require SymPy and mpmath:

```sh
python3 -m pip install -r requirements-optional.txt
python3 code/symbolic_checks.py
python3 code/symbolic_check_records.py
```

The first checks seven symbolic identities exactly, then calculates the
asymptotic constants at 80 decimal digits of working precision. The second
certifies the two polynomial certificates as exact polynomial divisions and
calculates the same constants at 90 digits; the two agree to every digit the
article prints. Numerical approximations are high-precision evaluations of exact
expressions, not interval-arithmetic certificates. The included environment
record identifies the versions actually used.

## Build the PDF

A TeX Live or MiKTeX installation providing `newtx`, AMS packages, `mathtools`,
`geometry`, `microtype`, `booktabs`, `tikz`, `enumitem`, `fancyhdr`, `xurl`,
`hyperref`, and `cleveref` is sufficient. The bibliography is inline; BibTeX is
unnecessary.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
latexmk -c
```

Or run `make pdf`. The resulting PDF was rendered and checked before packaging:
20 pages, no errors, no undefined references, no duplicate hyperlink
destinations. Font files are not included in the archive.

## Contents

- `article.tex`, `article.pdf`: the proof and supplementary results.
- `code/verify.py`: excedance-based exact enumerator and coefficient verifier.
- `code/symbolic_checks.py`: its optional symbolic and asymptotic companion.
- `code/verify_records.py`: record-based verifier, from the second archive.
- `code/symbolic_check_records.py`: its optional companion; produces the two
  polynomial certificates.
- `code/cross_check.py`: compares the four coefficient algorithms.
- `data/coefficients.csv`, `data/b289587_extended.txt`: four sequences and the
  target sequence through degree 200, from `verify.py`.
- `data/coefficients_records.csv`, `data/b289587_extended_n1000.txt`: the target
  sequence and the core series through degree 1000, from `verify_records.py`.
- `data/exhaustive_counts.csv`: directly enumerated counts for both patterns
  through n = 11.
- `data/verification_results.json`, `data/verification_log.txt`: results from
  `verify.py`.
- `data/verification_report_records.json`, `data/verification_records.log`:
  results from `verify_records.py`.
- `data/cross_check_results.json`: results from `cross_check.py`.
- `data/symbolic_and_asymptotic_results.json`, `data/symbolic_checks.log`:
  results from `symbolic_checks.py`.
- `data/symbolic_certificates.json`, `data/asymptotic_constants.json`,
  `data/asymptotic_ratios.csv`, `data/symbolic_check_records.log`: results from
  `symbolic_check_records.py`.
- `data/environment.json`: the local tool versions used for reproduction.
- `sources/source_audit.md`: source locations, what each establishes, and scope
  of the priority check.
- `OEIS_note.md`: a concise mathematical note suitable as a starting point for
  an OEIS update. Nothing has been submitted to OEIS.

Neither b-file is an official OEIS b-file; both were computed here from the
proved formula.

## Scope

The source entry attributes the generating-function conjecture to Thomas
Scheuerle on December 23, 2025, and still labelled it conjectural when consulted
on September 20, 2026. Standard results concerning 321-avoiders and Narayana
numbers are credited to the background literature and reproved where needed.
This archive proves the OEIS-listed conjecture; neither source archive claimed,
and this one does not claim, that an exhaustive priority or bibliographic search
has excluded every earlier independent proof. Finite tests are corroboration and
not a substitute for the argument. Nothing has been posted to OEIS or sent to
the source authors.
