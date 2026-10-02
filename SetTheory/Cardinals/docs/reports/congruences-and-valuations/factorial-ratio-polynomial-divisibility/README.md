# Polynomial divisibility of height-one factorial ratios

**Part I: proofs of Bala's uniform-multiplier conjectures, a complete
rational-root criterion, and certified optimal constants. Part II: rational
dilation, integrality, and algebraicity of factorial ratios (A347854–A347858,
A295432).**

A research report in two Parts, built from two AI-assisted manuscripts
(author lines "OpenAI ChatGPT" and "Research draft prepared with ChatGPT").
Both are unrefereed, and nothing in this report is formalized in Lean or
Rocq.

| Part | Source | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| I | the original report (dated 19 September 2026) | one of the 64 reports of the Cardinals repository's first unpacking; merged into ProveIt with that history in `dc54c3cb3` | none recorded | `a3fe9660e` (Cardinals history) | Sections 1–9, Appendices A–B |
| II | batch 74, manuscript 01 (dated 1 October 2026) | `OEIS_Fractional_Factorial_Theorems.zip`, arrival commit `c664fc2f0` (24-page PDF, not shipped) | no ProveIt commit; its only repository citation is the root `README.md` blob `bfe39c17`, introduced by `e37a17848` | `b669cff87` | Sections 10–23, Appendices C–D |

## Start here

Read **article.pdf** (49 pages: an unnumbered title page, then pages 1–48).
Its source is **article.tex**; the atlas table loaded by the source is
supplied in `data/atlas_table.tex`. Part I begins on page 4, Part II on
page 19. Section 10 is Part II's preface: its source, what it re-proves from
Part I, what is new, and a notation table for the two Parts.

**Part I** gives a general rational-root criterion for uniform polynomial
divisibility of balanced integral factorial ratios. It applies the criterion
to Peter Bala's uniform-product conjectures for OEIS A211417 and A295431,
proves explicit multipliers for every product length, and certifies the least
multipliers in the eight particular examples. It also contains an atlas for
the 52 sporadic height-one ratios, exact recurrences, generating functions,
and asymptotic expansions. The main existence and classification proofs are
conventional mathematical arguments. The eight optimal-constant results
additionally use finite exact certificates. Neither a large numerical sample
nor an unverified graph search is being substituted for an all-index proof.
See **STATUS.md** for the boundary between Part I's results, earlier work,
and unchecked questions of priority.

**Part II** proves that the Gamma-interpolated ratios A347854–A347858 take
positive integer values and have algebraic ordinary generating functions. The
arithmetic goes through a rational-dilation theorem for height-one ratios,
valid for composite denominators: the Gamma quotient is first cancelled to an
integer progression, a residue-shifted valuation formula reduces each shift
to a slice of the ordinary Landau function, and the primes dividing the
denominator are treated separately (the example 7/6 shows that substituting a
rational slope into Landau's criterion fails). Algebraicity comes from
fractional Frobenius solutions of four hypergeometric equations whose finite
monodromy is certified by four positive-definite integral Gram matrices.
Part II also proves the June 2026 conditional refinements of A347854 and
A347855, the divisor `6(6n+1)(12n-1)` of A295432, beta-product moment laws
with strict Hankel positivity, and an all-orders expansion with an explicit
fixed-order remainder constant `E_J`.

## Duplicates and what is new (Part II)

Part II's manuscript did not consult Part I, which was already in the
repository. Its A295431 statements are therefore **not new**: the multipliers
385, 5, 1, 770 for `n+1`, `2n+1`, `3n+1` and their product, the division by
`12n-1`, and both infinite clearing families are proved in Part I, with
smaller family constants (Part I's `L_r^{|I|}` and `(∏ g_i) L_{12r}^r`
divide Part II's `D(r) = L_r^r` and `C(k,r) = (k L_{12r})^r`) and with the
four multipliers shown least possible. Part II prints its digit-sum proofs
of these statements as a marked second route (Sections 16.2–16.3), and
Section 10.2 says so.

New relative to the repository: A347854–A347858 (integrality and
algebraicity), the rational-dilation theorem, the June 2026 refinements,
A295432's divisor, the Gram certificates, the moment laws, and the constant
`E_J`. The asymptotic and Lambert-W inverse sections of Part II instantiate
results already in the repository and claim no novelty: Part I's
factorial-ratio expansion (its equation (42)); `t2:thm:gamma` and
`t2:thm:balanced-inverse` of
`Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`
(with `a = log R`, `β = -1/2`, so the inverse uses the lower real branch
`W_{-1}`, values at most −1, which yields the large solution; the manuscript
says "negative real branch", its delivered README "large real branch"); and
the staircase theorem `p0:thm:staircase` of
`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
for integer index recovery. Dated `[write]` notes in Sections 11, 20, 21, 23
and Appendix D record this.

## Status of the questions Part I left open

**[Added 1 October 2026, batch 74.]** `STATUS.md` says that conjectures on
"gamma-interpolated values" in these OEIS entries are not claimed settled.
For A347854–A347858 they are now settled in Part II (integrality and
algebraic generating functions). The supercongruences in these entries
remain unclaimed in both Parts, as do minimal algebraic equations and their
degrees. A dated note to this effect is appended to `STATUS.md`; its earlier
text is unchanged. Part II's research question on minimal clearing constants
is re-scoped in the article: Part I's digit graphs settle the four specified
products, and what stays open is the behaviour of the optimal constants as
the product length `r` grows, which Part I already lists as open.

## Labels and notation

Part I's 56 labels are bare (`eq:…`, `thm:…`, `prop:…`, `lem:…`, `cor:…`,
`sec:…`, `app:…`) and are unchanged, as are their numbers (the `.aux`
numbers of all 56 were compared with a build of the committed text). Part
II's labels carry the prefix `ffd:`: the manuscript's 85 labels, prefixed,
and 18 added in writing (section, appendix and subsection anchors, and
`ffd:partI:directions` on Part I's research-directions subsection, the only
addition to Part I's body apart from the Part heading). In all, 159 labels
(56 → 159). Bibliography keys of Part II carry the prefix `ffd-`; Part II
reuses Part I's entries for Bober and DLMF §5.11.

Each Part keeps its own notation; the table in Section 10.4 lists every
collision. The dangerous ones: Part I's `B(n)` is A295431, which Part II
calls `U(n)`; Part II's A295432 is printed `B̃(n)` (the manuscript's
`B(n)`, the only renamed symbol); Part I's `U_n` is a different sequence
(`42A(n)/((2n+1)(3n+1)(5n+1))`) that Part II never uses; `A`, `B`, `L` are
sequences or the lcm in Part I but integer slope parameters in Part II.
Part II prints the valuation as `ν_p` (Part I: `v_p`).

## Files

```text
article.tex                                         the report (Parts I and II), standalone LaTeX
article.pdf                                         compiled report, 49 pages
README.md                                           this guide
STATUS.md                                           Part I's research-status notes, with a dated batch-74 note appended
Makefile                                            Part I's build shortcuts (pdf, verify, test, regenerate)
02-fractional-dilation-reviewer_notes.md            Part II: the manuscript's review checklist, as delivered
code/factorial_divisibility.py                      Part I: exact factorial-ratio and factor classes, certificate generator
code/verify_certificates.py                         Part I: separate exact verifier of the eight optimal constants
code/test_research.py                               Part I: regression tests
code/generate_artifacts.py                          Part I: regenerates certificates, tables, terms
code/02-fractional-dilation-verify.py               Part II: exact checker (delivery name verify.py)
code/02-fractional-dilation-asymptotic_demo.py      Part II: numerical demonstration, needs mpmath (delivery name asymptotic_demo.py)
data/atlas_52.csv, data/atlas_table.tex             Part I: admissible-slope atlas (the .tex is \input by article.tex)
data/certificates.json                              Part I: states, potentials, witnesses for 60 prime certificates
data/certificate_statistics.json                    Part I: certificate counts
data/minima_table.tex                               Part I: alternate generated table of prime minima
data/regression_output.txt, data/test_results.json  Part I: regression record
data/sequence_U.csv                                 Part I: U_n = 42A(n)/((2n+1)(3n+1)(5n+1)), n = 0..50
data/sharp_constants.csv                            Part I: per-prime minima and witnesses
data/sporadic_parameters.json                       Part I: the 52 parameter lists (Coserea's table)
data/verification_output.txt                        Part I: recorded verifier output
data/02-fractional-dilation-results.txt             Part II: recorded checker run (ALL CHECKS PASSED)
data/02-fractional-dilation-floor_certificates.json Part II: the eleven floor partitions, as generated
data/02-fractional-dilation-terms.csv               Part II: a_i(n) for n = 0..50, five sequences
data/02-fractional-dilation-asymptotic_results.txt  Part II: demonstration log (mpmath 1.3.0, 90 digits)
data/02-fractional-dilation-asymptotic_results.csv  Part II: forward and inverse errors
data/02-fractional-dilation-asymptotic_coefficients.csv  Part II: exact gamma_j through n^-11
```

Every Part II file except `article.tex` is byte-identical to the delivery.
The three Part II CSVs have CRLF line endings as delivered and are kept so
by `-text` lines in `SetTheory/Cardinals/.gitattributes`. The delivered
manuscript, its README and its PDF are not shipped: Part II of `article.tex`
is the manuscript's text, and this README replaces the delivery README.
Delivered files whose text still uses delivery names: the two Part II
programs name each other and their outputs by delivery names
(`verify.py`, `results.txt`, `floor_certificates.json`, `terms.csv`,
`asymptotic_results.*`, `asymptotic_coefficients.csv`), and
`02-fractional-dilation-reviewer_notes.md` refers to "the manuscript".
`02-fractional-dilation-results.txt` ends by citing `article.tex`, meaning
the manuscript, now Part II here.

## Verify Part I without trusting the generator

Python 3.10 or later is required; no third-party Python packages are needed.
From this directory run:

```sh
py code/verify_certificates.py
py code/test_research.py
```

(`python` or `python3` on other systems.) The first command reads the
supplied certificates and recomputes every graph transition. It does **not**
import or run the graph generator or its optimizer. It checks the eight
stated problems, all required primes, closure of every state set, every
integer potential inequality, and direct equality witnesses. Its recorded
output is:

```text
PASS: 8 cases; 60 prime certificates; 1685 states; 19277 exact transition inequalities.
All prime-coverage, potential, and sharpness checks passed.
```

The second command runs supplementary regression tests. Their output and
exact counts are in `data/test_results.json` and `data/regression_output.txt`.
The tests include 256-bit indices with the fixed random seed 20260919.
Finite regression tests supplement the proofs; they do not establish the
all-index claims. To regenerate Part I's data and certificates before
checking them (this rewrites files in `data/`; do it on a copy):

```sh
py code/generate_artifacts.py
py code/verify_certificates.py
```

The parameter file for the atlas is an input, not a generated conjecture.
The generator checks its 52 rows for balance, height one, and nonnegativity
of the Landau step function at every breakpoint.

## Rerun Part II on a copy

Do **not** run the Part II programs from `code/`. The demonstration imports
`verify` by its delivery name (`from verify import ROWS, Row, value`), which
fails under the prefixed name, and both programs write their outputs next to
themselves under delivery names. Copy them into an empty scratch directory
under their delivery names and run there (Git Bash):

```sh
R=$(mktemp -d)
cp code/02-fractional-dilation-verify.py "$R/verify.py"
cp code/02-fractional-dilation-asymptotic_demo.py "$R/asymptotic_demo.py"
cd "$R"
py verify.py --max-n 200 --output results.txt
uv run --no-project --with mpmath==1.3.0 python asymptotic_demo.py
```

`verify.py` needs only the standard library (about 3 s here) and ends with
`ALL CHECKS PASSED`. It checks the eleven floor partitions, the four
cyclotomic pairs, eight Gram identities and their leading minors, parameter
cancellation and Frobenius exponents, and runs finite regression tests
(n ≤ 200, 9,200 general valuation identities with composite d ≤ 12, 6,120
prime-valuation cross-checks, both families for r ≤ 8 and n ≤ 30). The
demonstration (about 3 s) needs `mpmath`; its outputs are numerical, not
interval-certified. On 1 October 2026 this recipe reproduced the delivered
`terms.csv`, `asymptotic_results.csv` and `asymptotic_coefficients.csv`
byte for byte, and `results.txt`, `floor_certificates.json` and
`asymptotic_results.txt` identical **modulo line endings**: on Windows the
text-mode writes produce CRLF where the delivered files have LF. With a
different `mpmath` the second line of `asymptotic_results.txt` records that
version instead of 1.3.0. Compare with `data/02-fractional-dilation-*`.

## Build the PDF

pdfLaTeX with standard packages (Latin Modern, amsmath, amsthm, cleveref,
microtype, longtable, tcolorbox, listings, hyperref) suffices. From this
directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three
times (`make pdf` runs it twice, which can leave cross-references unsettled
after a clean checkout). Keep `data/atlas_table.tex` next to the source in
its subdirectory. No network access or Python regeneration is needed. The
committed PDF was built in a scratch directory with MiKTeX's latexmk: 49
pages, no errors, no undefined references or citations, no multiply defined
labels, no duplicate PDF destinations (the title page is built with
`pageanchor=false`, which removed the `page.1` duplicate of the earlier
build), and no overfull boxes.

## Using the Part I library

From within `code/`, for example:

```python
from factorial_divisibility import A, Factor, classify, effective_bound

assert classify(A, (Factor(2, 1), Factor(3, 1), Factor(5, 1)))
assert not classify(A, (Factor(4, 1),))
assert not classify(A, (Factor(2, 1, multiplicity=2),))
cutoff, multiplier = effective_bound(A, (Factor(2, 1),))
```

Primitive factors must have positive slope and coprime slope/offset.
Normalize nonprimitive factors and treat their integer content separately;
merge equal roots and add their multiplicities. The explicit multiplier
returned by the library is a valid bound, not a claim of minimality. The
valuation helpers take primality as a caller precondition. The certificate
generator presently handles products of distinct positive-unit-offset
factors `k*n+1`; the mathematical classification theorem is more general
than that optimizer. CSV columns containing large sequence values should be
read as exact integers or text, not as floating-point spreadsheet cells.

## What is claimed, and what is not

Claimed (by proof in the article; unrefereed): Part I's criterion,
height-one classification, explicit all-`r` multipliers and eight optimal
constants; Part II's integrality and algebraicity for A347854–A347858, the
rational-dilation theorem, the June 2026 refinements, A295432's divisor, the
moment laws and Hankel positivity, and the remainder constant `E_J`.

Not claimed, by either source: the supercongruences in these OEIS entries;
minimal algebraic equations of the five generating functions or their
degrees; minimal family constants for growing `r`; nonsplit polynomial
divisors (Part I); exponentially small or resurgent sectors of the
asymptotic expansions, or convergence of the Stirling series (Part II);
publication priority (both sources say their searches support only the
recorded OEIS status). Part II's A295431 results are a second route, not a
new result. Part II's algebraicity proof depends on the classical Levelt /
Beukers–Heckman description of hypergeometric monodromy, which the
manuscript cites rather than proves; its numerical demonstrations are not
interval-certified; and its checker is not a proof-assistant kernel.

## Relation to other work in the repository

No statement of this report is formalized, and its place in the
research-report collection gives it no formal status. The Lean-backed
partial formalization recorded for `p0:thm:staircase` (in
`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`) is a
property of the transseries volume, not of this report's index-recovery
remark. `congruences-and-valuations/a321941-asymptotic-coefficient-integrality`
shares the collection category but no theorem.

## Provenance and discrepancies

- Part II's `\bibitem{failed}` (a "first-party account" of an invalid
  rational-slope argument) is an external blog post (teai.io, 18 August
  2026, corrected 26 August 2026), not a repository file. Its
  `\bibitem{proveit}` is the root `README.md` blob `bfe39c17` of
  `e37a17848`, cited only for the trust-boundary convention. The manuscript's
  sentence that a repository search found no matching file was right for
  A347854–A347858 and A295432 and missed Part I; a dated note says so.
- The manuscript's abstract is printed in Section 10.1 with its A295431
  sentence corrected and the Lambert branch glossed. Its hard-coded section
  numbers became cross-references; its audit map pointed to a nonexistent
  "Section 7.5", which is Section 17.4 here.
- Part I's text is unchanged apart from the Part heading, one label, the
  Part II sentence and smaller vertical spaces on the title page (so that the
  title page stays one page), and the PDF metadata subject. `STATUS.md`
  still says the delivered PDF has 20 pages; that was Part I's PDF.
- Part I's attribution: the problem statements originate in Peter Bala's
  August 28, 2025 comments in OEIS A211417 and A295431; the sporadic
  parameter data are attributed to Gheorghe Coserea, and the
  factorial-ratio classification to Bober and the preceding work cited in
  the article. Part II's targets are Bala's conjectures and refinements in
  A347854–A347858 and A295432; Penson's moment formulas and the OEIS
  asymptotic scales are acknowledged as prior.
