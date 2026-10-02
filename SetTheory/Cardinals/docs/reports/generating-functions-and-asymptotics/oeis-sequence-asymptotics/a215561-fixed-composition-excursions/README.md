# Fixed-composition excursions

**D-finiteness, transcendence, and all-order asymptotics for OEIS A215561, with an explicit correction for A215570 and asymptotic inversion; merged with an elementary convolution route, general step sets, and the giant-component law**

A research report on the words with n copies of each letter 1, …, r whose
every prefix sum is at most (r+1)/2 times its length. Write A_r(n) for
their number; the rows of the OEIS array A215561 are A000108 (r = 2),
A007004 (3), A215562 (4), A215570 (5), A215571 (6) and A215593 (7). The
report is built from two manuscripts of batch 73 that prove the same
theorems independently, written the same day; both are dated October 1,
2026 and were prepared for Vladimir Reshetnikov.

| Source | Manuscript | Archive | Pin | Arrival | Placed | Printed as |
|---|---|---|---|---|---|---|
| 61 (base) | batch 73, manuscript 61: *Fixed-composition excursions* (1,505-line source, 25-page A4 PDF) | `oeis_balanced_excursions.zip` | `40b17f2fc` | `aa43cc555` | `6e193dd4f` | Sections 2–13, 22–23, Appendix A; Appendix B rewritten |
| 42 (member) | batch 73, manuscript 42: *Balanced Late-Growing Permutations* (953-line source, 22-page letter PDF) | `late_growing_excursions.zip` | `bc4d1fa2b` | `bdf1a1a73` | `6e193dd4f` | Sections 14–21; notes and second proofs in Sections 2–13; merged into Sections 7, 22, 23 and Appendix B |

Section 1 (new) gives the provenance, a result-by-result crosswalk (Table
1), the merge decisions, the repository context and the notation (Table 2,
renamed symbols). Source 61's pin postdates source 42's arrival and holds
source 42's archive as an unopened zip, so source 61's "no repository
matches" could not see it; a dated note in Section 2.3 says so. The two
texts share about 1.8 % of their 8-word shingles (bibliography, OEIS rows,
kernel polynomials), their 47 common exactly computed terms are equal, and
their constants agree to the last printed digit for r ≤ 8.

Status: AI-assisted, unrefereed, **not formalized**. No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status.

## Files

```
article.tex                                      the merged report, standalone LaTeX, internal bibliography
article.pdf                                      the compiled report, 45 pages (unnumbered title page, then pages 1–44)
README.md                                        this guide
61-balanced-SOURCES.md                           source 61's source and claim provenance, as delivered
61-balanced-BUILD.md                             source 61's build and visual-QA receipt, as delivered
code/61-balanced-verify.py                       source 61: exact count-vector DP, bridge-logarithm and sextic checks, diagnostics
code/61-balanced-derive_alpha5.py                source 61: exact symbolic sextic elimination and first r = 5 correction
code/42-late-growing-verify.py                   source 42: exact DP with primitive/return arrays, bridge identity, sextic, constants r ≤ 12
code/42-late-growing-first_correction.py         source 42: exact Gaussian-moment first corrections for r = 3, 5
data/61-balanced-exact_rows.json                 source 61: enumerated rows, indexed from n = 0
data/61-balanced-kernel_constants.json           source 61: kappa_r, c(r) and reduced kernels, r ≤ 8
data/61-balanced-diagnostics.json                source 61: asymptotic and inverse diagnostics with input origins
data/61-balanced-verification.txt                source 61: recorded output of its verify.py
data/61-balanced-symbolic_verification.txt       source 61: recorded output of derive_alpha5.py
data/61-balanced-requirements.txt                sympy==1.14.0, mpmath==1.3.0 (identical to source 42's file)
data/42-late-growing-exact_counts.csv            source 42: exact counts, primitive counts, sums of return counts (CRLF)
data/42-late-growing-constants.csv               source 42: E_r = kappa_r, c(r), limits and deflated kernels, r ≤ 12 (CRLF)
data/42-late-growing-asymptotic_diagnostics.csv  source 42: finite-index ratios against the limits (CRLF)
data/42-late-growing-verification.txt            source 42: recorded output of its verify.py
data/42-late-growing-first_correction.txt        source 42: recorded output of first_correction.py
```

The three source-42 CSV files have CRLF line endings, as Python's `csv`
module writes them; `SetTheory/Cardinals/.gitattributes` marks them
`-text`, so they are stored byte-for-byte. Not shipped: both PDFs, both
delivered READMEs (this README replaces them), source 42's manuscript,
its `SHA256SUMS.txt` (verified 11/11 at placement and retired) and its
`requirements.txt` (byte-identical to the shipped one). `article.pdf` is a
build of the merged text.

## Labels and numbering

Every label carries the prefix `fce:`; source 42's material carries
`fce:lg:`. Source 61 delivered 70 unprefixed labels; all 70 are kept, with
the prefix (14 of them collided with source 42's bare labels: `eq:Q`,
`eq:diag`, `eq:kernel`, `eq:markedP`, `eq:oeisconj`, `eq:phase`,
`eq:prefix`, `eq:sextic`, `eq:steps`, `eq:transfer`, `lem:kernel`,
`sec:checks`, `sec:inverse`, `thm:main`). The write added 18 `fce:` labels
(Section 1, the three parts' anchors, the merged tables, and labels on
unlabelled sections of source 61) and 61 `fce:lg:` labels: **149** in
total. Source 42's labels on results printed once from source 61 (its main
theorem, D-finiteness theorem, kernel lemma, root-product proposition,
sextic, Lambert-W formula and first inverse corrections, and the
equations that only restate source 61's) are not used.

Source 61's Section k is Section k + 1 here for k = 1, …, 12, its
Sections 13 and 14 are Sections 22 and 23, and its Appendices A and B keep
their letters (B is rewritten); every numbered statement keeps its place
in its section. Source 42's Sections 3, 4, 7, 8, 9 and 11 are Sections 15,
16, 17, 18, 19 and 21 here; its Section 1 is merged into Section 2, its
Section 2 is Section 14 (with its kernel lemma and second proof
of the bridge identity in Sections 4–5), its Section 5 is merged into
Section 7, its Section 6 into Section 4, its Section 10 is Section 20 (its
inverse is that of Section 11), its Sections 12–13 are merged into
Sections 22–23, and its Appendix A into Appendix B.

## What is proved

For every fixed r ≥ 2 (Theorem 3.1, both sources):

    A_r(n) ~ kappa_r (rn)! / (rn (n!)^r),   kappa_r = exp( sum_{m≥1} P(S_m = 0)/m ),

with kappa_r a positive real algebraic number given by a finite
kernel-root product (Proposition 5.2), and a complete expansion in powers
of 1/n with algebraic coefficients alpha_{r,j}. This proves Kotesovec's
2016 fixed-row conjecture recorded in A215561. Every row is D-finite
(Theorem 3.2, both sources); every row generating function with r ≥ 3 is
transcendental (Theorem 3.2, source 61). For A215570,
alpha_{5,1} = −13/10 + 13 sqrt5/50 (Theorem 3.3, computed in both
sources by different contractions), and every alpha_{5,j} lies in
Q(sqrt5) (source 61).

Also proved: the limit law of the number of returns to zero
(Theorem 10.1; source 42's Theorem 19.2 for every centred rational
composition, with all fixed moments); centred rational rays with all
orders and D-finiteness (Corollary 12.1, source 61); the leading term for
every finite labelled integer step list by a one-large-summand argument
with only finite bridge mass (Theorem 16.1, source 42); a second
all-orders route with a Gaussian-moment algorithm and first-correction
formula (Sections 17–18, source 42); second-order terms for r = 2, 3
(source 42); a single giant primitive component with independent
Boltzmann decorations and an m^(−1/2) gap tail with infinite mean
(Section 19, source 42); eventual strict log-convexity (source 42); an
exact lower-branch Lambert-W core with corrections (both) and an explicit
rounding bound (source 42). Table 3 gives kappa_r, c(r) and 2 kappa_r − 1
for r ≤ 12.

**Not claimed:** the specific order-three recurrence of Kauers and
Koutschan for A215570 (Conjecture 15) is NOT proved; no recurrence for
A215562 is given, and no minimal recurrence order is established
(D-finiteness is an existence theorem); nothing is uniform in growing r;
no convergence, Borel summability, optimal truncation, Gevrey bound or
exponentially smaller sector of the expansion; no finite log-convexity
threshold; root values are high-precision numerics, not interval
certificates; the source audits are bounded and exhaustive priority is not
claimed; the A215570 terms n = 20 and n = 50 in the diagnostics are
OEIS b-file values, not independently enumerated. The leading constants
for r = 4, 5 already posted in OEIS are credited to Kotesovec; the kernel
method, the bridge–excursion identity and Lipshitz's diagonal theorem are
classical.

## Repository context

- The rounding statements (Section 11.3 and inequality (20.4)) are
  instances of `p0:thm:staircase` of the canonical transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`),
  whose separation clause is the Lean theorem `Fabius.staircase_separation`
  (with `Fabius.staircase_separation_fails`) in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
  Those formal theorems are general facts about ceilings; they do not
  verify this report's asymptotic inputs. The Lambert-W core is an
  instance of the same chapter's inversion apparatus
  (`p0:thm:perturbed-inversion`). Neither source cited these; the report
  does, and claims no novelty there.
- The bridge–excursion identity is the composition-marked case of
  Corollary `cor:excursion` of
  [`multiple-chain-exponential-formula`](../../../enumerative-combinatorics/multiple-chain-exponential-formula/).
- No other repository report concerns A215561 or its rows. Cluster O2's
  balanced Smirnov words report (A330266) uses "balanced" in a different
  sense.

## Build

From this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

(or three `pdflatex` passes). The committed PDF was built this way with
MiKTeX: 45 pages, no errors, warnings, undefined references, multiply
defined labels, duplicate destinations or overfull/underfull boxes.

## Rerun the checks

Python 3.10 or later with `sympy==1.14.0` and `mpmath==1.3.0`
(`data/61-balanced-requirements.txt`). **Do not run the scripts in this
directory**: each writes its outputs under the delivery names in `data/`
beside `code/` (`verification.txt`, `exact_rows.json`, `constants.csv`, …),
and both `verify.py` programs write a file named `verification.txt`. Run
each source on its own copy with the delivered layout:

    mkdir -p /tmp/fce61/code /tmp/fce61/data /tmp/fce42/code /tmp/fce42/data
    for f in verify derive_alpha5; do cp code/61-balanced-$f.py /tmp/fce61/code/$f.py; done
    for f in data/61-balanced-*; do cp "$f" "/tmp/fce61/data/${f#data/61-balanced-}"; done
    for f in verify first_correction; do cp code/42-late-growing-$f.py /tmp/fce42/code/$f.py; done
    for f in data/42-late-growing-*; do cp "$f" "/tmp/fce42/data/${f#data/42-late-growing-}"; done
    (cd /tmp/fce61 && python code/verify.py && python code/derive_alpha5.py)
    (cd /tmp/fce42 && python code/verify.py && python code/first_correction.py > first_correction.out)

Rerun on 2026-10-01 this way (Windows, Python 3.14.4, 15 s and 37 s):
every regenerated source-61 file equals the shipped one after removal of
carriage returns; source 42's three CSV files are byte-identical and its
`verification.txt` differs only in four timing fields; both stdout
captures of the symbolic programs equal the shipped records. `python
code/verify.py --quick` (source 42) shrinks the DP boxes and overwrites
the diagnostic data with the smaller run. Source 42's full DP stores
arrays of size (n+1)^r. The largest source-61 enumeration uses 1,419,857
rectangular states.

## Disclosures

- The shipped programs, data and markdown files are byte-identical to the
  delivery and use delivery names. Rename map: `code/<name>.py` →
  `code/61-balanced-<name>.py` or `code/42-late-growing-<name>.py`;
  `data/<name>` → `data/61-balanced-<name>` or `data/42-late-growing-<name>`;
  `requirements.txt` → `data/61-balanced-requirements.txt`; `SOURCES.md`,
  `BUILD.md` → `61-balanced-SOURCES.md`, `61-balanced-BUILD.md`.
- `61-balanced-BUILD.md` describes the delivered 25-page PDF, not
  `article.pdf`; `61-balanced-SOURCES.md` says repository searches found no
  A215561 match (true at its pin, which held source 42 only as an unopened
  zip) and names `code/verify.py`, `code/derive_alpha5.py`.
- Source 42's data files keep its letters: `T_r_n` is A_r(n), `E_r` is
  kappa_r, and `d1` in `data/42-late-growing-first_correction.txt` is
  alpha_{r,1}.
- Source 61's README instruction `python code/derive_alpha5.py >
  data/symbolic_verification.txt` would, run here, write an unprefixed file
  beside the shipped one; the program also writes that file itself.
- Source 61's original Appendix B (package contents) listed delivery names;
  it is rewritten in the article for the shipped names.
