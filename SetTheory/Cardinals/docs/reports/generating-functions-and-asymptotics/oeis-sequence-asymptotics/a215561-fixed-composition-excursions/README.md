# Fixed-composition excursions

**D-finiteness, transcendence, and all-order asymptotics for OEIS A215561, with an explicit correction for A215570 and asymptotic inversion; merged with an elementary convolution route, general step sets, and the giant-component law; Part IV: a proof of the Kauers–Koutschan recurrence for A215570 and the exact coefficients α_{5,2}, …, α_{5,8}**

A research report on the words with n copies of each letter 1, …, r whose
every prefix sum is at most (r+1)/2 times its length. Write A_r(n) for
their number; the rows of the OEIS array A215561 are A000108 (r = 2),
A007004 (3), A215562 (4), A215570 (5), A215571 (6) and A215593 (7). The
report is built from three independent manuscripts: two of batch 73 that
prove the same theorems, written the same day, and a third of batch 75
that proves, among results the first two already have, the explicit
A215570 recurrence they left open. All three are dated October 1, 2026
and were prepared for Vladimir Reshetnikov.

| Source | Manuscript | Archive | Pin | Arrival | Placed | Printed as |
|---|---|---|---|---|---|---|
| 61 (base) | batch 73, manuscript 61: *Fixed-composition excursions* (1,505-line source, 25-page A4 PDF) | `oeis_balanced_excursions.zip` | `40b17f2fc` | `aa43cc555` | `6e193dd4f` | Sections 2–13, 22–23, Appendix A; Appendix B rewritten |
| 42 (member) | batch 73, manuscript 42: *Balanced Late-Growing Permutations* (953-line source, 22-page letter PDF) | `late_growing_excursions.zip` | `bc4d1fa2b` | `bdf1a1a73` | `6e193dd4f` | Sections 14–21; notes and second proofs in Sections 2–13; merged into Sections 7, 22, 23 and Appendix B |
| 75-03 (addition) | batch 75, manuscript 03: *Fixed-Content Ballot Words. A proof of the A215570 recurrence, a fixed-row asymptotic theorem, and all-orders inversion* (917-line source with 87 labels, 22-page A4 PDF) | `OEIS_Fixed_Content_Ballot_Words.zip` | `29aca108e` | `4b874cea0` | `6ea60e367` | Part IV (Sections 24–29) and Appendix C; its re-proofs as rows of Table 5; its questions merged into Section 22 (Part III); notes in Sections 1, 2, 4, 9, 11, 13, 22, 23 and Appendices A, B |

Section 1 gives the provenance, a result-by-result crosswalk (Table 1,
with three rows for source 75-03), the merge decisions, the repository
context and the notation (Table 2, renamed symbols, with a block for
source 75-03). Source 61's pin postdates source 42's arrival and holds
source 42's archive as an unopened zip, so source 61's "no repository
matches" could not see it; a dated note in Section 2.3 says so. The two
batch-73 texts share about 1.8 % of their 8-word shingles (bibliography,
OEIS rows, kernel polynomials), their 47 common exactly computed terms are
equal, and their constants agree to the last printed digit for r ≤ 8.

Source 75-03 was written without knowledge of this report: its pin
`29aca108e` (October 1, 19:03) predates the placement `6e193dd4f` (19:16)
and held the archives of sources 61 and 42 only as unopened zips, so its
"targeted search for A215561" could not find them (Section 24.1 says
so). About 1.8 % of its 8-word shingles occur in this report (0.8 % of the
report's in it), all preamble, bibliography and OEIS strings. About two
thirds of it re-proves Parts I and II, partly in a weaker form; those
results are listed with the comparison in Table 5 and not reprinted.

Status: AI-assisted, unrefereed, **not formalized**. No Lean or Rocq
development checks any statement of this report, and its place in the
research-report collection confers no formal status.

## Files

```
article.tex                                         the merged report, standalone LaTeX, internal bibliography
article.pdf                                         the compiled report, 62 pages (unnumbered title page, then pages 1–61)
README.md                                           this guide
61-balanced-SOURCES.md                              source 61's source and claim provenance, as delivered
61-balanced-BUILD.md                                source 61's build and visual-QA receipt, as delivered
code/61-balanced-verify.py                          source 61: exact count-vector DP, bridge-logarithm and sextic checks, diagnostics
code/61-balanced-derive_alpha5.py                   source 61: exact symbolic sextic elimination and first r = 5 correction
code/42-late-growing-verify.py                      source 42: exact DP with primitive/return arrays, bridge identity, sextic, constants r ≤ 12
code/42-late-growing-first_correction.py            source 42: exact Gaussian-moment first corrections for r = 3, 5
code/75-03-ballot-words-verify.py                   source 75-03: resolvent and sextic, certificate identities, saddle and eta_1, Lambda_n, DP, alpha_{5,j}
code/75-03-ballot-words-certificate_data.py         source 75-03: integer arrays of the telescoping certificate (imported by verify.py)
data/61-balanced-exact_rows.json                    source 61: enumerated rows, indexed from n = 0
data/61-balanced-kernel_constants.json              source 61: kappa_r, c(r) and reduced kernels, r ≤ 8
data/61-balanced-diagnostics.json                   source 61: asymptotic and inverse diagnostics with input origins
data/61-balanced-verification.txt                   source 61: recorded output of its verify.py
data/61-balanced-symbolic_verification.txt          source 61: recorded output of derive_alpha5.py
data/61-balanced-requirements.txt                   sympy==1.14.0, mpmath==1.3.0 (identical to source 42's file)
data/42-late-growing-exact_counts.csv               source 42: exact counts, primitive counts, sums of return counts (CRLF)
data/42-late-growing-constants.csv                  source 42: E_r = kappa_r, c(r), limits and deflated kernels, r ≤ 12 (CRLF)
data/42-late-growing-asymptotic_diagnostics.csv     source 42: finite-index ratios against the limits (CRLF)
data/42-late-growing-verification.txt               source 42: recorded output of its verify.py
data/42-late-growing-first_correction.txt           source 42: recorded output of first_correction.py
data/75-03-ballot-words-verification_log.txt        source 75-03: recorded standard output of its verify.py
data/75-03-ballot-words-verification_results.json   source 75-03: exact alpha_{5,0..8}, normalized c_0..8, constants r ≤ 8, DP rows, error table
data/75-03-ballot-words-a215570_terms.csv           source 75-03: n, Lambda_n (its C_n), A215570(n) for 0 ≤ n ≤ 103 (CRLF)
```

The three source-42 CSV files and the source-75-03 CSV file have CRLF
line endings, as Python's `csv` module writes them;
`SetTheory/Cardinals/.gitattributes` marks them `-text`, so they are
stored byte-for-byte. Not shipped: the three delivered PDFs, the three
delivered READMEs (this README replaces them), the manuscripts of sources
42 and 75-03 (their text is merged here; both survive in their arrival
commits), source 42's `SHA256SUMS.txt` (verified 11/11 at placement and
retired) and its `requirements.txt` (byte-identical to the shipped one).
`article.pdf` is a build of the merged text.

## Labels and numbering

Every label carries the prefix `fce:`; source 42's material carries
`fce:lg:` and source 75-03's `fce:kk:`. Source 61 delivered 70 unprefixed
labels; all 70 are kept, with the prefix (14 of them collided with source
42's bare labels: `eq:Q`, `eq:diag`, `eq:kernel`, `eq:markedP`,
`eq:oeisconj`, `eq:phase`, `eq:prefix`, `eq:sextic`, `eq:steps`,
`eq:transfer`, `lem:kernel`, `sec:checks`, `sec:inverse`, `thm:main`). The
batch-73 write added 18 `fce:` labels (Section 1, the parts' anchors, the
merged tables, and labels on unlabelled sections of source 61) and 61
`fce:lg:` labels: 149. The batch-75 write added 54 `fce:kk:` labels and
renamed or removed none: **203** in total. Source 42's labels on results
printed once from source 61, and source 75-03's 87 delivered labels, are
not used as such (Part IV labels its own statements afresh).

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

Part IV is appended after the closing Part III (research directions and
conclusion) and before the appendices, so every existing label keeps its
number; its sections continue the numbering as Sections 24–29, and the
certificate is Appendix C. Source 75-03's Section 5 is Section 25 (its
Theorem 5.2 is Theorem 25.2), its Section 6 is Section 26 (Theorem 6.1 is
Theorem 26.1), its Section 7 is Section 27 (Theorem 7.1 is the second
route of Section 27.1 and Proposition 27.1), its Section 9 is Section 28,
its Section 10 is Section 29 and its Appendix A is Appendix C. Its
Sections 2–4 and 8 are rows of Table 5 (with two small increments in
Section 24.2), its Section 11 is merged into Section 22 (Part III),
its Section 12 into Section 23 and its Appendix B into Appendix B.

## What is proved

For every fixed r ≥ 2 (Theorem 3.1, sources 61 and 42; leading term also
source 75-03, with error O(n^(−1/5))):

    A_r(n) ~ kappa_r (rn)! / (rn (n!)^r),   kappa_r = exp( sum_{m≥1} P(S_m = 0)/m ),

with kappa_r a positive real algebraic number given by a finite
kernel-root product (Proposition 5.2), and a complete expansion in powers
of 1/n with algebraic coefficients alpha_{r,j}. This proves Kotesovec's
2016 fixed-row conjecture recorded in A215561. Every row is D-finite
(Theorem 3.2, all three sources); every row generating function with
r ≥ 3 is transcendental (Theorem 3.2, source 61). For A215570,
alpha_{5,1} = −13/10 + 13 sqrt5/50 (Theorem 3.3, computed in all three
sources by different contractions), and every alpha_{5,j} lies in
Q(sqrt5) (source 61; second route by source 75-03).

Also proved: the limit law of the number of returns to zero
(Theorem 10.1; source 42's Theorem 19.2 for every centred rational
composition, with all fixed moments; source 75-03 adds the limiting
variance 2 kappa (kappa − 1)); centred rational rays with all orders and
D-finiteness (Corollary 12.1, source 61); the leading term for every finite
labelled integer step list by a one-large-summand argument with only
finite bridge mass (Theorem 16.1, source 42; with an O(N^(−1/5)) rate,
source 75-03, Remark 24.1); a second all-orders route with a
Gaussian-moment algorithm and first-correction formula (Sections 17–18,
source 42); second-order terms for r = 2, 3 (source 42); a single giant
primitive component with independent Boltzmann decorations and an
m^(−1/2) gap tail with infinite mean (Section 19, source 42); eventual
strict log-convexity (source 42); an exact lower-branch Lambert-W core
with corrections (all three) and an explicit rounding bound (source 42).
Table 3 gives kappa_r, c(r) and 2 kappa_r − 1 for r ≤ 12.

New in Part IV (source 75-03):

- the positive coefficient formula A_5(n) = (5n)!/((n!)^2 (3n+1)!) Lambda_n,
  Lambda_n = [u^n] (1+u)^(3n+1) (1−u)^(−2n) sum_k C(n,k)^2 u^k, from zero-step
  deletion, Lagrange inversion and a Legendre identity (Theorem 25.2);
- **Kauers–Koutschan Conjecture 15**: the order-three recurrence displayed
  in OEIS A215570 holds for every n ≥ 0 (Theorem 26.1), by a residue
  representation of Lambda_n and an explicit rational telescoping
  certificate printed in full (Appendix C), checked exactly over Q(n,t). The
  report prints both source 75-03's normalized form and the OEIS form
  (degree 15) and the common factor relating them, checked at the intake;
- the exact coefficients alpha_{5,2}, …, alpha_{5,8} in Q(sqrt5)
  (Proposition 27.1, Table 6), e.g. alpha_{5,2} = 36/25 − 63 sqrt5/125,
  by a triangular algorithm from the recurrence, with the second-order
  inverse coefficient for r = 5 (equation (28.1)).

**Not claimed:** Parts I and II do not prove the Kauers–Koutschan
recurrence (Part IV does); no minimality of its order-three operator; no
recurrence for A215562 is given, and no minimal recurrence order is
established for any other row (D-finiteness is an existence theorem);
nothing is uniform in growing r; no convergence, Borel summability,
optimal truncation, Gevrey bound or exponentially smaller sector of the
expansion (for A215570 the possible (2/27)^n mode is not determined); no
finite log-convexity threshold; root values and the error tables are
high-precision numerics, not interval certificates; the source audits are
bounded and exhaustive priority is not claimed; the A215570 terms n = 20
and n = 50 in Section 13's diagnostics are OEIS b-file values, not
enumerated there (Part IV's proved formula reproduces their recorded
ratios). The leading constants for r = 4, 5 already posted in OEIS
(including kappa_4 = 4(phi − sqrt phi)) are credited to Kotesovec; the
kernel method, the bridge–excursion identity and Lipshitz's diagonal
theorem are classical. Checking the printed certificate alone does not
establish the counting semantics; the proof is the chain from words to
the coefficient formula and the certificate.

## Repository context

- The rounding statements (Section 11.3, inequality (20.4) and source
  75-03's rounded threshold in Section 28) are instances of
  `p0:thm:staircase` of the canonical transseries volume
  (`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`),
  whose separation clause is the Lean theorem `Fabius.staircase_separation`
  (with `Fabius.staircase_separation_fails`) in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.
  Those formal theorems are general facts about ceilings; they do not
  verify this report's asymptotic inputs. The Lambert-W core is an
  instance of the same chapter's inversion apparatus
  (`p0:thm:perturbed-inversion`, `p0:thm:lambert-core` with b < 0), and
  source 75-03's corrections and nested-logarithm anchor are instances of
  `p0:thm:lambert-centered` and of `t2:thm:balanced-inverse` in
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`.
  None of the three sources cited these; the report does, and claims no
  novelty there.
- The bridge–excursion identity is the composition-marked case of
  Corollary `cor:excursion` of
  [`multiple-chain-exponential-formula`](../../../enumerative-combinatorics/multiple-chain-exponential-formula/).
- No other repository report concerns A215561 or its rows. Cluster O2's
  balanced Smirnov words report (A330266) and the theta-ballot power-sum
  report (A357825) use "balanced" and "ballot" in different senses, and
  the "Conjecture 15" of `ballot-polynomial-hankel-determinants` is
  Cigler's, not Kauers and Koutschan's.

## Build

From this directory:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

(or three `pdflatex` passes). The committed PDF was built this way with
MiKTeX on 2026-10-02: 62 pages, no errors, warnings, undefined
references, multiply defined labels, duplicate destinations or
overfull/underfull boxes.

## Rerun the checks

Python 3.10 or later with `sympy==1.14.0` and `mpmath==1.3.0`
(`data/61-balanced-requirements.txt`; source 75-03 recorded the same
versions). **Do not run the scripts in this directory**: each writes its
outputs under delivery names, sources 61 and 42 in `data/` beside `code/`
(`verification.txt`, `exact_rows.json`, `constants.csv`, …; both
`verify.py` programs write a file named `verification.txt`), and source
75-03 beside the script itself (`verification_results.json`,
`a215570_terms.csv`); source 75-03's `verify.py` also imports
`certificate_data` by its delivered name. Run each source on its own copy
with the delivered layout:

    mkdir -p /tmp/fce61/code /tmp/fce61/data /tmp/fce42/code /tmp/fce42/data /tmp/fce03
    for f in verify derive_alpha5; do cp code/61-balanced-$f.py /tmp/fce61/code/$f.py; done
    for f in data/61-balanced-*; do cp "$f" "/tmp/fce61/data/${f#data/61-balanced-}"; done
    for f in verify first_correction; do cp code/42-late-growing-$f.py /tmp/fce42/code/$f.py; done
    for f in data/42-late-growing-*; do cp "$f" "/tmp/fce42/data/${f#data/42-late-growing-}"; done
    for f in verify certificate_data; do cp code/75-03-ballot-words-$f.py /tmp/fce03/$f.py; done
    (cd /tmp/fce61 && python code/verify.py && python code/derive_alpha5.py)
    (cd /tmp/fce42 && python code/verify.py && python code/first_correction.py > first_correction.out)
    (cd /tmp/fce03 && python verify.py > verification_log.txt)

Rerun on 2026-10-01 this way (Windows, Python 3.14.4, 15 s and 37 s):
every regenerated source-61 file equals the shipped one after removal of
carriage returns; source 42's three CSV files are byte-identical and its
`verification.txt` differs only in four timing fields; both stdout
captures of the symbolic programs equal the shipped records. `python
code/verify.py --quick` (source 42) shrinks the DP boxes and overwrites
the diagnostic data with the smaller run. Source 42's full DP stores
arrays of size (n+1)^r. The largest source-61 enumeration uses 1,419,857
rectangular states.

Source 75-03 was rerun the same way at the batch-75 intake (Windows, Python
3.14.4; 126 s under machine load, against 3.6 s recorded): all six PASS
lines; `a215570_terms.csv` regenerated byte for byte; standard output
equal to `data/75-03-ballot-words-verification_log.txt` except the
`Elapsed seconds` line; `verification_results.json` equal to the shipped
file except `runtime_seconds` and `python`, and except that on Windows
the program writes it with CRLF line endings while the shipped file has
LF. The certificate check is exact cancellation over Q(n,t), not sampling.
The printed certificate polynomials of Appendix C were expanded and
compared with the arrays of `certificate_data.py` at the write, with no
difference.

## Disclosures

- The shipped programs, data and markdown files are byte-identical to the
  delivery and use delivery names. Rename map: `code/<name>.py` →
  `code/61-balanced-<name>.py`, `code/42-late-growing-<name>.py` or (source
  75-03, delivered at the package root) `code/75-03-ballot-words-<name>.py`;
  `data/<name>` → `data/61-balanced-<name>` or
  `data/42-late-growing-<name>`; source 75-03's root files
  `verification_log.txt`, `verification_results.json`, `a215570_terms.csv`
  → `data/75-03-ballot-words-<name>`; `requirements.txt` →
  `data/61-balanced-requirements.txt`; `SOURCES.md`, `BUILD.md` →
  `61-balanced-SOURCES.md`, `61-balanced-BUILD.md`.
- `61-balanced-BUILD.md` describes the delivered 25-page PDF, not
  `article.pdf`; `61-balanced-SOURCES.md` says repository searches found no
  A215561 match (true at its pin, which held source 42 only as an unopened
  zip) and names `code/verify.py`, `code/derive_alpha5.py`.
- Source 42's data files keep its letters: `T_r_n` is A_r(n), `E_r` is
  kappa_r, and `d1` in `data/42-late-growing-first_correction.txt` is
  alpha_{r,1}.
- Source 75-03's files keep its letters: `asymptotic_d` is alpha_{5,j},
  `normalized_c` is the c̃_k of (27.4), `C_n` (CSV column and
  `C_formula_range`) is Lambda_n, `E` and `c` under `constants` are kappa_r
  and c(r), and `relative_error_order_M` is Table 7's column M. Its
  `verify.py` docstring says "Run: python verify.py", and its log ends
  "data written beside this script"; run it only on a copy as above.
- Source 61's README instruction `python code/derive_alpha5.py >
  data/symbolic_verification.txt` would, run here, write an unprefixed file
  beside the shipped one; the program also writes that file itself.
- Source 61's original Appendix B (package contents) listed delivery names;
  it is rewritten in the article for the shipped names. Source 75-03's
  Appendix B and README listed its delivery names and told the reader to
  run `python verify.py` in place; the article's Appendix B now describes
  its files under the shipped names.
- Source 75-03's own description of its relation to ProveIt (searches of
  the repository overview, the combinatorics overview and A215561 at
  `29aca108e`) is reported in Section 24.1 with the note that its pin
  could not see this report; its claim to an independent proof of the
  A215561 conjecture is reported as a third, weaker proof.
