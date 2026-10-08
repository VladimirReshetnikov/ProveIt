# Uniform Rooted Trees and Binary Partitions (OEIS A003238, A003318)

**Ratio nonconvergence and all fixed inverse-logarithmic orders: a
computer-assisted negative answer to a question of Erdős and Loxton (1979).**

A single-source report: bundle Report 215 of one external research session
(the session bundle of Reports 1–243, arrival commit `60f54ea06`), placed by
`f79c9bef1` (batch 112) and written on 7 October 2026. The author line and
PDF author field are empty and the title block reads "Report215"; the
manuscript names no person, tool or addressee.

| Source | Archive | Placed | Shipped as |
|---|---|---|---|
| *Uniform rooted trees and binary partitions: Ratio nonconvergence and all fixed inverse log orders* ("Report215", 4 October 2026) | `Report215-reproducibility.zip` (601,832 bytes, 37 files in `Report215/`; `Report215.tex`, 794 lines, 21 pp.) | `f79c9bef1` | `article.tex` |

The package records no ProveIt commit, so no pin is recorded.

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report, and its place in the
collection confers no formal status. **Theorems 1.1 and 7.1 are
computer-assisted** (exact integers and 256-bit directed intervals, including
`2^24` exact recurrence coefficients); the write reran every step of the
certificate except the `2^24`-coefficient radial sieve.

## What the report proves

`a_n = A003238(n)` (uniform rooted trees; `a_{n+1} = Σ_{d|n} a_d`),
`S_n = A003318(n)`, `β_n = A018819(n)` (binary partitions),
`Β_n = A000123(n) = β_{2n}`, `h = log 2`, `ρ = log(3/2)/log 2`.

- **Theorem 1.1:** neither `a_{n+1}/β_n` nor `S_{n+1}/Β_n` converges, even to
  `+∞`. Route: positive dyadic identities, a certified global bound
  `0 < G < 14` (Proposition 3.2), a cut positive operator with every tail
  bounded (Section 4), two conditional intervals for a hypothetical common
  limit that are disjoint (Proposition 5.1, exact gap (37)), and a positive
  Abelian transfer (Lemma 6.1). **This answers in the negative the question
  Erdős and Loxton left open on p. 328 of their 1979 paper** (whether
  `Q(x)/B(x)` has a limit).
- **Theorem 7.1:** the oscillation of the dyadic profile, and of each ratio's
  `limsup − liminf`, exceeds `0.00001839189788`.
- **Theorem 1.2:** a holomorphic dyadically periodic profile `𝒫` and
  expansions of `a_n` and `S_n` to every fixed inverse-logarithmic order, with
  relative remainder `O_J(L^{−J−1})`, a finite Gaussian prescription (50) for
  every correction, and `S_n ~ (hn/log n) a_n` (8).
- **Theorem 12.1:** smooth inverse centres with two ceilings of relative width
  `O_J(x/(log x)^{J+2})`; the leading scales (73).

(Section, statement and equation numbers are those of the committed PDF.)

## What the report does not claim

The periodic summatory leading law, the binary comparison and binary-prefix
approximation are Erdős–Loxton's; dyadic profiles and saddle polynomials are
not new methods (Mahler, de Bruijn, Dumas–Flajolet,
Banderier–Hwang–Ravelomanana–Zacharovas); bounded source comparison
(Pennington, Kato–McLeod and the final 2026 distinct-chain-partition preprint
not read); no worldwide priority. The conditional intervals are not profile
enclosures and their gap is not the oscillation bound; the bound may not be
rounded up. All orders fixed; no convergence, effective onset, growing-order
uniformity or powers of `1/n`; existential constants; relative inverse width;
no exact ceiling rule; the 48-term fixtures are not b-files.

## The write's findings

- **Cloitre's 2004 conjecture in A003238 is refuted** (Remark 1.3): the
  entry's "log(a(n)) is asymptotic to c*log(n)^2 where 0.4 < c < 0.5" has the
  right form and the wrong constant: `c = 1/(2 log 2) = 0.72134752…`, by (71)
  and (49) (also from Erdős–Loxton's Lemma 1 and the classical binary-partition
  growth). The entry already calls it "partly correct" (Zabolotskii, 2017,
  citing MathOverflow for `log(n)^2/log(4)`). The data explain the
  conjecture: `log a_n/log² n` is `0.486, 0.479, 0.489, 0.493` at
  `n = 10², 10³, 10⁴, 2·10⁴`. No OEIS edit.
- **The Erdős–Loxton citations are confirmed** from the published paper
  (note at the end of Section 2): Lemma 1, Theorem 3 on p. 324, and the open
  question on p. 328; their `B(x)` is `Β_{⌊x⌋}` and their `Q(n)` is `S_{n+1}`.
- **Remark 12.2 (transseries volume):** Theorem 12.1 is an analogue of
  `p0:thm:staircase`(2), proved directly (the approximants are not
  interpolations); the growth is outside `p0:def:model`, the leading balance in
  `log n` is quadratic, so `plt:def:lw-monomial-log-datum` does not apply as
  stated; the centres are not shown to be instances of a theorem of the
  volume.
- **Recomputed:** the sieve to `n = 20000` against all 10000 b-file terms of
  A003238, all 1000 of A003318, A018819 (`n ≤ 1000`) and A000123
  (`n ≤ 20000`), `Β_n = β_{2n}`, both shipped fixtures; the outward rounding
  of `I_1`, `I_2` against the 256-bit receipt endpoints; the exact gap
  `0.00001847273026448250…`; the global-bound endpoint; the exact
  oscillation interval; `2g/(R_1 + R_2) = 821010233977/44639777749800000`
  and the printed margin; `C_4`, `x_* < 1`, `3^200 < 2^317`, `Mt_i/2`; the
  inverse constants `2/(e√h)`, `1/(e√h)`.

## Further questions, and the standing rule

Section 14 (the source's own, with a dated note under Vladimir's standing rule
of 4 October 2026): certified profile values and an oscillation upper bound,
effective onsets, Fourier coefficients of the profile, smaller certificates,
terms below every fixed inverse-log order, and the continued source comparison;
from the non-claims, an exact ceiling rule and growing-order uniformity. No
claim of the source was found false; the one refutation is of Cloitre's OEIS
conjecture.

## Relation to the repository

Before batch 112, A003238 and A000123 appeared only as targets rejected by
the source audits of `a047874-long-increasing-subsequences` and
`a126348-stable-hilbert-series`. Nearest by object (same directory, batch
112): `a055779-labeled-fat-trees`, `a242375-many-color-rooted-trees`,
`a244407-high-outdegree-rooted-trees`; no shared result, so no reciprocal
note. No Lean or Rocq development treats these sequences.

## Labels and numbering

All labels carry the prefix `urt:`: the 95 delivered labels, prefixed before
anything cited them (94 references updated: 71 `\eqref`, 23 `\ref`), and the
write's three (`urt:rem:oeis`, `urt:sec:provenance`, `urt:rem:transseries`);
98 in all. The write's remarks are the last statements of their sections and
its additions contain no numbered display, so every number is delivered
(checked against the `.aux` of a build of the delivered text: 95 labels, 0
differences). Section 1.1 is the write's.

## Notation

No symbol was renamed. Letters with several senses are tabulated in Section
1.1, with false readings: `B(t)` (radial product) versus `Β_n` (cumulative
count) versus `B_3`; `Q`, `q`; `D`; `A`; `H`, `G`, `R`; `S_n` versus `S_3`;
`M`, `C`; `L`, `t`, `v`; `h`, `ρ`, `σ`; Cloitre's `c`.

## The write's additions

The status note after the abstract, Remark 1.3, Section 1.1 (provenance,
sources read, checks, relation, collected non-claims, reading conventions),
the dated notes at the ends of Sections 2 and 14, Remark 12.2, the label
prefixes, the bibliography entry `TSvol`, and the `\file` macro and
`writenote` environment in the preamble. Everything else is delivered text.

## Files

```text
README.md                                  this guide (replaces the delivered README.txt)
article.tex                                the report (delivered Report215.tex, written)
article.pdf                                compiled report, 26 pages
SOURCES.txt                                source ledger and bounded comparison (delivered)
SOURCE_FILES.txt                           delivered input inventory
code-README.txt                            the delivered code/README.txt
code/certified_interval.py                 256-bit directed interval primitives
code/certify_global_bound.py               certificate step 1: 0 < G < 14
code/operator_constants.py                 certificate step 2: power-majorant constants
code/certify_radial_values.py              certificate step 3: radial values, 2^24 exact coefficients (heavy)
code/certify_operator.py                   certificate step 4: T1, T^2 1, T^3 1 with tails
code/combine_certificate.py                certificate step 5: conditional intervals and their gap
code/verify_oscillation.py                 independent exact check of the oscillation corollary
code/verify_finite_models.py               finite model checks (recurrences to 10000, identities)
code/verify_exact.py                       exact prefix and identity checks
code/saddle_engine.py                      exact finite correction functional (50)
code/verify_saddle_engine.py               independent graded-exponential oracle, orders 0-4
code/verify_arithmetic.py                  rational probes of the interval primitives
code/test_certificate_guards.py            corrupted-receipt guard tests
code/reproduce.py                          full replay, PDF and ZIP driver (delivered root reproduce.py)
code/test_package_guards.py                package guard tests (delivered root test_package_guards.py)
data/PACKAGE_GUARD_CHECKS.json             recorded package guard checks (delivered root)
data/code-ARITHMETIC_CHECKS.json           receipt of verify_arithmetic.py
data/code-EXACT_CHECKS.json                receipt of verify_exact.py
data/code-FINITE_MODEL_CHECKS.json         receipt of verify_finite_models.py
data/code-GLOBAL_BOUND_CERTIFICATE.json    receipt of step 1
data/code-GUARD_CHECKS.json                receipt of test_certificate_guards.py
data/code-NONCONSTANCY_CERTIFICATE.json    receipt of step 5 (256-bit endpoints, gap, input hashes)
data/code-OPERATOR_CONSTANTS_CERTIFICATE.json receipt of step 2
data/code-OPERATOR_VALUE_CERTIFICATE.json  receipt of step 4
data/code-OSCILLATION_BOUND_CERTIFICATE.json receipt of verify_oscillation.py
data/code-RADIAL_VALUE_CERTIFICATE.json    receipt of step 3
data/code-SADDLE_CHECKS.json               receipt of verify_saddle_engine.py
data/code-b003238.txt                      48 displayed A003238 terms, transcribed (not a b-file; OEIS data, CC BY-SA 4.0)
data/code-b003318.txt                      48 displayed A003318 terms, transcribed (not a b-file; OEIS data, CC BY-SA 4.0)
data/requirements.txt                      requirements (delivered root)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to its delivery. Not shipped (retrievable from `60f54ea06`):
the delivered PDF (21 pages), the pure checksum manifest `MANIFEST.json` (36
entries, verified at the write), and the delivered `README.txt`, replaced by
this guide.

```sh
git show 60f54ea06:docs/incoming/Report215-reproducibility.zip > <scratch>/r215.zip
```

**Delivered text that names the delivery layout.** The certificate scripts
read and write their receipts beside themselves in `code/` under the
delivered names (`GLOBAL_BOUND_CERTIFICATE.json`, …, `b003238.txt`);
`reproduce.py` and `test_package_guards.py` check the closed delivered
inventory (`MANIFEST.json`, `Report215.tex`, the PDF), so they run only in a
re-extracted archive; `SOURCE_FILES.txt` and `code-README.txt` use delivered
paths; Section 13 describes the delivered archive.

**Third-party data.** The two 48-term fixtures hold OEIS terms (CC BY-SA
4.0, https://oeis.org/LICENSE), not MIT-0 like the rest of the repository.

## Rerunning the checks (on scratch copies)

Never run the programs in place: they overwrite their receipts. From this
directory (Git Bash):

```sh
T=$(mktemp -d); mkdir -p "$T/code"
for f in code/*.py; do b=$(basename "$f"); case $b in reproduce.py|test_package_guards.py) ;; *) cp "$f" "$T/code/";; esac; done
for f in data/code-*; do b=$(basename "$f"); cp "$f" "$T/code/${b#code-}"; done
cd "$T/code"
for s in certify_global_bound operator_constants certify_operator combine_certificate verify_oscillation \
         verify_finite_models verify_exact verify_saddle_engine verify_arithmetic; do py -B $s.py > /dev/null && echo "ok $s"; done
```

Compare each rewritten receipt with the shipped `data/code-*` file after
removing carriage returns (or as JSON). `certify_radial_values.py` needs about
1.6 GiB and a few minutes; run it alone, before `combine_certificate.py`, if
the machine allows. At the write (7 October 2026, Windows, Python 3.14.4)
the listed steps ran in about 60 s (global bound) and 203 s (operator), the
rest in seconds; the global-bound, operator-constant and operator-value
receipts were byte-identical after removing carriage returns, the
oscillation, exact and saddle receipts equal as JSON, and the nonconstancy
receipt differed only in the SHA-256 hashes of its inputs (line ends). The
radial step was not run (the intake confirmed its regression values with an
own sieve to `10^6`).

## Independent check of the write (7 October 2026)

An independent adversarial check of the write (`37b523e32`) read the four
OEIS entries again, together with Section 3 of Erdős–Loxton in the published
scan. Every quotation and citation is as reported. The paper says only that
its methods "could be used to give bounds for the oscillation"; calling these
upper bounds is an inference, since a positive lower bound would have
decided the question. The check is recorded in a dated note at the end of
Section 14.

- **Cloitre's conjecture.** The refutation is confirmed and holds in every
  logarithm base: the constant is `log b/(2 log 2)`, which is `1/2` in base
  2, still outside the open interval. A floating divisor sieve to `2^25`
  continues the write's data: `log a_n/log² n` is 0.503, 0.518, 0.531 and
  0.537 at `n = 10⁵, 10⁶, 10⁷, 2^25`.
- **The radial sieve, which the write did not rerun, done independently.**
  `a_{2^24}` was computed exactly by the sieve in eight word-size prime
  moduli plus CRT. It equals the receipt's 65-digit endpoint. A floating sum
  over `n ≤ 2^24` reproduces the finite radial values `H(t_1)`, `H(t_2)` to
  `2·10⁻¹³`. The true tail between `2^24` and `2^25` is `2.2·10⁻¹³`, well
  under the bound (36), `1.51·10⁻⁹`.
- **The operator.** A direct floating evaluation of `T1(t_i)` from (21),
  using no package code, gives values inside the certified enclosures.
- **Exact reconstruction of the receipts.** The check rebuilt `S_3`, `I_1`,
  `I_2`, the gap (37), `R_1`, `R_2` and `2g/(R_1+R_2)` from the stored
  endpoints, in exact rationals and with its own code. All agree with the
  receipts and the printed decimals.
- **Reruns.** The delivered chain (all steps except the radial sieve) was
  rerun on a copy. Every receipt equals its delivered version; the combined
  receipt differs only in its recorded input hashes.
- **Also confirmed:**
  - the OEIS data and both fixtures;
  - the inverse constants of (73);
  - the provenance figures, the manifest (36 entries) and the byte identity
    of the 33 staged files;
  - the README listing;
  - the numbering (95 labels unchanged, 3 added).

Nothing needed correcting. Rebuilt: 26 pages (25), label numbers unchanged.

## Build

pdfLaTeX (lmodern, microtype, amsmath, amssymb, amsthm, mathtools, booktabs,
array, longtable, geometry, hyperref, fancyhdr). In a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX pdfLaTeX (7 October 2026;
rebuilt after the independent check, three passes): 26 pages (25 at the
write); no errors or warnings, no undefined references, no multiply defined
labels, no duplicate destinations, no overfull or underfull boxes. The
delivered text gives 21 pages with no warnings.

## Provenance

- Batch 112 of `docs/incoming`: bundle Report 215 (arrival `60f54ea06`),
  placed unprefixed by `f79c9bef1`; written 7 October 2026.
- Sources cited by the report: OEIS A003238, A003318, A018819, A000123;
  Erdős–Loxton (1979); Gol'dberg–Livshits (1968); Gati–Harary–Robinson
  (1982); Harary–Robinson (1975); Mahler (1940); de Bruijn (1948);
  Dumas–Flajolet (1996); Banderier–Hwang–Ravelomanana–Zacharovas (2014); and
  the repository's transseries volume (added by the write).
