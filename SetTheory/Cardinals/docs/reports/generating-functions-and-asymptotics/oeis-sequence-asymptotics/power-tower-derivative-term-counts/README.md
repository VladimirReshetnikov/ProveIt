# Term counts in the derivatives of power towers

**One framework and three sequences: OEIS A293239 (`x^x`), A290268 (`x^(x^2)`), A281434 (`x^(x^x)`), with depth certificates for A290268 at logarithmic deficits 3 and 4**

**What this report is.** One article covering three OEIS sequences that ask the
same question about three different functions:

| Sequence | Function | The question |
|---|---|---|
| [A293239](https://oeis.org/A293239) | `x^x` | how many distinct monomials are in the fully collected `n`-th derivative? |
| [A290268](https://oeis.org/A290268) | `x^(x^2)` | the same |
| [A281434](https://oeis.org/A281434) | `x^(x^x)` | the same |

The three were written as separate reports and are merged here because they
share a setup, not because they share a result. **They reach three different
answers by three different recurrences**, and the article keeps all three
intact. What is proved once instead of three times is the common machinery:
the canonical differential-polynomial form, the uniqueness of that form, the
transition recurrence it obeys, and the reduction of "count the terms" to
"count the nonvanishing coefficients". That is Part 1 (Section 1). Parts 2, 3
and 4 are the three investigations; Section 5 compares them. A fourth
manuscript, on A290268 only, was written into the end of Part 3 on
29 September 2026 as Sections 3.14–3.26.

**Status.** AI-assisted research notes. Unrefereed. Nothing in this report is
formalized; see "Relation to the Lean development" below for what the nearby
Lean development does and does not prove.

## Sources

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Cardinals-era delivery | `A293239_research_report.zip` (16-page article) | not recorded | merged in `630e041e5` (Cardinals history, brought in by `dc54c3cb3`) | Part 2 (Section 2) |
| 01 | Cardinals-era delivery | `A290268_partial_results.zip` (15-page article) | not recorded | as above | Part 3, Sections 3.1–3.13 |
| 01 | Cardinals-era delivery | `A281434_exact_algorithm_and_cubic_growth.zip` (17-page article) | not recorded | as above | Part 4 (Section 4) |
| 02 | batch 42, manuscript 06 | `ProveIt_A290268_Finite_Certificates.zip` (*From Infinite Nonvanishing to Finite Certificates: Bulk positivity, fixed-depth finiteness, and a four-depth solution for OEIS A290268*, 22-page PDF, dated 29 September 2026) | `afb2d1227` | `3609d0473` | Part 3, Sections 3.14–3.26 |

The first three rows are the original merge; `MERGE_EDITS.md` records every
edit made to them, and all fifty of their theorems, lemmas, propositions,
corollaries, definitions, conjectures and remarks are present with their
statements unchanged. Part 1 and Section 5 were written for the merge.

Source 02 (manuscript 06) is printed in full: every theorem, proposition,
lemma, corollary, definition, remark and research question, with its proofs
and its non-claims. It was written against the repository note
`Oeis/A290268/README.md` and the conditional Lean reduction, and **never read
this report**. Its bulk positivity, symmetry holes, depths one and two, upper
bound, depth bridge and linear independence therefore re-derive Part 3's
Theorem 3.7, Theorem 3.11, Theorems 3.16–3.17, Theorem 3.14, Proposition 3.4
and Lemma 3.2; they are printed as marked second routes, with Part 3
credited. Its manuscript, README, PDF and `SHA256SUMS.txt` (10/10 verified at
placement) are not shipped; the archive survives in the history of
`8315d24e3`. Where the write had to choose: the addition is placed as
subsections at the end of Part 3, not as a new part, so that no existing
section, theorem or equation number moved (checked against the `.aux` of a
build of the previous text: 0 of 217 labels changed number); the manuscript's
letters are kept, with a dictionary; three editorial remarks (3.31, 3.42,
3.46) are marked as additions of the intake.

## Status of each headline question — read this first

**None of the three headline questions is fully settled here, and this report
does not pretend otherwise.** Two of the three OEIS entries print a conjectured
closed form, and neither is proved. The third prints no closed form; there the
growth *order* is settled and the constant is not — and the obstruction is a
different kind of statement, because further zeros provably exist and the open
question is only how many.

- **A293239 (`x^x`): the principal all-order closed formula is NOT proved.**
  Its precise missing nonvanishing statement is isolated. What *is* proved
  unconditionally: the term count reduces exactly to zeros of the first-kind
  Lehmer–Comtet triangle [A008296](https://oeis.org/A008296), giving
  `a(n) = 1 + n(n+1)/2 - Z(n)`; and `n + 1 + floor(n^2/4) <= a(n) <= q(n)`, so
  `a(n) = Theta(n^2)`. Separately, **the recurrence printed in the OEIS entry
  with the range `n > 6` is disproved at `n = 8`** (the recurrence gives 36,
  the true value is 35). For the proposed sequence `q` the recurrence holds for
  every `n >= 14` and fails at `n = 13`; asserting the corrected range for the
  actual derivative count remains conditional on the principal conjecture.

- **A290268 (`x^(x^2)`): the OEIS conjecture is NOT proved.** What is proved:
  the conjectured expression `U(n)` is an *upper* bound; every predicted
  cancellation is explained; positivity holds on a large coefficient region;
  there are no further zeros on the first **four** logarithmic-deficit
  diagonals (deficits 1 and 2 in Part 3 as first written; deficits 3 and 4 in
  Sections 3.14–3.26, by an effective infinite-to-finite reduction plus exact
  finite certificates); and `Lambda(n) <= a(n) <= U(n)` with
  `Lambda(n) = (3n^2+10n+8)/8` for even `n` and `(3n^2+12n+1)/8` for odd `n`,
  so `a(n) = Theta(n^2)`. The addition improves the lower bound (Corollary
  3.45, Remark 3.46) to `(3n^2+26n-72)/8` for even `n >= 8` and
  `(3n^2+28n-111)/8` for odd `n >= 17` — a gain of `2n-10`, resp. `2n-14`, in
  the linear term only; the leading constant `3/8` is unchanged, and the
  proposed leading constant `1/2` is not established. The certified finite
  range `a(n) = U(n)` for `n <= 3000` (Proposition 3.18) is unchanged. **The
  open region is now logarithmic deficit `m = k - j >= 5`, `n >= 2k + 2`**,
  away from the reflection zeros; at every fixed `m >= 3` it is reduced to
  finitely many cells, with bounds far too large to compute.

- **A281434 (`x^(x^x)`): the growth order is settled; the constant is not.**
  For `n >= 1`, with `eps = 1` for odd `n` and `0` otherwise,

      (7n^3 + 39n^2 + 26n + 3*eps*(n-1))/24  <=  a(n)  <=  (2n^3 + 3n^2 + 4n)/3

  hence `a(n) = Theta(n^3)`. The sharper equivalent `a(n) ~ (2/3)n^3` is **not**
  proved; it would need the deficit from the upper polynomial to be `o(n^3)`.

Every finite computation in this report certifies a range or a finite list of
cells. None of them is by itself an all-`n` proof, and each verifier says so in
its own output. The depth-3 and depth-4 certificates of Sections 3.14–3.26
decide every `n` only because a proved reduction (Proposition 3.41) shows the
finite rectangles to be exhaustive; the rectangles themselves reach only
derivative order `n <= 359`, inside the range `n <= 3000` that Part 3's
modular certificate already covers. What that certificate does not supply is
the six seed *signs* the reduction needs.

## What is not claimed

- No closed formula for any of the three sequences, and no leading constant
  for A290268 or A281434.
- For A290268: nothing at deficits `m >= 5` beyond the finite range
  `n <= 3000` and the per-depth finiteness theorem; the manuscript's general
  bounds `K_d`, `Q_d` are "deliberately crude" and not claimed practical.
- The manuscript's zero-count bound (at most `d` real zeros per row of the
  Mellin interpolant) is not an integer nonvanishing statement.
- No priority: manuscript 06's literature and repository checks are "not a
  comprehensive historical-priority search"; Meixner–Pollaczek theory and the
  reflection, covariance and Chebyshev-system arguments are classical.
- No Lean or Rocq verification, no referee, no independent human review.

## A warning about notation

The parts keep the notation of their sources, which is *not* consistent
between them, because silently rewriting 2,600 lines of dense manipulation is a
worse risk than declaring the clash. Three collisions matter more than the rest:

- **`j` changes role.** In Parts 2 and 3 it is the exponent of `log x`. In
  Part 4 it is the exponent of `x^-1`, and `l` is the logarithm exponent. Every
  envelope and every bound in Part 4 is indexed the second way.
- **`z` has three meanings.** It is `x^2` in Part 3 and `log x` in Part 4 — a
  direct contradiction — and in Part 2 it is neither, but the formal variable
  in which the Lehmer–Comtet numbers are defined.
- **Sections 3.14–3.26 swap `j` and `k`.** They use the depth coordinates of
  manuscript 06 and of the Lean development: **`k` is the exponent of
  `log x`** (Part 3's `j`), `j` is the exponent of `x` in `x^(x^2+j)`, `d` is
  the logarithmic deficit (Part 3's `m`, *not* Part 3's `d = n-2k-1`, which is
  the addition's `q`). Table 3 of the article gives the full dictionary with
  the false readings, and lists the symbols renamed from the manuscript
  (`P_d -> Pi_d`, `Q_k^(r) -> calQ_k^(r)`, `A_{M,k} -> calA_{M,k}`,
  `B_d(r) -> calB_d(r)`, `B(N) -> beta(N)`, `L -> tau`, `h_d(N) -> chi_d(N)`,
  `m -> nu_d` and `rho`, `F_{d,k} -> calF_{d,k}`, series variable `z -> xi`;
  no normalization changed).

§1.5 of the article gives the three canonical monomials side by side, and is
explicit that many other letters (`u`, `v`, `t`, `q`, `U`, `Z`, `E`, `Δ`) are
reused across parts with unrelated meanings. `a(n)` denotes a different
sequence in each part.

## Labels

Labels carry a per-part prefix: `fw:` (Part 1), `xx:` (Part 2), `xxb:`
(Part 3), `xxc:` (Part 4), `syn:` (Section 5). The batch-42 addition uses the
sub-prefix **`xxb:dc:`** (85 labels). The article has 304 `\label`s (219
before the addition); none was renamed or removed. No label here has a Lean
mapping.

## Files

```
README.md                                         this guide
article.tex                                       the article (pdfLaTeX, internal bibliography)
article.pdf                                       the compiled article, 80 pages (A4)
MERGE_EDITS.md                                    every edit made to the three original texts in the merge
A293239_oeis_notes.txt                            statement of the x^x recurrence-range correction
A290268_result_status.json                        Part 3's machine-readable status, as delivered (stale; see below)
02-depth-certificates-SOURCE_AUDIT.md             manuscript 06's source and proof-boundary audit, as delivered
CODE_LICENSE.txt                                  license for the code (shipped with the A281434 group)
Makefile, build.sh, build.ps1                     article build and the original verification targets
requirements-optional.txt                         optional NumPy for the A281434 modular path
code/verify.py, code/verify_diagonals.py          A293239 (Part 2) verifiers
code/verify_gmp.cpp                               A293239 compiled exact verifier
code/verify_exact.py, code/verify_modular.cpp     A290268 (Part 3) exact and modular verifiers
code/combine_certificates.py                      A290268 certificate combiner
code/a281434.py, code/test_a281434.py,
code/run_experiments.py                           A281434 (Part 4) algorithm, tests, experiments
code/02-depth-certificates-verify.py              manuscript 06: full exact verifier (writes nothing unless --write-data)
code/02-depth-certificates-minimal_verify.py      manuscript 06: standalone verifier printed in Section 3.25.2
code/02-depth-certificates-Makefile               manuscript 06's delivered Makefile (do not use; see below)
data/02-depth-certificates-finite_certificate.csv all 16,034 rectangle cells: sign, reduced sign, residues mod 1009, 1013 (CRLF)
data/02-depth-certificates-sign_thresholds.csv    observed sign transitions per tested row (CRLF)
data/02-depth-certificates-verification.json      executed-check summary and exact seed integers
data/b281434.txt, data/b352697.txt, data/benchmarks.csv, data/counts.csv,
data/python_report.json, data/selected_holes.json, data/test_results.txt,
data/zeros.csv, data/environment.json             A281434 and A293239 outputs
data/diagonal_certificates.json, data/diagonal_report.txt,
data/gmp_report.txt                               A293239 diagonal and GMP outputs
data/exact_counts.csv, data/exact_run.log, data/exact_summary.json,
data/certified_counts.csv, data/certificate_run.log, data/certificate_summary.json,
data/modular_witnesses.csv, data/sample_coefficients.json,
data/watch_coordinates.csv                        A290268 exact and certificate outputs
data/p1000000007_{counts.csv,run.log,summary.txt,watches.csv,zeros.csv}
data/p1000000009_{counts.csv,run.log,summary.txt,watches.csv,zeros.csv}
                                                  A290268 modular runs, one set per modulus
```

That is all 58 files in the directory.

## Building

    sh build.sh            # three pdflatex passes
    make pdf               # the same, into build/, then copies article.pdf
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

The committed PDF was built with `latexmk` (pdfTeX, MiKTeX): 0 errors, 0
undefined references or citations, 0 multiply-defined labels, 0 duplicate
destinations, 0 LaTeX warnings; one overfull box (8.4 pt, in the Section 5
comparison table), present before the addition as well.

## Verifying

Run from the report root. Each script is independent of the others.

    python code/verify.py --max-n 1500              # A293239, exact
    python code/verify_diagonals.py                 # A293239, offsets 1..16
    python code/verify_exact.py --max-n 200 --formula-n 16   # A290268, exact
    python code/test_a281434.py                     # A281434, 10 regression groups
    python code/run_experiments.py                  # A281434, data + benchmarks

Optional compiled verifiers, both exact rather than probabilistic:

    g++ -O3 -std=c++17 code/verify_gmp.cpp -lgmp -o verify_gmp      # A293239
    g++ -O3 -std=c++17 code/verify_modular.cpp -o verify_modular    # A290268

`make verify` runs the A290268 exact and modular passes and the certificate
combiner. **Note that several of these rewrite files in `data/`**: `make verify`
tees its run logs there, and `code/verify.py` rewrites `data/python_report.json`.
The shipped `data/` is the output of a full run, so re-running is reproduction,
not corruption — but the files will change.

**Depth certificates (Sections 3.14–3.26).** Python 3.9 or later, standard
library only:

    py code/02-depth-certificates-minimal_verify.py   # prints PASS, writes nothing
    py code/02-depth-certificates-verify.py           # prints a JSON report with "status": "PASS", writes nothing

To regenerate the data, **work on a copy** of this directory:
`verify.py --write-data` writes the *unprefixed* files
`data/finite_certificate.csv`, `data/sign_thresholds.csv` and
`data/verification.json` next to the shipped prefixed ones. On the intake
copy both CSVs came out byte-identical to the shipped ones and the JSON
identical up to line endings (the suite writes CRLF on Windows). The
recomputed `H_{d,k,q}` of all 494 depth-3 cells and of 925 depth-4 cells were
also checked independently from the series definition in exact rationals,
with no mismatch. Do **not** use `code/02-depth-certificates-Makefile`: from
the report root its `verify` target runs `code/minimal_verify.py` (absent
under that name) and `code/verify.py` — the A293239 verifier of Part 2, which
rewrites `data/python_report.json` — and its `data` target does the same with
`--write-data`; its `all`/`clean` targets run `latexmk` on the merged
`article.tex`.

## What the modular verifiers do and do not do

Both compiled verifiers are exact. A nonzero residue certifies a nonzero
coefficient outright. Every *zero* residue inside the proved support envelope is
checked again with an exact integer formula rather than being accepted. Neither
is a probabilistic zero test. Manuscript 06's witnesses modulo 1009 and 1013
follow the same rule: a nonzero residue proves nonvanishing, and exact zeros
are the 48 symmetry holes, computed as exact integers by two independent
recurrences.

## Relation to the Lean development

Placement beside a Lean development confers no formal status. The Lean library
`A290268` (`Combinatorics/DerivativeExpansions/A290268/Lean`, namespace
`LeanProofs.A290268`, imported by the root `ProveIt.lean`) defines the
coefficient lattice `coeff n j k` by the recurrence of Section 3.15 in the
same `(j, k)` coordinates, and proves:

- `Count.card_S`: the conjectured support `S n` has cardinality `closedForm n`;
- `Table.a_values_le_53`: `a n = closedForm n` for `n <= 53` (`native_decide`);
- `Main.a_eq_closedForm_of_support`, `Main.a_eq_closedForm_of_two_sided`,
  `Main.a_eq_closedForm_of_support_all`: `a n = closedForm n` **conditional**
  on the support characterization (or its two inclusions). Manuscript 06
  relies on these statements and reads them as conditional;
- `Structural.mem_S_of_coeff_ne_zero`: the structural inclusion, conditional
  on a hypothesis `hhole` of vanishing on the hole line. That line is exactly
  the reflection family of Theorem 3.11 / Theorem 3.29, so either proof would
  discharge `hhole` on paper; neither is formalized, and the module
  `A290268.Hole` named in the declaration's docstring does not exist.

Theorem 3.23 (deficits 1–4) would discharge the nonvanishing inclusion only on
cells of depth at most four; the `Main` theorems stay conditional. None of this
report's theorems is formalized.

## Relation to neighbouring material

- `Oeis/A290268/README.md` (research notes, outside the collection) is the
  note manuscript 06 continued. It still calls the general-`k` bulk open and
  lists three Lean modules (`A290268.Hole`, `.DepthOne`, `.Series`) that never
  existed; both are stale with respect to this report. It is not edited here.
- `Combinatorics/ExpressionEnumeration/PowerTowers/` (power-tower *value*
  counts) is unrelated.

## Discrepancies and delivered-file disclosures

- `A290268_result_status.json` is Part 3's delivered status record and is kept
  byte-identical. Its `remaining_obligation` ("k-j >= 3 and n >= 2k+2") and
  `proved_results` predate the addition: the obligation is now `k-j >= 5`, and
  deficits 3 and 4 are classified (Theorem 3.23).
- `code/02-depth-certificates-minimal_verify.py` says in its docstring that it
  is the listing of "Appendix A of article.tex" (the manuscript's numbering;
  here Section 3.25.2). `code/02-depth-certificates-verify.py` gives
  `python3 code/verify.py` as its usage line and writes unprefixed file names
  under `--write-data`. `code/02-depth-certificates-Makefile` uses the
  delivery names throughout (see above).
- `02-depth-certificates-SOURCE_AUDIT.md` cites the pinned repository URLs of
  `afb2d1227`, calls the inspected note's general-`k` bulk open, and does not
  know this report; the article corrects this in Section 3.25.3.
- In Part 3's own reproduction listing (Section 3.12) the build commands still
  name the original `A290268_partial_results.tex`; the file is `article.tex`.

## Provenance

The three original reports were merged into one article on 20 September 2026
(`630e041e5`, Cardinals history) and brought into ProveIt with the Cardinals
repository (`dc54c3cb3`). Manuscript 06 of batch 42 arrived in `8315d24e3`,
was placed as an addition in `3609d0473` (staged files prefixed
`02-depth-certificates-`, byte-identical to the delivery), and was written
into Sections 3.14–3.26 on 29 September 2026, with dated notes pointing
forward from the abstract, the reading guide, §1.5, Part 3's status box,
Theorem 3.1, Section 3.7.4, the precise missing step (Section 3.10), Part 3's
conclusion and Section 5.

These are AI-assisted drafts. None is refereed or machine-checked.
