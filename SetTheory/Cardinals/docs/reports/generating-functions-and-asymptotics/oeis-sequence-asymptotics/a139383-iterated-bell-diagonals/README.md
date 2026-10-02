# Asymptotics of Iterated Bell Diagonals (OEIS A139383, A261280)

**Fixed depth shifts and proportional depth**

This research report was built on 2 October 2026 from two manuscripts of
batch 77. Both are dated 2 October 2026, both have an empty author line, and
neither names a tool or a person or says whether it was produced with AI
assistance. Here `H(n,m) = n! [z^n] (e^z − 1)^{∘m}` are the iterated
(higher-order) Bell numbers; A139383 is `H(n,n)` and A261280 is `H(n,n+1)`.

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 53 | 53 | `oeis-iterated-bell-report-attribution-revised.zip` (`iterated-bell.tex`, 410 lines, with `inverse-section.tex`; 12-page PDF) | none | `aa7345800` | Part I, Sections 1–9 |
| 28 | 28 | `iterated-bell-proportional-addendum.zip` (`proportional-depth.tex`, 428 lines; 11-page PDF) | none | `aa7345800` | Part II, Sections 10–18 |
| 54 | 54 | `oeis-iterated-bell-report.zip` (`iterated-bell.tex`, 392 lines; 11-page PDF) | none | not staged (superseded) | contained in Part I |

All three archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive>.zip > <scratch>/<archive>.zip`).

- **54 is superseded by 53.** Manuscript 53 is the "attribution corrected"
  revision of 54: a `diff` has four hunks, replacing four lines by twenty-two
  (the abstract, the subsection "Historical attribution", the
  research-question sentence and two bibliography entries). The rest of the
  text, `inverse-section.tex`, the programs, the recorded results and the
  certificate are byte-identical. Every sentence of 54 is therefore in Part I,
  and nothing of 54 was staged.
- **28 embeds 53.** Archive 28 carries archive 53 whole, byte for byte, under
  `dependencies/foundation/` (31 files), plus one file found nowhere else, a
  pre-release diagnostic, shipped as
  `data/28-proportional-foundation-recurrence-original.json`. The placement
  staged 53's files once, from archive 53.

Every result, proof, remark, question and limitation of 53 and 28 is printed.
Source 28's Section 2 restated 53's fixed-contour lemmas; it is replaced by a
list of pointers to Part I that keeps the three displays Part II's proofs
cite (see "Where the merge had to choose").

**Status: unrefereed, not formalized; AI assistance not stated by the
sources.** Both sources report independent mathematical review and replay of
their checks and say that this "is not proof-assistant verification". Part II
is conditional on Part I and its certificate.

## Files

```
article.tex        the merged report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 30 pages (title, abstract and contents 1–2,
                   Guide 2–7, Part I 8–19, Part II 20–30)
README.md          this guide
inverse-section.tex  source 53's \input file, as delivered; printed inline as
                   Section 7 of article.tex and no longer \input (its labels are unprefixed)

Source 53 (Part I), files from oeis-iterated-bell-report-attribution-revised.zip
53-iterated-bell-CHANGE-NOTE.md                    the attribution correction (53 versus 54)
53-iterated-bell-VERIFICATION.md                   verification scope and executable-check record
53-iterated-bell-mathematical-review.md            independent mathematical and software review
53-iterated-bell-interval-certificate.md           review of the interval certificate
53-iterated-bell-attribution-review.md             source-specific attribution review
53-iterated-bell-source-NOTICE.md                  OEIS attribution and CC-BY-SA-4.0 notice for the .seq files
code/53-iterated-bell-replay.py                    replay driver (delivered layout; see "Rerunning")
code/53-iterated-bell-check_recurrence.py          exact recurrence, official terms, small EGF checks
code/53-iterated-bell-generate_coefficients.py     exact rational coefficient and Abel-remainder generator
code/53-iterated-bell-verify_amplitude.py          2048-panel outward-interval certificate, 214/100 < J < 243/100
code/53-iterated-bell-explore_amplitude.py         exploratory long-double contour values (not certified)
code/53-iterated-bell-build.sh                     delivered PDF build of iterated-bell.tex (do not run here)
data/53-iterated-bell-recurrence.json              recurrence check output, n <= 260
data/53-iterated-bell-recurrence-check.txt         byte-identical copy of the previous file
data/53-iterated-bell-coefficients.json            generator output, order 3
data/53-iterated-bell-coefficient-generation.txt   byte-identical copy of the previous file
data/53-iterated-bell-amplitude-original.txt       certificate run: checkpoints and CERTIFIED line
data/53-iterated-bell-exploratory-amplitude.json   three exploratory contour runs, C = 2.865407977-2.865407994 (not certified)
data/53-iterated-bell-producer-replay.txt          producer's run of replay.py (about 36 s)
data/53-iterated-bell-runtime.json                 Python 3.12.14, mpmath 1.3.0, SymPy 1.14.0
data/53-iterated-bell-review-frozen-sources.json   hashes of the reviewed revised sources (delivered names)
data/53-iterated-bell-review-original-frozen-sources.json  the same for the first edition (54)
data/53-iterated-bell-source-A139383.seq           official OEIS export (CC-BY-SA-4.0, see NOTICE)
data/53-iterated-bell-source-A261280.seq           official OEIS export (CC-BY-SA-4.0, see NOTICE)

Source 28 (Part II), files from iterated-bell-proportional-addendum.zip
28-proportional-QA.md                              final production and verification record
28-proportional-final-source-audit.md              final integrated source review (PASS, conditional)
28-proportional-audit-audit.md                     independent audit of the proportional extension
28-proportional-audit-reviewed-proportional-depth.md  the frozen research draft that audit reviewed
28-proportional-sources-README.md                  research-package readme
28-proportional-sources-proportional-depth.md      research note (later wording than the reviewed draft)
28-proportional-sources-literature.md              source audit: Prellberg, Skau-Kristensen, CMM, Nagaev-Vakhtel, OEIS
28-proportional-sources-PRIMARY-SOURCES.md         primary-source URLs and hashes (third-party PDFs not shipped)
code/28-proportional-replay.py                     replay driver (delivered layout; see "Rerunning")
code/28-proportional-generate_coefficients.py      byte-identical to code/53-iterated-bell-generate_coefficients.py
code/28-proportional-generate_proportional.py      general-beta integrand polynomials through order 3
code/28-proportional-check_coefficients.py         the auditor's original check (hard-coded /workspace paths)
code/28-proportional-check_coefficients_portable.py  the same check with --base/--out arguments
code/28-proportional-check_proportional.py         exploratory contour quadrature and exact ratios (not certified)
data/28-proportional-orbit-coefficients.json       byte-identical to data/53-iterated-bell-coefficients.json
data/28-proportional-proportional-coefficients.json  general-beta polynomials, order 3
data/28-proportional-coefficient-checks.json       the audit's independent check output
data/28-proportional-diagnostics.json              exploratory diagnostics (not_certified: true)
data/28-proportional-exact-replay.txt              producer's run of replay.py
data/28-proportional-runtime.json                  Python 3.12.14, SymPy 1.14.0, pdfTeX
data/28-proportional-manifest.json                 package manifest: roles and SHA-256 of the delivered files
data/28-proportional-foundation-recurrence-original.json  pre-release diagnostic (first ten terms, float amplitudes)
data/28-proportional-search-control-query-summary.json   OEIS control query (1,2,12,154,3455 -> A139383)
data/28-proportional-search-1_4_51_1380_64660.txt         OEIS search, no result ("null")
data/28-proportional-search-1_5_70_1989_95986.txt         OEIS search, no result ("null")
data/28-proportional-search-15_52_2471_19302_1855570.txt  OEIS search, no result ("null")
```

Delivery names of the renamed files: every `53-iterated-bell-` and
`28-proportional-` file is the delivered file of the same base name, from the
delivered directory `verification/`, `results/`, `review/`, `source/` or
`sources/` (for example `review/proportional-audit/audit.md` →
`28-proportional-audit-audit.md`, `results/coefficients.json` →
`data/53-iterated-bell-coefficients.json`). Source 53's `iterated-bell.tex` is
now `article.tex` (rewritten as this report); the three search-evidence files
were named `sources/search-evidence/1%2C4%2C51%2C1380%2C64660.txt` and so on
(`%2C` became `_`).

Not shipped (all survive in `096ee7b87`): the three delivered PDFs, both
delivery READMEs (this README replaces them), 28's `proportional-depth.tex`,
`build.sh`, `results/compile.log` and `results/pdfinfo.txt`, 28's embedded copy
of 53, all checksum ledgers (`SHA256SUMS`, `review/FROZEN_SHA256SUMS`,
`review/ORIGINAL_FROZEN_SHA256SUMS`, 53's `manifest.json`, 28's
`review/FINAL_SOURCE_SHA256SUMS` and `review/proportional-audit/SHA256SUMS`;
all verified at placement), and all 28 files of 54. Nothing was excluded as a
heavy artifact: the largest shipped data file is 15 KB.

## Labels and numbering

Every label in `article.tex` carries the prefix `ibd:` (100 labels).

- Part I: source 53's 39 labels (34 in `iterated-bell.tex`, 5 in
  `inverse-section.tex`) as `ibd:<name>`, plus 16 new ones (`ibd:part:diag`,
  `ibd:part:pd`, six section labels `ibd:sec:*`, eight Guide labels
  `ibd:guide*`): 55.
- Part II: 43 of source 28's 52 labels as `ibd:pd:<name>`, plus
  `ibd:pd:sec:statement` and `ibd:pd:sec:prellberg`: 45. The nine dropped
  labels belonged to displays that restated Part I and were replaced by
  references to it: `eq:defH`, `eq:recurrence` (Section 10) and `eq:residue`,
  `eq:stieltjes`, `eq:fatou`, `eq:psi`, `eq:contourfinite`, `eq:K`,
  `eq:remainder` (Section 11).

Part I has source 53's numbers: Sections 1–9, Theorem 1.1, Lemmas 2.1–2.2 and
equations (1)–(32), checked against a build of the delivered source. Source
28's Section *n* is Section *n* + 9 and its Theorem 1.1 and Propositions 4.1,
6.1 are Theorem 10.1 and Propositions 13.1, 15.1. Its equations continue Part
I's numbering: its (3)–(5) are (33)–(35), (12)–(14) are (36)–(38), and (*k*)
for *k* ≥ 16 is (*k* + 23). The shipped reviews cite the delivered numbers
(for example, `53-iterated-bell-attribution-review.md` calls the historical
specialization "equation (32)", which it still is).

## What is proved, and what is not

- **Part I (source 53).** For each fixed integer *k* and every *M*,
  `H(n,n+k) = e^k C n^{2n−5/6} / (2^{n−1} e^n) · (1 + Σ_{j≤M} P_{j,k}(log n)/n^j + O((1+log n)^{D_M}/n^{M+1}))`,
  with explicit polynomials of degree at most 2*j*, the amplitude
  `C = √(2π) I_0 / 2` defined by a fixed contour of radius 1/2, and the
  certified enclosure **2 < C < 4** (from 2.14 < J < 2.43 for the outer
  contour and an analytic cut bound below 1/2). A261280/A139383 → *e*. Also:
  an effective Fatou coordinate with explicit rational Abel-remainder
  constants, the shift rule and first correction, the Galton–Watson
  factorial-moment interpretation, smooth inverses to every finite order and a
  safe integer bracket for the threshold.
- **Part II (source 28).** For integer depth `m = λn + δ`, every fixed order,
  uniformly for λ in a compact subset of (0,∞) and bounded δ, with amplitude
  `D(λ) = √(2π) λ^{−1/(3λ)} I(1/λ)`, `D(1) = 2C`; `I` is real analytic and
  strictly positive on (0,∞) (an exact quadratic composition inequality plus
  the single certified seed `I(1) > 1.64`); the floor-depth phase
  `e^{−{λn}/λ}`, the shift ratio `e^{r/λ}`, eventual monotonicity of
  `H(n,⌊λn⌋)`, the first correction, and smooth inverses with the warning
  against holding δ_n constant.
- **Not claimed.** No priority for the leading formulas, the parabolic
  method or the displayed coefficients (Prellberg's FPSAC 2002 slides and
  Mishna's 2005 summary already state the pre-sum bivariate formula; both
  sources say so, and the report prints both statements verbatim). The digits
  `C ≈ 2.86540798` are exploratory and not certified. The certificate relies
  on the outward-rounded operations of `mpmath.iv` (tested with mpmath 1.3.0
  and Python 3.12.14), not on a verified arithmetic kernel. The expansions are
  finite-order Poincaré expansions, not transseries; no sharp remainder
  degree, no instantiated remainder constants, no numerical threshold
  certificate, no canonical interpolation of the integer sequence. Part II
  claims no uniformity as λ → 0 or ∞ and no certified amplitude values away
  from λ = 1. OEIS "conjecture" labels (as retrieved on 2 October 2026) are not
  treated as evidence of novelty.

## Where the merge had to choose

1. **Base.** 53 is Part I because 28 is written on it.
2. **Source 28's Section 2** (four pages restating 53's Sections 2–6 from the
   embedded copy) became Section 11, a list of pointers to the Part I labels,
   keeping 28's three cited displays (`ibd:pd:eq:entry`,
   `ibd:pd:eq:realbound`, `ibd:pd:eq:seed`) and its non-restating sentences.
   The definition of `H` and the recurrence in 28's Section 1 now refer to
   Part I's (1) and (2). 28's restatements in its own variables of the orbit
   recursion and of the real functional are kept, with notes naming the Part I
   originals.
3. **Both literature sections are printed in full.** Each derives the same
   specialization of Prellberg's formula, but each carries its own non-claims
   and comparisons; 28's adds the general recurrence, `I(β) = β J_P(β)` and the
   slope-λ prefactor.
4. **One renamed symbol.** Prellberg's contour integral, `J(β)` in both
   sources, is `J_P(β)`, to separate it from the certified outer contribution
   `J` (source 53 used `J` for both). The Guide's notation table lists the
   other overloaded letters (`C` versus `D(1) = 2C`, `k` versus δ, `μ_j`,
   `R_j`, `Z`, `q`, `c`, `d`, …) with the readings to avoid.
5. **Citations of the package.** 28's `\cite{foundation}` became references
   to Part I and `\cite{audit}` the shipped `28-proportional-audit-audit.md`.
   28's running header is dropped. The two bibliographies are merged; the
   Nagaev–Vakhtel DOIs agree (53's `10.1163/…` redirects to 28's
   `10.1515/…`).

Dated `[write, 2 October 2026]` notes: Part II's answer to 53's first
research question (compact slope ranges; the endpoint regimes and the other
three questions remain open); the Takeuchi report's copy of the
Prellberg-limitation check; the status of 53's repository search; the
transseries-volume instances in both inverse sections; the unpacking of each
package in this directory; the Part I originals of 28's restated displays.

## Relation to the repository

- **Takeuchi numbers.**
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000651-takeuchi-numbers`
  (batch 77, cluster P3) prints the same counterexample to Prellberg's broad
  printed theorem (`f(z) = z/(1−z)`, `a(z) = z`, `b(z) = 1` gives `B_{n−1}`,
  not the `B_n` scale) in its subsection "A limitation of the printed general
  theorem". Part I keeps its own one-paragraph check, with a note pointing
  there.
- **Inversion.** Both inverse sections are instances of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`
  (`p0:thm:lambert-core`, `p0:thm:perturbed-inversion`, `p0:thm:staircase`;
  the Fatou logarithm is the model case of `plt:ex:mot-parabolic`). No novelty
  is claimed for the inversion mechanics.
- **Neighbours.** `a088714-bell-scale-growth` (same directory) iterates a
  different series and shares no theorem.
  `SetTheory/Cardinals/docs/reports/congruences-and-valuations/iterated-series/a168362-lacunary-iterates-mod4`
  has the same shape `[x^n]F^{∘n}(x)`, and its open
  `lim:conj:refined-asymptotic` is "suggested by parabolic iteration theory";
  this report's method is a candidate there, with no claim.
  `a277364-bell-asymptotics` is unrelated.
- **Formal status.** No Lean or Rocq development in ProveIt concerns these
  sequences, and no statement of this report is formalized.

## Delivered files that use delivery names, and other discrepancies

The shipped delivered files are byte-identical to the delivery. Their text
uses the delivered layout and names:

- `53-iterated-bell-CHANGE-NOTE.md` records the SHA-256 of the first edition's
  ZIP and PDF (archive 54, not shipped). `53-iterated-bell-VERIFICATION.md`,
  `53-iterated-bell-mathematical-review.md` and
  `53-iterated-bell-attribution-review.md` name `README.md`,
  `iterated-bell.tex`, `iterated-bell.pdf`, `CHANGE-NOTE.md`,
  `review/attribution-review.md`, `frozen-sources.json`,
  `original-frozen-sources.json`, `results/coefficients.json` and
  `verification/replay.py`; the attribution review's "Frozen identities" are
  the SHA-256 of the delivered `iterated-bell.tex`, PDF, README and change
  note, which this report does not reproduce (`article.tex` and `README.md`
  are rewritten, the PDF is not shipped). Its page references ("page 1 and
  pages 10–12") are to the delivered PDF.
- `data/53-iterated-bell-review-frozen-sources.json` and
  `…-original-frozen-sources.json` hash the delivered files under their
  delivered names; the second one describes the first edition (54).
- `28-proportional-audit-audit.md` says the foundation it used is
  `/workspace/shared/oeis-iterated-bell-report/iterated-bell.tex`, a path in the
  producer's workspace named like archive 54. The mathematics of 53 and 54 is
  byte-identical (see above), so the audit applies to Part I either way.
- `28-proportional-sources-README.md` names the audit as
  `/workspace/shared/iterated-bell-proportional-audit/audit.md` (shipped as
  `28-proportional-audit-audit.md`) and the research files by their
  research-directory names.
- `28-proportional-sources-literature.md`, line 61, cites
  `/workspace/shared/oeis-takeuchi-asymptotics-result/takeuchi-asymptotics.tex`,
  subsection "A limitation of the printed general theorem". That is batch-77
  manuscript 65, now
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a000651-takeuchi-numbers/article.tex`.
  The same file and `28-proportional-sources-PRIMARY-SOURCES.md` name saved
  third-party PDFs (`prellberg2002-slides.pdf`, `nv2003.pdf`, …) that were
  never delivered; only their URLs and hashes are given.
- `28-proportional-QA.md` and `28-proportional-final-source-audit.md` name
  `results/compile.log`, `results/pdfinfo.txt`, `proportional-depth.tex` and
  `FINAL_SOURCE_SHA256SUMS`, none of which is shipped, and describe the
  delivered 11-page PDF.
- `data/28-proportional-manifest.json` lists every delivered file of archive
  28, including the embedded `dependencies/foundation/` copy, under delivered
  names.
- The research notes `28-proportional-sources-proportional-depth.md` and
  `28-proportional-audit-reviewed-proportional-depth.md` are two snapshots of
  the same draft (the reviewed one, and one with later attribution and
  contour wording); the article supersedes both.
- `inverse-section.tex` is kept as delivered but is no longer `\input`; its
  labels lack the `ibd:` prefix and its `\eqref{eq:main}`, `\eqref{eq:rec}`
  refer to source 53's numbering.

## Building the PDF

```
cd <scratch>
cp <this directory>/article.tex .
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with the packages loaded in the preamble (geometry, lmodern,
microtype, amsmath, amsthm, mathtools, booktabs, longtable, array, enumitem,
hyperref). The committed build has 30 pages, no errors, no undefined or
multiply defined references, and no overfull boxes. Do not run
`code/53-iterated-bell-build.sh`: it builds the delivered `iterated-bell.tex`
and writes `.build/` and a PDF beside itself.

## Rerunning the checks

Never run the programs inside this directory: `explore_amplitude.py`
writes `contour-longdouble-diagnostics.json` beside itself,
`check_proportional.py` writes `diagnostics.json` beside itself,
`generate_proportional.py` reads and writes beside itself, and
`28-proportional-check_coefficients.py` reads and writes hard-coded
`/workspace/shared/…` paths. The replay drivers expect the delivered layout.
Rebuild it in a scratch directory (paths below are relative to this report
directory), then compare outputs with the shipped files modulo CR on Windows.

**Source 53** (`verification/replay.py`; Python 3.12, mpmath 1.3.0, SymPy):

| copy from | to `<scratch>/` |
|---|---|
| `code/53-iterated-bell-replay.py` | `verification/replay.py` |
| `code/53-iterated-bell-check_recurrence.py` | `verification/check_recurrence.py` |
| `code/53-iterated-bell-generate_coefficients.py` | `verification/generate_coefficients.py` |
| `code/53-iterated-bell-verify_amplitude.py` | `verification/verify_amplitude.py` |
| `code/53-iterated-bell-explore_amplitude.py` | `verification/explore_amplitude.py` (optional; NumPy, SciPy) |
| `data/53-iterated-bell-source-A139383.seq` | `source/A139383.seq` |
| `data/53-iterated-bell-source-A261280.seq` | `source/A261280.seq` |

Then `cd <scratch>` and `py verification/replay.py` (or
`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 python verification/replay.py`).
Without `manifest.json` (not shipped) the replay skips its manifest check. It
writes its outputs to a temporary directory and prints them; compare with
`data/53-iterated-bell-recurrence.json`, `…-coefficients.json` and
`…-amplitude-original.txt` (the certificate must end with
`CERTIFIED: 214/100 < J < 243/100`). The producer's run took about 36 s
(`data/53-iterated-bell-producer-replay.txt`). On this laptop under load,
`check_recurrence.py --max 260` took 78 s and `generate_coefficients.py
--order 3` 73 s, both reproducing the shipped JSON exactly; the interval
certificate was stopped after 512 of 2048 panels with its checkpoints
digit-identical to the shipped ones, so the final `CERTIFIED` line was not
rerun here.

**Source 28** (`verification/replay.py`; Python 3, SymPy):

| copy from | to `<scratch>/` |
|---|---|
| `code/28-proportional-replay.py` | `verification/replay.py` |
| `code/28-proportional-generate_coefficients.py` | `verification/generate_coefficients.py` |
| `code/28-proportional-generate_proportional.py` | `verification/generate_proportional.py` |
| `code/28-proportional-check_coefficients_portable.py` | `verification/check_coefficients_portable.py` |
| `code/28-proportional-check_proportional.py` | `verification/check_proportional.py` (only for `--diagnostics`) |
| `data/28-proportional-orbit-coefficients.json` | `results/orbit-coefficients.json` |
| `data/28-proportional-proportional-coefficients.json` | `results/proportional-coefficients.json` |
| `data/28-proportional-coefficient-checks.json` | `review/proportional-audit/coefficient-checks.json` |

Then `cd <scratch>` and
`uv run --no-project --with sympy==1.14.0 python verification/replay.py`. It
works in a temporary directory and compares against the three copied JSON
files. This recipe was run on a copy when the report was written: it printed
`PASS: exact orbit JSON, general-beta JSON, and independent coefficient checks
agree.` in 71 s. The optional `--diagnostics` (NumPy, SciPy, mpmath;
exploratory, not certified) was not run.

To work from the delivery itself instead, extract the archives from the
arrival commit
(`git show 096ee7b87:docs/incoming/oeis-iterated-bell-report-attribution-revised.zip`,
`git show 096ee7b87:docs/incoming/iterated-bell-proportional-addendum.zip`)
into a scratch directory and follow the delivered READMEs there.
