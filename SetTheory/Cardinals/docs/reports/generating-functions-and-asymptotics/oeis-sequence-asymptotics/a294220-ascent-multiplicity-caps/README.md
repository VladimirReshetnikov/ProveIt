# Ascent Sequences with Bounded Multiplicity (OEIS A294220)

**Factorial growth constants of every cap b ≥ 3, and fixed Taylor sectors of the large-cap expansion**

This research report was built on 2 October 2026 from two manuscripts of
batch 77, both dated 1 October 2026. Source 47 is the foundation; source 52
is its addendum. Author lines: "A proof and reproducible research report"
(47) and "A reproducible large cap addendum" (52). No tool or person is named.

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 47 | 47 | `oeis-bounded-multiplicity-family-report.zip` (`bounded-multiplicity-report.tex`, 612 lines, 13-page PDF) | none (identifies manuscript 37, the cap-two report, by SHA-256) | `aa7345800` | Part I, Sections 1–10 |
| 52 | 52 | `oeis-fixed-sector-addendum.zip` (`fixed-sector-addendum.tex`, 312 lines, 7-page PDF) | none (identifies source 47 by SHA-256) | `aa7345800` | Part II, Sections 11–16 |

Both archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive> > <scratch>/<archive>`). The
hashes that source 47 records for manuscript 37's delivered
`a202058-report.tex` and `.pdf`, and those that source 52 records for source
47's delivered `.tex` and `.pdf`, all match the delivered files (checked at
the write). Archive 52 does not bundle source 47.

Both manuscripts are printed in full. Source 52 re-derives source 47's first
variation (b+1)(ζ(b+2)−1) by another computation; it is kept as a marked
second proof. Source 52 shows that source 47's remainder bound
O(b^{5/2}(4/9)^b) is not sharp in its power of b (the true size is
(8/(9√π))√b(4/9)^b); both are printed, side by side in dated notes, because
source 47's bound has explicit constants, holds for every b ≥ 3, and feeds its
integer brackets.

**Status: AI-assisted delivery, unrefereed, not formalized.** Neither
manuscript states how it was produced; both came through the repository's
incoming channel for AI-assisted research deliveries. Source 47's audits are
"mathematical checks of this argument, not journal peer review"; source 52's
reviews are research reviews. At intake the programs were rerun on copies
(see "Rerunning"); the proofs were not re-derived.

## Files

```
article.tex        the merged report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 27 pages (title page and contents 1-2,
                   Guide 2-6, Part I 7-20, Part II 20-27, references 27)
README.md          this guide

Source 47 (Part I), from oeis-bounded-multiplicity-family-report.zip
47-caps-general-cap-proof.md               original fixed-cap proof record (support/)
47-caps-compaction-proof.md                original compaction proof record (support/)
47-caps-large-cap-asymptotic.md            original large-cap proof record (support/)
47-caps-audits-cap-family-audit.md         independent audit, every fixed cap b >= 3
47-caps-audits-large-cap-audit.md          independent audit of the large-cap expansion
47-caps-audits-cap-remainder-inverse-audit.md  audit of the explicit remainder and integer inversion
47-caps-audits-integrated-audit.md         integrated audit of the delivered report
47-caps-literature.md                      scoped primary-source and OEIS retrieval record
47-caps-qa-visual-review.md                visual review of the delivered PDF
code/47-caps-compaction-verify.py          word generation vs raw-budget and grouped recursions, caps 3, 4
code/47-caps-compaction-bijection-check.py the suffix involution, its inverse, quotas and ascent totals
code/47-caps-barrier-verify.py             exact child-rank identities and barrier implementation, b = 3..8
code/47-caps-evaluate-constants.py         T_b and mu_b by 70-digit quadrature
code/47-caps-verify-large-cap.py           large-cap ratios, first variation, both inverse models
code/47-caps-verify.sh                     delivered check driver (delivery paths; do not run here)
code/47-caps-build.sh                      delivered PDF build (builds bounded-multiplicity-report.tex; do not run here)
data/47-caps-compaction-validation.json         output of compaction-verify.py
data/47-caps-compaction-bijection-validation.json  output of compaction-bijection-check.py
data/47-caps-barrier-validation.json            output of barrier-verify.py
data/47-caps-constants.json                     output of evaluate-constants.py
data/47-caps-large-cap-validation.json          output of verify-large-cap.py
data/47-caps-provenance.json               SHA-256 of manuscript 37's tex/pdf and of the proof records
data/47-caps-verification-summary.json     release checks and scope
data/47-caps-requirements.txt              mpmath==1.3.0

Source 52 (Part II), from oeis-fixed-sector-addendum.zip
52-sectors-fixed-taylor-sectors.md         original derivation (sources/)
52-sectors-fixed-sector-independent-audit.md  independent PASS audit (sources/)
52-sectors-integrated-source-review.md     integrated mathematical and source-fidelity review
52-sectors-qa-visual-review.md             visual review of the delivered PDF
code/52-sectors-fixed-sector-verify.py     author coefficients (--order) and 45-digit quadratures (--numerics)
code/52-sectors-fixed-sector-independent-audit.py  exact-rational and geometric-moment checks
code/52-sectors-root-sector-gamma-check.py Gamma-centred coefficient check, r = 1, 2, 3
code/52-sectors-check-reciprocal.py        reciprocal algebra identity
code/52-sectors-verify.sh                  delivered check driver (delivery paths; do not run here)
code/52-sectors-build.sh                   delivered PDF build (builds fixed-sector-addendum.tex; do not run here)
data/52-sectors-fixed-sector-validation.json             output of fixed-sector-verify.py --order 3 --numerics
data/52-sectors-fixed-sector-independent-validation.json output of fixed-sector-independent-audit.py
data/52-sectors-root-sector-gamma-validation.txt         output of root-sector-gamma-check.py
data/52-sectors-reciprocal-validation.json               output of check-reciprocal.py
data/52-sectors-provenance.json            SHA-256 of source 47's tex/pdf and of the included sources
data/52-sectors-verification-summary.json  release checks and scope
data/52-sectors-requirements.txt           mpmath==1.3.0, sympy==1.14.0
```

Not shipped (all in `096ee7b87`): both delivered PDFs, both `SHA256SUMS`
ledgers, source 52's README and manuscript (its text is Part II), and the four
files of archive 52's `checks/replay/`, which are byte-identical to the saved
results above. The delivered README of source 47, staged as `README.md` by
the placement commit, is replaced by this file; it survives in `096ee7b87`
and `aa7345800`. No file was excluded as heavy (largest data file 5,818
bytes), so there is nothing to reconstruct.

## Label prefix

`amc:` (Part I, source 47's labels) and `amc:sec:` (Part II, "sectors",
source 52's labels). Source 47's own section labels began with `sec:`, so its
section labels read `amc:sec:compaction`, `amc:sec:checks`, …; they belong to
Part I. Part II's labels all read `amc:sec:eq:…`, `amc:sec:thm:…`,
`amc:sec:cor:…` or `amc:sec:sec:…`. Guide labels are `amc:guide:`, Part labels
`amc:part:`. 91 labels: 48 from source 47, 29 from source 52, 14 added at the
merge.

## What is claimed

- **Part I (source 47).** For every fixed cap b ≥ 3:
  (a_n^{(b)}/n!)^{1/n} → μ_b = 1/T_b, with
  T_b = ∫_0^∞ log E_b(v)/(E_b(v) − 1) dv and E_b(v) = Σ_{j≤b} v^j/j!; the
  exponential generating function has radius T_b; and
  log a_n^{(b)} = log n! − n log T_b + O_b(n/log n) (Theorem 1.1). The proof
  uses an exact compaction by a suffix involution, uniform positive-operator
  barriers, stopped Feynman–Kac comparison and a coefficient extraction at
  every length. A length inverse N_b(X) = n_0 + O_b(L/(log L)³),
  n_0 = L/W_0(L/(eT_b)). As b → ∞: T_b ↓ π²/6, μ_b ↑ 6/π²,
  T_b = π²/6 + (b+1)(ζ(b+2) − 1) + O(b^{5/2}(4/9)^b), with the explicit
  0 ≤ T_b − π²/6 − (b+1)(ζ(b+2) − 1) ≤ 160 b^{5/2}(4/9)^b for every b ≥ 3
  (Theorem 1.2, Section 7). A W_{−1} cap inverse with integer brackets and
  counterexamples to rounding by ⌈b_0⌉ at arbitrarily small tolerances
  (Section 8). For b = 2 the same formula, with T_2 = 3π²/8, is imported from
  the sibling cap-two report (see below).
- **Part II (source 52).** T_b − π²/6 = Σ_{r≥1} A_{r,b} exactly, with strictly
  positive sectors, for every b ≥ 2; for fixed K the remainder after K sectors
  is positive and asymptotic to A_{K+1,b} (Theorem 12.1). Every fixed sector
  has an expansion to all algebraic orders,
  A_{r,b} = C_r b^{(3−r)/2} β_r^b (Σ_j c_{r,j} b^{−j} + …), β_r = (r/(r+1))^r,
  with rational c_{r,j}, explicit c_{r,1}, three corrections for r = 2, 3, and
  A_{1,b} = (b+1)(ζ(b+2) − 1) exactly (Theorem 13.1). The same for
  6/π² − μ_b (Corollary 14.1). In particular
  T_b − π²/6 − (b+1)(ζ(b+2) − 1) ~ (8/(9√π))√b(4/9)^b.

## What is not claimed

The union of both sources' non-claims, all printed in the report:

- no fixed-cap prefactor, ratio limit or all-orders expansion in n for b ≥ 3;
  the O_b(n/log n) error is deliberately coarse; a_n^{(b)} ~ C_b n! μ_b^n is
  not implied;
- the limits in length and cap are kept separate: no uniform asymptotics for
  b = b(n), no exchange of limits;
- the length inverse is not an exact rounding rule; the cap inverse concerns
  the limiting growth constant, not cap selection for finite lengths; no
  unconditional rounding near integer transitions;
- the sector results are for a fixed number of sectors and a fixed order: no
  optimal truncation, summability, uniformity in r = r(b), justified sum of all
  sector expansions, or accumulation-scale (e^{−b}) theorem; finite
  truncations of an earlier sector do not resolve later sectors; the
  reciprocal remainder is positive only eventually for each fixed K; no new
  inverse; "transseries" in Part II means only the exact sector decomposition;
- no priority claim; the literature checks are scoped; the cap-two compacted
  recurrence and the conjectured constant 8/(3π²) are due to Conway, Conway,
  Elvey Price and Guttmann (2022); the standalone OEIS page of A317784 could
  not be retrieved by source 47;
- the quadratures are numerical checks, not interval-certified enclosures.

## Relation to other reports and to formal developments

- **[2 October 2026] Sibling report on cap two.**
  [`../a202058-ascent-000-growth`](../a202058-ascent-000-growth) (batch 77,
  OEIS A202058, four manuscripts) treats the cap b = 2 (ascent sequences
  avoiding 000). Its Part I is the "separately audited cap-two report" that
  source 47 cites by hash: its main theorem (label `a58:fd:thm:main` there)
  gives T_2 = 3π²/8, the root limit and an O(n^{9/13}(log n)³) error, and its
  later Parts sharpen the cap-two asymptotics and prove the cap-two ratio
  limit. This report uses from it only T_2 and the case b = 2 of the root
  limit; source 47's barrier proof excludes b = 2. By the coordinator's
  decision at the write, sources 47 and 52 form their own report instead of
  Parts V–VI of the A202058 report: that report is about the fine asymptotics
  of one cap, this one about the growth constants of all caps b ≥ 3 and their
  dependence on b. The article says this in the Guide ("Relation to other
  reports") and in a dated note in Part I, Section 1.
- The batch-77 reports
  [`../a202061-ascent-120-deficit`](../a202061-ascent-120-deficit) and
  [`../a202062-ascent-201-enumeration`](../a202062-ascent-201-enumeration)
  treat other pattern classes of ascent sequences; they share no theorem with
  this report.
- The length inverse and the W_{−1} cap inverse are instances of the Lambert
  core `p0:thm:lambert-core` of the transseries volume
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`,
  and the integer brackets of its separation step `p0:thm:staircase`. No
  novelty is claimed for these mechanics.
- **Formal status.** Nothing in this report is formalized in Lean or Rocq, and
  its location confers no formal status. The only related formal statement is
  generic: the separation inequality of `p0:thm:staircase`, formalized as
  `staircase_separation` in
  `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`.

## Building

From this directory, in a scratch copy (the repository keeps no auxiliary
files):

```
mkdir <scratch>/amc && cp article.tex <scratch>/amc/ && cd <scratch>/amc
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX with amsmath, amssymb, amsthm, booktabs, lmodern, microtype,
hyperref, enumitem, longtable and array. The build of 2 October 2026 (MiKTeX)
had no errors, no undefined references or citations, no multiply defined
labels or duplicate destinations, and no overfull boxes. The log repeats
pdfTeX notices "fontmap entry ... already exists, duplicates ignored"; they come
from the `\pdfmapfile` lines both delivered sources carry and are harmless.

## Rerunning

Run the programs on a copy, never in this directory. The shipped
`*-verify.sh` drivers use the delivered layout (`checks/`, `sources/`,
unprefixed names), call `python3`, and write `checks/replay/` inside the
package; source 52's driver compares with `cmp`, which fails on Windows
because redirected Python output ends lines with CRLF. Requirements: Python 3
with mpmath 1.3.0 and SymPy 1.14.0 (use `py` on this machine).

Either rerun the delivered package from the arrival commit:

```
git show 096ee7b87:docs/incoming/oeis-bounded-multiplicity-family-report.zip > <scratch>/47.zip
git show 096ee7b87:docs/incoming/oeis-fixed-sector-addendum.zip > <scratch>/52.zip
# unzip each in <scratch>; then, in each package directory: bash verify.sh
```

or run the shipped copies individually:

```
R=<this directory>; mkdir <scratch>/amc-run && cd <scratch>/amc-run
for f in compaction-verify compaction-bijection-check barrier-verify evaluate-constants verify-large-cap; do
  cp "$R/code/47-caps-$f.py" "$f.py"; done
py compaction-verify.py          > compaction-validation.json
py compaction-bijection-check.py > compaction-bijection-validation.json
py barrier-verify.py             > barrier-validation.json
py evaluate-constants.py         > constants.json
py verify-large-cap.py           > large-cap-validation.json
for f in fixed-sector-verify fixed-sector-independent-audit root-sector-gamma-check check-reciprocal; do
  cp "$R/code/52-sectors-$f.py" "$f.py"; done
cp "$R/data/52-sectors-fixed-sector-validation.json" fixed-sector-validation.json   # input of the audit script
py fixed-sector-independent-audit.py > fixed-sector-independent-validation.json
py root-sector-gamma-check.py        > root-sector-gamma-validation.txt
py check-reciprocal.py               > reciprocal-validation.json
py fixed-sector-verify.py --order 3 --numerics > fixed-sector-validation.replay.json   # slow
```

Compare each output with the file of the same name under
`data/47-caps-…` or `data/52-sectors-…`, modulo CR (for example
`diff --strip-trailing-cr`); compare `fixed-sector-validation.replay.json`
with `data/52-sectors-fixed-sector-validation.json`. The independent audit
script reads `fixed-sector-validation.json` from its own directory, which is
why the saved author output is copied there first.

At intake (2 October 2026, on copies, machine heavily loaded) source 47's
five checks reproduced their saved JSON byte for byte modulo CR (about 5, 4,
5, 15 and 130 s); source 52's independent audit (30 s), Gamma-moment check
(118 s) and reciprocal check (17 s) did likewise, and the coefficient block of
`fixed-sector-verify.py --order 3` without `--numerics` (6 s) equalled the
saved one. The author's 45-digit quadratures (`--numerics`, b = 50 … 500) were
stopped after 170 s and not rerun; the delivered README says the full check
"may take several minutes". No delivered PDF was rebuilt.

## Delivered files that use delivery names

The shipped records are byte-identical to the deliveries and therefore speak
of the delivered packages:

- `47-caps-qa-visual-review.md`, `47-caps-audits-integrated-audit.md`,
  `data/47-caps-verification-summary.json` and `data/52-sectors-provenance.json`
  name `bounded-multiplicity-report.tex` / `.pdf` (SHA-256 `0e53f4ea…`,
  `c357905a…`), the text of Part I (and `article.tex` at the placement
  commit) and its unshipped PDF.
- `data/47-caps-provenance.json` identifies the cap-two report as
  `a202058-report.pdf` / `.tex` of package `oeis-a202058-report`, and
  `47-caps-literature.md` calls it "the companion cap-two deliverable"; that
  report is Part I of `../a202058-ascent-000-growth`. The proof records cite each other as
  `general-cap-proof.md`, `compaction-proof.md`, `large-cap-asymptotic.md`
  (shipped as `47-caps-*.md`) and the checks as `compaction-verify.py`, … .
- `47-caps-audits-cap-remainder-inverse-audit.md` was audited against
  `large-cap-proposal.md`, a superseded exploratory proposal that source 47
  did not deliver.
- `52-sectors-integrated-source-review.md`, `52-sectors-qa-visual-review.md`
  and `data/52-sectors-verification-summary.json` identify, by name or by
  SHA-256 (`00fc2ddc…`, `e7db8511…`), `fixed-sector-addendum.tex` / `.pdf`,
  the text of Part II and its unshipped PDF;
  `52-sectors-fixed-sector-independent-audit.md` names
  `fixed-sector-audit-reproduced.json`, a file its own rerun command creates.
- `code/47-caps-verify.sh`, `code/52-sectors-verify.sh` and both `build.sh`
  use delivery names, as described under "Rerunning".
- Sentences in the Parts about "the accompanying source archive", "the ZIP",
  `verify.sh` or `provenance.json` describe the delivered archives; dated
  notes in Sections 9 and 15 and bracketed notes in the bibliography give the
  shipped names.

## Changes made at the merge

- Labels prefixed (`amc:`, `amc:sec:`); one section label added in Part I and
  two in Part II.
- Sections numbered through the report (source 52's Section k is Section
  k + 10); equations numbered through the report.
- Source 52's `\cite{main}` and "the separately supplied report" are
  references to Part I; three mentions of "the main report" gained references
  to the result they name; the bibliography entry `main` is dropped; a
  bracketed pointer to Part I is added to source 52's abstract.
- No symbol renamed and no normalization changed. A notation table in the
  Guide separates the letters the sources use differently, with false
  readings (for example Part I's remainder H_b, which is Part II's R_{1,b},
  versus Part II's harmonic number H_r; Part I's budgets β_i versus Part II's
  bases β_r).
- Nine dated `[write, 2 October 2026]` notes: the Guide's sibling-report note;
  Part I §1 (Part II's sharp remainder; the cap-two report in this
  repository), §8 (sharp size of H_b), §9 (shipped files), §10 (question 5
  answered for fixed sectors and re-scoped; cap-two ratio limit); Part II §13
  (second proof of the first variation), §14 (the narrow meaning of
  "transseries", and why the Part stays in this collection), §15 (shipped
  files, intake replay).
