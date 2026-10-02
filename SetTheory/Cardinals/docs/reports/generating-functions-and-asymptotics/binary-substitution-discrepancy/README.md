# Sharp discrepancy for two families of binary substitutions

**Part I: counterexamples and corrected theorems for OEIS A284365 and A284366, `0 -> 1, 1 -> (10)^m` (September 19, 2026). Part II: exact position-error envelopes for the quadratic morphic words `0 -> 1, 1 -> 1 0^a 1^b`, OEIS A284368–A284371 (October 1, 2026).**

This is a research report in two Parts, built from two manuscripts. Both
author lines read "Research study prepared with ChatGPT"; both are
AI-assisted, unrefereed and not formalized in a proof assistant.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | the original report, one of the 64 research reports catalogued on 19 September 2026 | `oeis_discrepancy_counterexamples.zip` (17-page PDF) | none | `a3fe9660e` (former Cardinals repository, merged here in `dc54c3cb3`) | Part I: Sections 1–10, Appendix A |
| Part II | batch 73O1, manuscript 44 | `OEIS_Quadratic_Morphic_Words_Research_Package.zip` of arrival commit `c79d64038` (main file `article.tex`, 15-page PDF) | none (cites this report by repository URL) | `9df4ba51a` | Part II: Sections 11–22, Appendices B–C |

Every theorem, corollary, proposition, lemma, remark, proof, table, figure
and research question of manuscript 44 is printed. Part I is unchanged except
for a dated note (`[Added 1 October 2026, batch 73O1: …]`) in its Section 9.4,
a front matter (title, abstract) that announces both Parts, and the place of
its Appendix A, which now follows Part II. The title's "a family" became
"two families"; Part I keeps the old title as its Part heading.

## Results

### Part I

For the fixed word of `0 -> 1, 1 -> 101010`, the OEIS position sequences
A284365 (zeros) and A284366 (ones) conjecture upper position errors below 2.
Both are false. The first counterexamples are:

| Sequence | Rank n | Position a(n) |
| --- | ---: | ---: |
| A284366, positions of 1 | 2,977,771 | 5,334,043 |
| A284365, positions of 0 | 8,933,313 | 20,222,898 |

The common error is `(2977771*sqrt(21)-13645857)/2`, approximately
2.00487217332612884794. The sharp common upper bound is
`(6+sqrt(21))/5`, approximately 2.11651513899116800132.

Part I proves complete discrepancy limit intervals for every substitution
`0 -> 1, 1 -> (10)^m`, m >= 1. It also proves the density statements,
constructs infinite counterexample families, and derives exact recurrences
and rational generating functions for their indices.

### Part II

For `tau_(a,b): 0 -> 1, 1 -> 1 0^a 1^b` with a, b >= 1, put
`q = (sqrt((b+1)^2+4a)-(b+1))/2` and `Ĉ = (a-q)/(1-q^2)` (the manuscript's
`C`, renamed in the article because Part I's `C` is a different constant).
Part II proves:

- prefix discrepancy is bounded **iff** a <= b+1; at a = b+2 it grows
  logarithmically, for a >= b+3 by a power law (Theorem 13.2);
- in the bounded regime, sharp, unattained, subsequential envelopes
  `q-Ĉ < E_1(n) < q(1+Ĉ)` for positions of ones and
  `1/q-Ĉ-1 < E_0(n) < Ĉ/q` for positions of zeros, and sharp counting
  discrepancy (Theorem 13.1), from the exact four-state Bellman extrema
  (Proposition 15.1);
- for A284368 (`1 -> 1011`, (a,b) = (1,2)):
  (1+√13)/3 < E_0 < (4+√13)/3 and (√13−5)/3 < E_1 < (√13−2)/3, and for
  A284369 (`1 -> 1001`, (2,1)): −(3+√3)/2 < F_0 < 2+√3 and −2 < F_1 < 1+√3,
  with the closures equal to the closed intervals (Theorem 12.1); this
  proves the conjectures of A284368 and of A284370/A284371 with sharper
  constants;
- the state attractors are full intervals in both OEIS cases (exact tiling
  for A284368, overlap for A284369); this is not automatic (a gap occurs at
  (a,b) = (2,5));
- constructive extremal subsequences and rational generating functions of
  their indices.

## What is not claimed

- Part I does not determine the frequency distribution of discrepancy values
  within their interval, the density of the ranks with error above 2, or the
  exact best factor-balance constant, and does not claim that its extremal
  subsequence enumerates all record errors. Part II's research question 3
  asks the same density question for its family; it is open in both Parts.
- Part II's floor formulas for A284368 (Corollary 12.2) agree with the OEIS
  identification with the s-Wythoff pair A184484–A184485 and are a
  calibration, not a new result. Its principal claims are the two-parameter
  theorem and the A284369–A284371 envelopes. A limited source search found
  no proof of the A284369 bounds; this is not an exhaustive priority claim.
- Part II leaves open: the interval-versus-Cantor classification of the
  attractors, the error distributions, threshold densities, exact
  first-hitting algorithms, closed forms for A284370/A284371, the optimal
  factor-balance constant, the critical and supercritical normalizations,
  an automated OEIS survey, and a Lean formalization.
- The two families are disjoint: `(10)^m = 1 0^a 1^b` only for m = 1,
  (a,b) = (1,0), which Part II excludes. Part II does not contain, re-prove or
  refine Part I. For (a,b) = (m, m−1) the incidence matrix and q coincide
  with Part I's `sigma_m`, but the words and envelopes differ; the formal
  limit (a,b) = (1,0) of Part II's formulas reproduces Part I's m = 1 Beatty
  pair, outside Part II's hypotheses (Remark 11.1).
- Classical substitution-discrepancy methods (Adamczewski 2003, 2004) are not
  claimed as new.
- No Lean or Rocq declaration in this repository formalizes any statement of
  either Part (a search of `*.lean`/`*.v` for A2843xx, A18448x, Beatty and
  Wythoff finds only the ExponentialIdentities project's Beatty-fiber modules
  for the two-base exponent problem, which are unrelated). Placement in the
  Cardinals research-report collection confers no formal status.

## Files

```
article.tex                              the report (Parts I and II), standalone LaTeX with an embedded bibliography
article.pdf                              the compiled report, 34 pages (title and abstract, contents pp. 2-3,
                                         Part I pp. 4-16, Part II pp. 17-31, Appendices A-C pp. 32-33,
                                         references p. 34)
README.md                                this guide
Makefile                                 Part I's build and verification targets
oeis_proposed_updates.txt                Part I's suggested OEIS corrections, not submitted
02-morphic-oeis_proposed_updates.txt     Part II's draft OEIS comments, not submitted, as delivered
02-morphic-research_status.md            Part II's research status and claim boundary, as delivered
code/substitution.py                     Part I: exact arithmetic and recursive word tools
code/independent_check.py                Part I: separate compact certificate checker
code/verify.py                           Part I: tests, first-counterexample search, data generation
code/make_figure.py                      Part I: regenerates figures/finite_maxima (matplotlib)
code/02-morphic-verify.py                Part II: exact standard-library verifier
code/02-morphic-make_figures.py          Part II: figure generator (matplotlib)
code/02-morphic-build.sh                 Part II: the manuscript's PDF build script (see "Rerun hazards")
data/certificates.json                   Part I: first-violation descent traces and certificates
data/finite_extrema.json                 Part I: exact block extrema for W_0 through W_30
data/extremal_family.json                Part I: first 25 terms of the extremal family
data/verification.json                   Part I: executed test report (310,816 checks, --long run)
data/02-morphic-verification.json        Part II: executed test report (201,686 checks)
figures/finite_maxima.pdf, figures/finite_maxima.png                         Part I figure
figures/02-morphic-A284368_errors.pdf, figures/02-morphic-A284368_errors.png   Part II figure
figures/02-morphic-A284369_errors.pdf, figures/02-morphic-A284369_errors.png   Part II figure
```

Delivery-name map of Part II (manuscript 44; every file byte-identical to the
delivery): `code/verify.py`, `code/make_figures.py` → `code/02-morphic-*`;
`build.sh` → `code/02-morphic-build.sh`; `data/verification.json` →
`data/02-morphic-verification.json`; `figures/A28436{8,9}_errors.{pdf,png}` →
`figures/02-morphic-*`; `oeis_proposed_updates.txt`, `research_status.md` →
`02-morphic-*`. Not shipped: the manuscript `article.tex` (its text is
Part II), its 15-page PDF, its delivery README, the file list `MANIFEST.txt`
and the checksum ledger `SHA256SUMS.txt` (verified 14/14 at placement,
retired).

## Labels and numbering

Part I's 80 labels are bare (`thm:general`, `eq:weight`, `sec:family`, …) and
unchanged; no Part I theorem, equation, table or section number changed (the
`.aux` numbers of all Part I labels were compared with a build of the
committed text). Every label of Part II carries the prefix `qmw:`: the 72
delivered labels of manuscript 44 and five new ones (`qmw:sec:provenance`,
`qmw:tab:notation`, `qmw:rem:partI`, `qmw:app:checklist`, `qmw:app:files`):
157 labels in all. Four delivered names collided with Part I (`eq:weight`,
`sec:family`, `sec:intervals`, `thm:general`). Manuscript 44's section *n* is
Section *n* + 11 here (its Theorem 2.1 is Theorem 13.1); its Appendices A, B
are Appendices B, C. Section 11 (provenance, notation table, comparison of the
two families) is new. Part II's tables are numbered II.1–II.3 so that Part I's
Table 3 (in Appendix A, now printed after Part II) keeps its number.

## Notation (Part II)

Table II.1 of the article lists every symbol shared by the two Parts. Only one
symbol of manuscript 44 is renamed: its constant `C = (a−q)/(1−q²)` is printed
as `Ĉ`, because Part I's `C = q/(1−q²)` is the upper end of Part I's error
intervals, while `Ĉ` is the largest state-1 weight (the role of Part I's `H`).
No normalization changed. `q`, `λ`, `r`, `s`, `M`, `X`, `S_a`, `E_0`, `E_1`
have the same definitions in both Parts, applied to the respective word.

## Relation to other material

- `../../automata-and-formal-languages/tribonacci-additive-complexity` cites
  Part I; its "optimal discrepancy" concerns the Tribonacci word.
- No other report treats A284368–A284371, A184484/A184485 or the family
  `1 -> 1 0^a 1^b`.

## Rerun the checks

### Part I

Requires Python 3.10 or later; all verification code uses only the standard
library. From this directory:

```sh
python code/independent_check.py
python code/verify.py --long
```

The long test literally generates a prefix of 20,222,898 binary letters.
The main algorithm does not need to allocate this word; the literal build
is an independent cross-check. A memory-lighter run is `python code/verify.py`.
A successful verification **rewrites** `data/verification.json` and
regenerates the certificate and sequence data in `data/`. The delivered
report records a successful `--long` run with 310,816 counted checks, plus
assertions within the independent checker; running without `--long`
overwrites it with one that records that the optional large-word test was
omitted. Run on a copy to keep the shipped evidence.

All decisions about inequalities, extrema, and first violations use exact
integer arithmetic in the quadratic field. Decimal arithmetic is used only
for displaying values and a secondary small-coefficient arithmetic cross-check.
The interval theorem is proved in the article, not inferred from these tests.

Quadratic values in JSON are encoded as `{"m": m, "a": a, "b": b}` for
`a + b*q`, where `q = (sqrt(m*m+4*m)-m)/2`. Ranks and letter positions are
1-based. Prefix lengths and internal extremum offsets are 0-based.

API example (run from `code/`, or add `code/` to `PYTHONPATH`):

```python
from substitution import Substitution

model = Substitution(3)
print(model.select(1, 2977771))       # 5334043
print(model.select(0, 8933313))       # 20222898
print(model.prefix_counts(5334042))  # (2356272, 2977770)
print(model.first_at_least(1, threshold=2))
```

`first_at_least` returns the earliest error >= the given integer threshold
through the searched block range. Its `None` result means no witness was
found up to `max_level` (default 128), not a proof that none exists in the
infinite word. The implementation's complexity discussion assumes fixed m;
integer bit costs are accounted for separately in the article.

### Part II: rerun hazards

The delivered Part II programs are byte-identical and still use their
**delivery names**, resolved relative to the report root:

- `code/02-morphic-verify.py` writes `data/verification.json` — in this
  report that is **Part I's** recorded test report, which a run in place
  would overwrite;
- `code/02-morphic-make_figures.py` writes unprefixed
  `figures/A284368_errors.{pdf,png}` and `figures/A284369_errors.{pdf,png}`;
- `code/02-morphic-build.sh` runs `latexmk` on `article.tex` in the current
  directory (here the whole two-Part report), into `.build/`, and copies the
  result over `article.pdf`.

So run them **on a copy of the delivered layout**: re-extract
`OEIS_Quadratic_Morphic_Words_Research_Package.zip` from arrival commit
`c79d64038` (`git show c79d64038:docs/incoming/OEIS_Quadratic_Morphic_Words_Research_Package.zip`),
or copy each `02-morphic-` file back to its delivery name in a scratch
directory, then

```sh
python code/verify.py          # in the copy; writes data/verification.json there
```

At intake (batch 73O1, on a copy) `code/verify.py` passed in 71 s and wrote a
report JSON-equal to the shipped `data/02-morphic-verification.json`
("PASS: 201,686 exact/counting checks"). The figure script and build script
were not rerun. Independently, a floating-point brute force over 2·10⁶
letters for eight parameter pairs stayed inside every envelope, and the
extremal-index generating functions and the phase transition were reproduced.

## Build the PDF

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or `make pdf` (two `pdflatex` passes; Part I's `Makefile`). A TeX installation
with `newpxtext`, `newpxmath`, `amsmath`, `amsthm`, `mathtools`, `microtype`,
`tcolorbox`, `listings`, `enumitem`, `hyperref`, `bookmark` and the other
packages named in the preamble is sufficient. The pre-rendered figures are
included. The batch-73O1 build (MiKTeX, pdfLaTeX) has no errors, undefined
references or citations, multiply defined labels, duplicate destinations, or
overfull boxes. The figure PDFs (Part I's and Part II's, as delivered) embed
matplotlib Type 3 fonts; they were not regenerated.

## Discrepancies and disclosures

- **Citation of Part I.** Manuscript 44 cited Part I as "V. Reshetnikov,
  ProveIt repository, … research draft"; Part I's author line is "Research
  study prepared with ChatGPT". The article cites Part I by section instead.
- **External claim, dated.** Manuscript 44 and `02-morphic-oeis_proposed_updates.txt`
  say that the A284371 page omits "−a(n)" in its printed inequality; this is
  as seen on 1 October 2026 and was not re-checked at intake.
- **Delivered texts naming delivery files.** `02-morphic-oeis_proposed_updates.txt`
  refers to "the accompanying article" (Part II here);
  `02-morphic-research_status.md` speaks of "the article" and says that no
  GitHub repository change was submitted (true of the delivery);
  `code/02-morphic-build.sh` builds `article.tex`.
- Part I's verification compared the first 30 displayed terms of each position
  sequence and the first 30 binary letters with OEIS; the linked 10,000-term
  b-files were not compared. Part II's verifier compared the posted initial
  OEIS terms. No OEIS changes have been submitted.

## Primary references

- https://oeis.org/A284364, https://oeis.org/A284365, https://oeis.org/A284366
- https://oeis.org/A284368, https://oeis.org/A284369, https://oeis.org/A284370,
  https://oeis.org/A284371, https://oeis.org/A184484, https://oeis.org/A184485
- B. Adamczewski, *Symbolic discrepancy and self-similar dynamics*, Annales de
  l'Institut Fourier 54 (2004), no. 7, 2201–2234, doi:10.5802/aif.2079.
- B. Adamczewski, *Balances for fixed points of primitive substitutions*,
  Theoretical Computer Science 307 (2003), 47–75.

No external papers, fonts, checksum files, or transient TeX build files are
bundled.
