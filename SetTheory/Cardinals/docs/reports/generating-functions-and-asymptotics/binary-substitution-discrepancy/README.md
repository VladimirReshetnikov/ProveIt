# Sharp discrepancy for two families of binary substitutions

**Part I: counterexamples and corrected theorems for OEIS A284365 and A284366, `0 -> 1, 1 -> (10)^m` (September 19, 2026). Part II: exact position-error envelopes for the quadratic morphic words `0 -> 1, 1 -> 1 0^a 1^b`, OEIS A284368–A284371 (October 1, 2026). Part III: exact fluctuation laws and sharp critical and supercritical normalization for the same family and for every critical arrangement (October 5, 2026).**

This is a research report in three Parts, built from three manuscripts. The
author lines read "Research study prepared with ChatGPT" (Parts I, II) and
"Research prepared with ChatGPT" (Part III); all three are AI-assisted,
unrefereed and not formalized in a proof assistant.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| Part I | the original report, one of the 64 research reports catalogued on 19 September 2026 | `oeis_discrepancy_counterexamples.zip` (17-page PDF) | none | `a3fe9660e` (former Cardinals repository, merged here in `dc54c3cb3`) | Part I: Sections 1–10, Appendix A |
| Part II | batch 73O1, manuscript 44 | `OEIS_Quadratic_Morphic_Words_Research_Package.zip` of arrival commit `c79d64038` (main file `article.tex`, 15-page PDF) | none (cites this report by repository URL) | `9df4ba51a` | Part II: Sections 11–22, Appendices B–C |
| Part III | batch 114, "Exact Fluctuation Laws and Sharp Discrepancy in Binary Morphic Words" (5 October 2026) | `binary_morphic_fluctuations.zip` of arrival commit `e4d5dcf9e` (main file `binary_morphic_fluctuations.tex`, 30-page PDF) | `112d6bed` (it read this report there; this directory is unchanged between the pin and the placement) | `99053b5d1` | Part III: Sections 23–36 |

Every theorem, corollary, proposition, lemma, remark, proof, table, figure
and research question of manuscript 44 is printed. Part I is unchanged except
for a dated note (`[Added 1 October 2026, batch 73O1: …]`) in its Section 9.4,
a front matter (title, abstract) that announces both Parts, and the place of
its Appendix A, which now follows Part II. The title's "a family" became
"two families"; Part I keeps the old title as its Part heading.

Every theorem, corollary, proposition, lemma, definition, remark, proof,
table, figure and research item of the batch-114 manuscript is printed as
Part III, which answers Part II's research question 7. Parts I and II are
unchanged except for dated notes (`[Added 6 October 2026, batch 114: …]`) in
Part II — at the end of Section 16, at research questions 2, 3, 4 and 7 of
Section 21, and in Part II's introduction — and a front matter (title, date
line, abstract, PDF subject) that also announces Part III. The title "two
families" is kept: Part III treats Part II's family, and in its critical part
a wider class of words. On 6 October 2026, after the independent check of
the batch-114 write, eleven places of Part II that the batch-73O1 rename
`C → Ĉ` had missed were corrected, with a dated note in Section 11 (see
"Discrepancies and disclosures").

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

### Part III

Part III answers Part II's research question 7 (the unbounded regimes of
`tau_(a,b)`), with `X = #0 - q #1` (so `#0 - #1` at the critical value q = 1):

- **critical, a = b+2:** `limsup X(N)/log N = -liminf X(N)/log N = (a-1)/(2 log a)`,
  every value in between is a limit point, and `|X(N)| <= ((a-1)/(2 log a)) log N + O(1)`
  (Theorem 32.1); Part II's cycle `P_k` is the *first* prefix of weight
  `k(a-1)`, with exact lengths `p_k = A(a^(2k)-1) + Bk` (Theorem 32.3;
  a = 3: 4, 32, 276, 2464, …);
- **supercritical, a >= b+3:** with `alpha = log q / log lambda`, the cluster set of
  `X(N)/N^alpha` is `[-𝒞_(a,b), 𝒞_(a,b)]`, `𝒞_(a,b) = (lambda-1)/(q^2-1) * ((lambda+q)(lambda^2-1)/(q+1)^2)^alpha`,
  and `X(N) = c^alpha N^alpha Theta(log_lambda(cN)) + O(N^(alpha^2))` with a continuous
  anti-periodic graph-directed profile `Theta` (Theorem 33.1); exact finite bound
  `|X(N)| <= K L_N^alpha` in geometric length;
- **(a,b) = (8,1)** (`1 -> 1 0^8 1`): endpoints `±sqrt(10)` and
  `X(N)^2 + 5X(N) <= 10N` for every prefix; an infinite family
  `a = q^3, b = q^2-q-1` with quadratic envelopes.

Its critical analysis holds for **every word w with a zeros and a-1 ones
beginning with 1** (`0 -> 1, 1 -> w`): an exact, coefficientwise positive
convolution formula `F_(2m,c) = 1 + K_c sum_(j<m) (S(t)S(1/t))^j` for every
complete-block prefix histogram (Theorem 26.2), an exact random-sum law and
exact finite mean and variance, quantitative Gaussian and local limit laws at
every cutoff, cumulants, the pressure `chi(s) = (1/2) log(S(e^s)S(e^-s)/a^2)`
and a full large-deviation principle, the sharp variance bounds
`(a-1)/a^2 <= v <= (a^2-1)/12` with their equality words and the matching
pressure comparison, the cluster interval `[-d/(2 log a), d/(2 log a)]` for
the support diameter d, and the classification of the zero-height profiles,
counted by `(a-1)2^(a-2) = A001787(a-1)`.

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
  factor-balance constant, an automated OEIS survey, and a Lean
  formalization. Its question on the critical and supercritical
  normalizations is answered in Part III; Part III also answers the extremal
  slice of the first-hitting question at a = b+2 and proves the critical
  analogues of the distribution and threshold questions, which stay open in
  the bounded regime.
- Part III states two results with an argument sketch only: the first local
  (Edgeworth) correction to the local limit law, and the remark that every
  fixed correction order follows likewise. They are recorded as Questions 11
  and 12 of its Section 35 (Vladimir's standing rule of 4 October 2026);
  its other results come with proofs, those of the quantitative Gaussian
  estimates in condensed form. It does not claim: external
  review or proof-assistant verification; that its finite computations
  replace the proofs, or that its floating-point diagnostics and plots are
  interval-certified; the spectral explanation of discrepancy growth
  (Adamczewski), the existence of the Gaussian limit (Paquette–Son,
  Theorem 3.3) or the invariant-section identity (Rajabzadeh–Safaee,
  Solomyak, Proposition 3.1) as new; global priority; an OEIS number for the
  critical word `10001`; anything about the bounded regime; absolute
  continuity or absence of atoms of the supercritical phase laws; a count of
  words (it counts profiles); sharpness of the error `O(N^(alpha^2))`;
  exact-extreme asymptotics from the endpoint values of the rate function.
- The two families are disjoint: `(10)^m = 1 0^a 1^b` only for m = 1,
  (a,b) = (1,0), which Part II excludes. Part II does not contain, re-prove or
  refine Part I. For (a,b) = (m, m−1) the incidence matrix and q coincide
  with Part I's `sigma_m`, but the words and envelopes differ; the formal
  limit (a,b) = (1,0) of Part II's formulas reproduces Part I's m = 1 Beatty
  pair, outside Part II's hypotheses (Remark 11.1).
- Classical substitution-discrepancy methods (Adamczewski 2003, 2004) are not
  claimed as new.
- No Lean or Rocq declaration in this repository formalizes any statement of
  any Part (a search of `*.lean`/`*.v` for A2843xx, A18448x, Beatty and
  Wythoff finds only the ExponentialIdentities project's Beatty-fiber modules
  for the two-base exponent problem, which are unrelated; a search for
  A001787 and the zero-height and histogram notions of Part III finds nothing
  either). Placement in the
  Cardinals research-report collection confers no formal status.

## Files

```
article.tex                              the report (Parts I-III), standalone LaTeX with an embedded bibliography
article.pdf                              the compiled report, 72 pages (title and abstract pp. 1-2, contents
                                         pp. 3-5, Part I pp. 6-18, Part II pp. 19-34, Part III pp. 35-69,
                                         Appendices A-C pp. 70-71, references p. 72)
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
code/03-fluct-verify.py                  Part III: main exact critical verifier (histograms, moments, extrema,
                                         arrangements) and the three critical figures
code/03-fluct-general_word_audit.py      Part III: independent literal-word audit of the general finite formulas
code/03-fluct-verify_profile_realization.py   Part III: Euler-trail profile realization and enumeration
code/03-fluct-verify_supercritical.py    Part III: integer checks at (a,b) = (8,1) and the supercritical figure
code/03-fluct-build.sh                   Part III: the manuscript's PDF build script (see "Rerun hazards")
data/03-fluct-requirements.txt           Part III: Python package versions for figures and the supercritical check
data/03-fluct-computation_report.txt     Part III: check scopes and numerical conventions
data/03-fluct-verification_summary.json  Part III: summary of the main run (37,129 exact assertions)
data/03-fluct-literal_checks.json        Part III: 106 literal words, 906,168 symbols
data/03-fluct-generalized_word_audit.json   Part III: the 4,081 words with a = 2..8
data/03-fluct-independent_general_moment_audit.json   Part III: 1,078 words, 4,312 histograms and moments
data/03-fluct-profile_realization_checks.json   Part III: 1,793 profiles, 15,521 words, a = 2..9
data/03-fluct-supercritical_checks.json  Part III: (8,1) prefix inequality and extremizing prefixes
data/03-fluct-supercritical_figure_caption.txt   Part III: figure conventions
data/03-fluct-diagnostics.json           Part III: floating-point Gaussian diagnostics (not certified)
data/03-fluct-histogram_a3_m{008,032,128}_c1.json   Part III: exact histograms of W_16, W_64, W_256 at a = 3
figures/03-fluct-{supercritical_profile,gaussian_histograms,extreme_and_typical_scales,pressure_and_rate}.{pdf,png}
                                         Part III figures (Figures 4-7)
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

Delivery-name map of Part III (batch 114; every file byte-identical to the
delivery): `code/verify.py`, `code/general_word_audit.py`,
`code/verify_profile_realization.py`, `code/verify_supercritical.py` →
`code/03-fluct-*`; `build.sh` → `code/03-fluct-build.sh`;
`code/requirements.txt` → `data/03-fluct-requirements.txt`; `data/*` →
`data/03-fluct-*` (12 files); `figures/*.{pdf,png}` → `figures/03-fluct-*`
(8 files). Not shipped: the manuscript `binary_morphic_fluctuations.tex` (its
text is Part III), its 30-page PDF and its delivery `README.txt`
(retrievable from `git show e4d5dcf9e:docs/incoming/binary_morphic_fluctuations.zip`).
No checksum manifest was delivered.

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

Every label of Part III carries the prefix `bmf:`: the 117 delivered labels
of the batch-114 manuscript and five new ones (`bmf:sec:provenance`,
`bmf:tab:notation`, `bmf:rem:partII`, `bmf:q:edgeworth`,
`bmf:q:fixed-orders`): 279 labels in all. The manuscript's section *n* is
Section *n* + 23 here (its Theorem 3.2 is Theorem 26.2); Section 23
(provenance, notation table, relation to Parts I–II, citations checked,
independent checks, non-claims) is new. Its four figures are Figures 4–7, its
one new table is Table III.1, and the table counter is restored after Part
III, so Part I's Table 3 keeps its number. The `.aux` numbers of all 157
labels of Parts I–II are unchanged (compared with a build of the committed
text).

## Notation (Part II)

Table II.1 of the article lists every symbol shared by the two Parts. Only one
symbol of manuscript 44 is renamed: its constant `C = (a−q)/(1−q²)` is printed
as `Ĉ`, because Part I's `C = q/(1−q²)` is the upper end of Part I's error
intervals, while `Ĉ` is the largest state-1 weight (the role of Part I's `H`).
The rename of `1af5d1402` missed the eleven places where `C` touched a letter
(`\frac Cq`, `-qC`, `q+qC`); they printed Part I's `C` until they were
corrected on 6 October 2026.
No normalization changed. `q`, `λ`, `r`, `s`, `M`, `X`, `S_a`, `E_0`, `E_1`
have the same definitions in both Parts, applied to the respective word.

## Notation (Part III)

No symbol of the batch-114 manuscript is renamed. Table III.1 prints, for
every letter that Parts I–II also use, both meanings; the clashes are
resolved by scope (Part III's symbols are local to Sections 23–36). The
important ones: Part III's `X` is `#0 - #1` in its critical Sections 25–32
(Part II's `X` at q = 1) and Part II's `X` in Section 33; `S(t)` is the
zero-height polynomial, not Part II's state sets `S_0, S_1`; `K_0(t), K_1(t)`
are seed polynomials, not Part II's attractors; `C(t)` is a 2×2 matrix and
`𝒞_(a,b)` the supercritical amplitude, neither Part I's `C` nor Part II's
`Ĉ`; `v = Var Z` beside the positions `u(n), v(n)`; `r, s, t` are depth, tilt
and Laurent variable (and `λ^-2`, `q^-2`, geometric time in Section 33), not
Part II's slopes or Part I's `t = 1 - q`; `m` is half the depth, not Part I's
parameter. `P_k` is Part II's recursion; the critical `Q_k = σ_a(P_k)1` is
Part II's `Q_k` followed by a one. Clashes inside the manuscript (`χ`, `d`,
`e`, `A`, `B`, `c`, `Y`, `E`) are listed in Section 23.

## Relation to other material

- `../../automata-and-formal-languages/tribonacci-additive-complexity` cites
  Part I; its "optimal discrepancy" concerns the Tribonacci word.
- No other report treats A284368–A284371, A184484/A184485 or the family
  `1 -> 1 0^a 1^b`, and none uses A001787 or the zero-height histogram
  identity of Part III.

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

### Part III: rerun on a copy

The delivered Part III programs are byte-identical and resolve their output
directories relative to their own location (`code/..`, i.e. the report root),
writing **unprefixed** delivery names: `03-fluct-verify.py` writes
`data/{literal_checks,generalized_word_audit,diagnostics,verification_summary}.json`,
`data/histogram_a3_m{008,032,128}_c1.json`, `data/computation_report.txt` and,
without `--skip-figures`, `figures/{gaussian_histograms,extreme_and_typical_scales,pressure_and_rate}.{pdf,png}`;
`03-fluct-general_word_audit.py` writes `data/independent_general_moment_audit.json`;
`03-fluct-verify_profile_realization.py` writes `data/profile_realization_checks.json`;
`03-fluct-verify_supercritical.py` writes `data/supercritical_checks.json`,
`data/supercritical_figure_caption.txt` and `figures/supercritical_profile.{pdf,png}`.
`code/03-fluct-build.sh` runs `latexmk` on `binary_morphic_fluctuations.tex`
in `code/`, which is not shipped. So re-extract the archive
(`git show e4d5dcf9e:docs/incoming/binary_morphic_fluctuations.zip`) or copy
each `03-fluct-` file back to its delivery name in a scratch directory, then
there:

```sh
python code/verify.py --skip-figures      # standard library; or --output-dir <scratch dir>
python code/general_word_audit.py
python code/verify_profile_realization.py
python code/verify_supercritical.py      # needs numpy and matplotlib (data/03-fluct-requirements.txt)
```

At intake (batch 114, on a copy, Python 3.14.4 on Windows) all four passed,
each in seconds (`verify.py`: "PASS: 37129 exact assertions; 106 literal
words"; the supercritical check: `all_exact_checks_passed: true`). The
regenerated data equal the shipped files apart from CRLF line endings on
Windows and the software-version lines of `computation_report.txt` and
`verification_summary.json`; `supercritical_checks.json`,
`profile_realization_checks.json`, `independent_general_moment_audit.json`
and `supercritical_figure_caption.txt` were byte-identical. The figures were
not regenerated. Separately programmed spot checks at intake and two checks
at the write are listed in Section 23 of the article.

**Independent check of the write (6 October 2026).** An adversarial check
made by the intake after the write (`788a7bd5a`), with its own programs (not
shipped), found every item of Part III valid and nothing to retract. It
confirmed: the (8,1) inequality `X(N)^2 + 5X(N) <= 10N` on all 134,225,921
prefixes (the empty one included) of `tau^13(1)`, worst slack −16, and the
sqrt-family inequality at (27,5) on 1,592,865 prefixes; the supercritical
convergence `X(P_k)/|P_k|^alpha → 𝒞_(a,b)` in exact integer arithmetic for
nine pairs ((8,1), (4,1), (5,1), (5,2), (7,3), (9,2), (27,5), (6,1), (10,6);
closed forms exact for `k <= 40`; the finite bound `|X(N)| <= K L_N^alpha`
never exceeded); the critical exact extrema and lengths of Proposition 32.2
for a = 3..7, the first hits, and the exact slope `d/2` for d = 1..5; the
profile counts 1, 4, 12, …, 1024 for a = 2..9; the four steps marked
[write] (Solomyak's and Paquette–Son's preprints re-read); and Remark 23.1
literally. Four wordings were made more precise, as the check suggested:
Remark 23.1 now quotes Part III's Question 1 as "does not automatically
extend" across q = 1; the "does not claim" list of Section 23 names the
remark on every fixed correction order as well; the notes at Part II's
questions 3 and 2 state the range `0 < x < (a-1)/2` and point to the exact
position-error laws at complete cutoffs. The note at the end of Section 35
records the check and the first wordings.

## Build the PDF

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or `make pdf` (two `pdflatex` passes; Part I's `Makefile`). A TeX installation
with `newpxtext`, `newpxmath`, `amsmath`, `amsthm`, `mathtools`, `microtype`,
`tcolorbox`, `listings`, `enumitem`, `hyperref`, `bookmark` and the other
packages named in the preamble is sufficient. The pre-rendered figures are
included. The batch-114 build (MiKTeX, pdfLaTeX, 71 pages) and the rebuild
after the independent check of 6 October 2026 (72 pages; every label number
unchanged) have no errors, undefined references or citations, multiply
defined labels, duplicate destinations, or overfull or underfull boxes;
Part III needs no package beyond those above.
The figure PDFs of Parts I and II and Part III's
`03-fluct-supercritical_profile.pdf` embed matplotlib Type 3 fonts (Part
III's other three figures embed TrueType fonts); none was regenerated.

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

- **Part III, delivered texts naming delivery files.**
  `data/03-fluct-computation_report.txt` gives the commands
  `python code/verify.py` (shipped as `code/03-fluct-verify.py`);
  `code/03-fluct-build.sh` builds the unshipped manuscript source;
  `data/03-fluct-requirements.txt` was `code/requirements.txt`. The
  manuscript's own text refers to "the accompanying archive" with its
  source and PDF; dated notes in Section 34 say what is shipped.
- **Part III, pin and citation of this report.** The manuscript read this
  report at `112d6bed` and cited it as "Vladimir Reshetnikov, ProveIt: Sharp
  discrepancy for two families of binary substitutions, Part II"; Part III
  cites Part II by section instead. It also names a search-index commit
  `52d8ca404`, which it did not use. The OEIS pages A284368–A284371 were
  accessed by the manuscript on 5 October 2026; the bibliography keeps the
  existing entries.
- **Part III, citations checked at the write.** Solomyak's Proposition 3.1
  (arXiv:2502.14308v3) and Paquette–Son's Theorem 3.3 and Proposition 3.1
  (arXiv:1505.01428v1) were read and support the manuscript's uses; the
  journal page confirms Studia Math. 286 (2026), 189–206, but not the issue
  number "no. 2" of the delivered reference; the journal version of
  Paquette–Son was not read; Rajabzadeh–Safaee and Bressaud–Bufetov–Hubert
  were read only in abstract; Feller was not checked (Section 23).
- **Part II, missed renames (corrected 6 October 2026).** The batch-73O1
  write (`1af5d1402`) printed manuscript 44's `C` as `Ĉ` only where `C` stood
  next to a non-letter. Eleven places where it touched a letter (`\frac Cq`,
  `-qC`, `q+qC`: the summary, (13.9), (15.3) and its proof, the
  nonattainment argument and position-error bounds of Section 15, Section 18,
  Appendix B) were left as `C` and so printed Part I's `C = q/(1−q²)`. The
  printed bounds were false: for A284369, (13.9) read `E_0(n) < C/q ≈ 2.1547`,
  while `E_0` reaches 3.6437 within the first 300,000 letters; the intended
  sharp bound is `Ĉ/q = 2+√3 ≈ 3.7321` (Theorem 12.1). Found by the
  independent check of the batch-114 write; all eleven now read `Ĉ`, with a
  dated note at the provenance bullet of Section 11 (Vladimir's standing rule
  of 4 October 2026: no wrong statement is dropped unrecorded).
- **OEIS data.** The OEIS values used as fixtures or cited (A001787,
  A284368–A284371) are under CC BY-SA 4.0. Part III, like Parts I–II,
  submits nothing to OEIS.

## Primary references

- https://oeis.org/A284364, https://oeis.org/A284365, https://oeis.org/A284366
- https://oeis.org/A284368, https://oeis.org/A284369, https://oeis.org/A284370,
  https://oeis.org/A284371, https://oeis.org/A184484, https://oeis.org/A184485
- B. Adamczewski, *Symbolic discrepancy and self-similar dynamics*, Annales de
  l'Institut Fourier 54 (2004), no. 7, 2201–2234, doi:10.5802/aif.2079.
- B. Adamczewski, *Balances for fixed points of primitive substitutions*,
  Theoretical Computer Science 307 (2003), 47–75.
- https://oeis.org/A001787 (Part III)
- E. Paquette and Y. Son, *Birkhoff sum fluctuations in substitution
  dynamical systems*, Ergodic Theory Dynam. Systems 39 (2019), no. 7,
  1971–2005, doi:10.1017/etds.2017.83, arXiv:1505.01428.
- B. Solomyak, *On the Lyapunov spectrum of the twisted cocycle for
  substitutions*, Studia Math. 286 (2026), 189–206,
  doi:10.4064/sm250402-31-7, arXiv:2502.14308.
- H. Rajabzadeh and P. Safaee, *Twisted cocycle for interval exchange
  transformations: invariant structures and Lyapunov spectrum*,
  arXiv:2501.16824 (2025).
- X. Bressaud, A. I. Bufetov and P. Hubert, *Deviation of ergodic averages
  for substitution dynamical systems with eigenvalues of modulus 1*,
  Proc. London Math. Soc. (3) 109 (2014), no. 2, 483–522,
  doi:10.1112/plms/pdu009.
- W. Feller, *An Introduction to Probability Theory and Its Applications*,
  Vol. II, 2nd ed., Wiley, 1971, Chapter XVI.

No external papers, fonts, checksum files, or transient TeX build files are
bundled.
