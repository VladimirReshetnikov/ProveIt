# A parity factorization and sharp stabilization for Cigler's Hankel polynomials

**Part II: rectangular Schur structure and sharp recurrences**

This is a research report in two parts on the shifted Hankel determinants of
Cigler's polynomial extension `c_n(t)` of the middle binomial coefficients
(Johann Cigler, *Hankel determinants of middle binomial coefficients and
conjectures for some polynomial extensions and modifications*,
arXiv:2111.14492v3, Section 6). It is built from two manuscripts. Part I (20
September 2026) proposes a complete proof of Cigler's Conjecture 16 and
determines where its stabilization first fails. Part II (29 September 2026)
proves Part I's experimental rectangular-Schur formula and determines the exact
minimal recurrence. Both are AI-assisted research drafts prepared for Vladimir
Reshetnikov.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*A parity factorization and sharp stabilization for Cigler's Hankel polynomials*) | `cigler_conjecture16_research.zip` | (none) | sorted in `8374aaa79` of the Cardinals history, in ProveIt since `dc54c3cb3` | Part I: Sections 1–11 (pp. 5–17) and Appendices A–B (pp. 17–19) |
| 02 | batch 56, manuscript 01 (*Rectangular Schur Structure and Sharp Recurrences for Cigler's Hankel Polynomials: A proof of the repository's Schur conjecture, exact pole multiplicities, and corrected generating-function reciprocity*, 29 Sep 2026, 22-page A4 PDF as delivered) | `ProveIt_Cigler_Schur_Recurrences.zip` (inner `cigler_schur_research/`, main file `article.tex`), arrived in `e47ed8547` | `e9c09b125` (and blob `f33543af` of this `article.tex`) | `ae718a441` (prefix `02-schur-recurrences-`) | Part II: Sections 12–22 (pp. 20–41) and Appendices C–D (pp. 41–42) |

The pin `e9c09b125` is ProveIt commit
`e9c09b12549ea4e3bea7cebc52b450b761f6f581`. At that commit Part I's
`article.tex` was blob `f33543af1f`, and the `article.tex` of the sibling
report `cigler-conjecture-8-schur` blob `9c984baeeb`. No commit touched this
directory between `dc54c3cb3` and the placement, so every statement Part II
makes about "the repository's report" refers to Part I as printed here. The
manuscript read Part I through a GitHub connector at the pinned commit, not
from a library copy (`02-schur-recurrences-sources.md`). Its archive arrived
in `e47ed8547` and was retired in the placement commit; its manuscript, PDF
and delivery README are not shipped and survive only in `e47ed8547`.

**Status:** AI-assisted, unrefereed, and not formalized. Neither part has been
independently refereed or checked in a proof assistant. Neither makes an
absolute priority claim.

## Files

```
article.tex                                      the report, standalone LaTeX with an internal bibliography
article.pdf                                      the compiled report, 43 pages (title page, contents pp. 2–4,
                                                 Part I pp. 5–19, Part II pp. 20–42, references pp. 42–43)
README.md                                        this guide
LICENSE                                          MIT-0, Part I's delivered license file
STATUS.md                                        Part I's logical scope and limitations, as delivered
SOURCES.md                                       Part I's source and literature audit, as delivered
Makefile                                         Part I's make targets (see "Rerun hazards")
requirements.txt                                 Part I's pin, sympy==1.14.0
code/hankel.py                                   Part I: moments, fraction-free determinants, parity and alternant formulas
code/verify.py                                   Part I: main exact regression suite
code/verify_additional.py                        Part I: recurrence and t=1 specialization checks
data/verification.json                           Part I: recorded main run
data/verification.log                            Part I: its console transcript
data/sample_polynomials.json                     Part I: example coefficient arrays
data/additional_verification.json                Part I: recorded supplementary run
data/additional_verification.log                 Part I: its console transcript
02-schur-recurrences-STATUS.md                   Part II's claims and verification boundaries, as delivered
02-schur-recurrences-sources.md                  Part II's repository pin and source audit, as delivered
code/02-schur-recurrences-verify.py              Part II's exact verifier (Python 3, SymPy)
code/02-schur-recurrences-Makefile               Part II's delivered Makefile (must not be run; see below)
data/02-schur-recurrences-verification.json      Part II: recorded run, all ranges
data/02-schur-recurrences-verification.log       Part II: its console transcript
data/02-schur-recurrences-sample_polynomials.json Part II: exact coefficient arrays of the tested polynomials
data/02-schur-recurrences-requirements.txt       Part II's pin, sympy==1.14.0 (byte-identical to requirements.txt)
data/02-schur-recurrences-pdf_checks.json        Part II: hand-written layout record of the delivered 22-page PDF
```

Every Part I file is as it arrived in the Cardinals collection, except
`article.tex`, `article.pdf` and this README. Every `02-schur-recurrences-`
file is byte-identical to the batch-56 delivery. The delivery names map to the
shipped paths as follows:

| Delivered as | Shipped as |
|---|---|
| `article.tex`, `article.pdf`, `README.md` | not shipped (Part II of `article.tex`, `article.pdf` and this README replace them) |
| `STATUS.md` | `02-schur-recurrences-STATUS.md` |
| `sources.md` | `02-schur-recurrences-sources.md` |
| `Makefile` | `code/02-schur-recurrences-Makefile` |
| `code/verify.py` | `code/02-schur-recurrences-verify.py` |
| `data/verification.json` | `data/02-schur-recurrences-verification.json` |
| `data/verification.log` | `data/02-schur-recurrences-verification.log` |
| `data/sample_polynomials.json` | `data/02-schur-recurrences-sample_polynomials.json` |
| `data/pdf_checks.json` | `data/02-schur-recurrences-pdf_checks.json` |
| `requirements.txt` | `data/02-schur-recurrences-requirements.txt` |

## Labels and numbering

Part I's 73 labels are bare (`thm:main`, `conj:schur`, `eq:schur-candidate`,
…) and unchanged. Every label of Part II carries the prefix `rs:`: the
manuscript's 98 labels (three of which, `eq:D`, `eq:pair` and `sec:audit`,
would otherwise collide with Part I's) and five added in the merge
(`rs:sec:merge-provenance`, `rs:sec:front`, `rs:sec:notation`,
`rs:sec:source`, `rs:app:package`): 176 labels in all. The `.aux` numbers of
all 73 Part I labels were compared with a build of the committed text and are
unchanged.

The manuscript's Section *n* is Section *n* + 11 here, and its Theorem,
Lemma, Proposition, Corollary and equation *n.m* are (*n* + 11).*m*; its
Appendices A and B are Appendices C and D. Sections 12.1–12.3 (provenance,
the manuscript's title block, abstract and status box, and a notation table)
were added before its Section 1.1, which is Section 12.4 here; they contain no
numbered statement or equation.

Text added in the merge is marked `[Added 29 September 2026, batch 56: …]`:
in Part I, a line on the title page and the date, a sentence in the abstract,
and notes at the end of Section 1.3, after the proofs of Propositions 9.1 and
9.2, at the end of Section 10 (after Conjecture 10.1) and in Section 11.3; in
Part II, notes in Section 12.4 (pinned paths), after equation (18.13) (Cigler's
printed page 24; an observation of this merge), in Section 20.1 (shipped names
and a rerun) and in Appendix D (delivered commands). No statement of either
source was changed.

## Notation

Part II keeps the manuscript's notation; the table in Section 12.3 lists
every letter that means different things in the two parts, with the tempting
false reading. The important ones:

- **`𝒰`, `𝒱`.** Part I's `𝒰_a(m;t) = det(M_1^a[m])` has the power first and
  the size second. Part II's `𝒰_m(q)` is a Gram determinant of **size** `m` of
  a symbol `q`. The dictionary is `𝒰_a(m;t) = U_a(m) = 𝒰_m(Q_t^a)` (and the
  same for `𝒱`); `𝒰_m(q)` is not `𝒰_a(m;t)` with `a = m`.
- **Generating variable.** Part I's Proposition 9.1 writes `Σ H_k(n;t) x^n`;
  Part II writes `z` (and uses `x = z + 1/z` in Sections 13–14). Cigler writes
  `x`.
- **`d`.** Part I's `d_k` is the coarse exponent bound of Proposition 9.1;
  `d_k(n;t) = t^{-C(n,2)} D_k(n;t)` is the same unadjusted normalization in
  both parts (Cigler's). Part II's `d_r`, `d_q`, `d_±` are polynomial degrees.
- `N^δ_{a,m}` (Part I, numerator determinants) versus `N_k` (Part II,
  recurrence order); `δ ∈ {0,1}` versus `δ_k = ⌊k²/4⌋`; `B = 1 + t²` versus
  the factorial ratio `B(m,r)`; `M_ε` (matrices) versus `M = k − 1`;
  `𝓕_k` (Part I) and `F_k` (Part II) are the same function.

Renamed from the manuscript: its macro `\HH` is printed with Part I's `\Ht`
(the same glyph `𝓗` for the same object), and its bibliography key `CK`
(Ciucu–Krattenthaler, arXiv:0812.1251) is `CiucuK`, because Part I's `CK` is
Cigler–Krattenthaler, arXiv:2003.01676, a different paper. Its citations of
Part I (`RepoParity`) are internal references; its entry for Cigler's paper is
merged with Part I's. No printed symbol and no normalization changed.

## What the report claims

With `a = ⌊k/2⌋`, `b = ⌊(k−1)/2⌋` and
`H_k(n;t) = (−1)^{k·C(n,2)} t^{−C(n,2)} det(c_{k+i+j}(t))_{0≤i,j<n}`:

### Part I (Sections 1–11, Appendices A–B)

- **Theorem 1.1 (Conjecture 16, with a sharp first defect).** For every
  `k ≥ 1`, `n ≥ 0`, `H_k(n;t)` is a reciprocal polynomial in `Z[t]` of exact
  degree `(k−1)n`, with constant and leading coefficients 1 and strictly
  positive coefficients in between. For `k ≥ 2`,
  `H_k(n;t) = 1/((1−t)^a (1−t²)^{ab}) − C(n+a, a−1) t^{n+1} + O(t^{n+2})`
  formally at `t = 0`: coefficients stabilize through degree `n`, and the
  first failure is always at degree `n+1`. `H_1 = 1`.
- The parity factorization (Theorem 4.1) into principal minors of powers of
  tridiagonal matrices; coefficientwise total nonnegativity (Lemma 5.1,
  Proposition 5.2); fixed-size alternant evaluations (Theorem 6.2) with a
  proved Christoffel identity (Lemma 6.1); a coefficient-extraction formula
  (Corollary 7.2); a nonminimal recurrence at each fixed shift
  (Proposition 9.1); uniform convergence on compact subsets of the open unit
  disk (Proposition 9.2); product formulas at `t = 1` (Appendix A).
- **Conjecture 10.1** (the experimental rectangular-Schur formula) was stated
  as unproved; it is proved in Part II.

### Part II (Sections 12–22, Appendices C–D)

- **Theorem 12.1 (the repository's rectangular-Schur conjecture).**
  `D_k(n;t) = (−1)^{k·C(n,2)} t^{C(n,2)} s_(n^a)(1^a, t, (t²)^b)` in `Z[t]`
  for all `k ≥ 1`, `n ≥ 0`; so `H_k(n;t) = s_(n^a)(1^a, t, (t²)^b)`, with no
  exceptional `t`. This proves Part I's Conjecture 10.1.
- **Theorem 12.2 (exact generic recurrence).** Over `Q(t)`, and at every
  real `t ∉ {0, ±1}`, the reduced denominator of `Σ H_k(n;t) z^n` is exactly
  `Π_{q=0}^{k−1} (1 − t^q z)^{e_{k,q}}` with
  `e_{k,q} = 1 + ⌊q(k−1−q)/2⌋`: the minimal recurrence, with no cancellation.
  Corollary 17.1 gives its order `N_k` (`N_{2a} = 2a + a(a−1)(2a−1)/3`,
  `N_{2a+1} = 2a+1 + 2a(a²−1)/3`). This replaces Part I's nonminimal bound.
- **Theorem 14.1 (Toeplitz factorization with a boundary parameter)**, the
  bridge from the parity factors to the Schur determinant; Proposition 13.1
  re-derives Part I's parity factorization by a second route, and
  Corollary 15.1 re-proves Part I's shape statements through tableaux (not
  claimed as new). Proposition 15.2: for odd shifts the coefficients are
  unimodal within each parity class (this one imports classical `SL_2` /
  Schur-module character theory).
- **Theorem 16.1 (cluster allocation).** For a rectangular Schur polynomial
  on repeated distinct nonzero nodes, every allocation of rows among clusters
  has exact polynomial degree `Σ r_i s_i` and an explicit nonzero leading
  coefficient; with pairwise distinct products, the reduced denominator is
  exact.
- **Theorem 18.2 (numerator).** The generating numerator has exact degree
  `N_k − k` and reciprocity sign `(−1)^{a+1}` for `k = 2a`, `+1` for odd `k`
  (Lemma 18.1: zero gap and negative-index reciprocity). Consequently the
  positive sign printed in Cigler's equation (85) is **false when `a` is
  even**; his denominators (84) and (86) are proved and minimal.
  **Theorem 18.3:** the period-four signed normalization for odd `k` has
  reduced denominator `Π (1 + t^{2q} z²)^{e_{k,q}}`, numerator degree
  `2N_k − k` and sign `(−1)^a`.
- **Theorem 19.1.** For fixed `0 < t < 1`,
  `F_k(t) − H_k(n;t) ~ n^{a−1} t^{n+1} / ((a−1)! (1−t)^{b+1} (1−t²)^{(a−1)b})`,
  relative error `O(1/n)` locally uniformly on `(0,1)`; it sharpens Part I's
  Proposition 9.2. **Theorem 19.2:** the reduced denominators at `t = 0`,
  `1`, `−1` (both parities), with exact exponents.
- Appendix C: small-shift formulas; Section 20: finite checks, dependency
  audit and a formalization plan; Section 21: six research topics.

**Merge observations** (Section 18.4, marked as such; they concern the
external source, not ProveIt): Cigler's printed generating function for `d_3`
on p. 24 omits the numerator factor `1 − tx` (its `x` coefficient is `(1+t)²`,
but `d_3(1,t) = 1 + t + t²`), and his (87) has the sign and argument of shift
`2k+1` but exponents that are correct only after replacing `k` by `k+1`
inside them. Both were checked on a rendering of the printed page and by exact
computation during the intake.

## What is not claimed

- No absolute priority for either part; both searches were bounded. The
  general Schur, character-factorization (Ciucu–Krattenthaler), stretched-Schur
  recurrence (Alexandersson) and repeated-variable bialternant
  (González-Serrano–Maximenko) machinery is classical and credited.
- Not every assertion of Cigler's **Conjecture 17** is settled; it remains
  open (Section 21.1). The literal whole of the printed **Conjecture 18** is
  not claimed: one sign is false, and corrected statements are proved.
- **Complex roots of unity**: spectral cancellations there are not classified
  (Section 21.2); only the real line is (Theorem 19.2).
- Theorem 16.1's minimality statement needs **distinct products**, not only
  distinct nodes. The fixed-`t` asymptotic is **not uniform up to `t = 1`**.
- Ordinary coefficient **unimodality is false** (`H_4(2;t)` has the valley
  5, 4, 5); parity-wise unimodality for even shifts is a question, not a
  claim. Part I claims no unimodality or log-concavity.
- Repeated-variable spectral coefficients are rational functions and must not
  be evaluated separately at `t = 0, ±1`.
- Finite checks do not prove all-index statements; no Lean or Rocq proof
  exists for anything here.

Part I's `STATUS.md` (lines 42–45) still calls the rectangular-Schur identity
"experimental and unproved here" and does not claim minimality of the
recurrence; it is Part I's delivered record and is left as delivered. Part II
proves both.

## Checks

Part I's suites passed 1,248 original-Hankel/parity evaluations, 864
auxiliary corner/alternant evaluations, 90 full polynomial comparisons, 84
first-defect checks, 234 products at `t = 1` and 126 recurrence residuals, plus
1,248 evaluations of the then-experimental Schur formula (Python 3.13.5,
SymPy 1.14.0). Part I's experimental rectangular-Schur formula (Section 10) is
proved in Part II (batch 56); Part I does not depend on it.

Part II's verifier passed 1,092 Hankel–Schur integer comparisons, 1,092
Toeplitz-factorization checks, 36 ordinary and 18 signed recurrence/numerator
checks, 2,052 numerator-reciprocity coefficient comparisons, 143 confluent
leading coefficients, 36 exceptional-parameter checks and 56 polynomial
identities (Python 3.13.5, SymPy 1.14.0). At `t = 0, ±1` it checks that the
denominators of Theorem 19.2 annihilate the sequences; their minimality is
proved in the text, and an independent Berlekamp–Massey computation during
the intake found exactly those minimal denominators for `k ≤ 10`, and exactly
the generic denominator of Theorem 12.2 for `k ≤ 9` at `t = 2, 3, −2, 1/2`.
It also reproduced the Schur identity at 342 new cases.

## Rebuild the PDF

From a copy of `article.tex` in a scratch directory (the report was built
this way, with MiKTeX `pdflatex`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has no errors, undefined references, multiply defined labels or
duplicate destinations, and no overfull boxes; three underfull-box warnings
come from Part II's verification table as delivered. Copy back only
`article.pdf`. Part I's `Makefile` target `pdf` runs `pdflatex` twice in
place and leaves auxiliary files in the report directory; do not use it here.

## Rerun the checks

Every verifier here writes into its own directory tree, so run them on a copy
(or, for Part II, with an explicit output path outside the report). Bare
`python` does not resolve reliably on the Windows machine this collection is
maintained on; use `uv run --no-project --with sympy==1.14.0 python` or `py`.

Part II, from the report root:

```sh
W=/path/to/scratch; mkdir -p "$W"
uv run --no-project --with sympy==1.14.0 python code/02-schur-recurrences-verify.py --output "$W/verification.json"
for f in verification.json sample_polynomials.json; do
  diff <(tr -d '\r' < "$W/$f") "data/02-schur-recurrences-$f"; done   # expect only "elapsed_seconds"
```

It writes `verification.json` and `sample_polynomials.json` into `$W`. Run
this way on a copy on 29 September 2026 (Python 3.13.5, SymPy 1.14.0), every
check passed; the console output and `sample_polynomials.json` equal the
records after CRLF → LF, and `verification.json` differs only in
`elapsed_seconds`.

Part I, on a copy:

```sh
W=/path/to/scratch/cig16; mkdir -p "$W"
cp -r code data requirements.txt "$W"/
cd "$W"
uv run --no-project --with sympy==1.14.0 python code/verify.py
uv run --no-project --with sympy==1.14.0 python code/verify_additional.py
```

These rewrite `$W/data/verification.json`, `sample_polynomials.json` and
`additional_verification.json`; compare them with the originals after
CRLF → LF. Run this way on 29 September 2026, both passed, and the files
differed from the records only in `elapsed_seconds`. Do not use Python's `-O`
option; both Part I drivers reject it.

### Rerun hazards

- **Part II's verifier overwrites Part I's records by default.** Its default
  `--output` is `data/verification.json`, and it always writes
  `sample_polynomials.json` beside its output (`verify.py:342`, `:352`): both
  names are Part I's recorded files. Always pass `--output` outside the
  report.
- **Part I's verifiers have no output option** and rewrite `data/` in place;
  so do Part I's `make verify` and the commands of Part I's Appendix B.
- **CRLF.** On Windows every verifier writes CRLF files; the records are LF.
- **`code/02-schur-recurrences-Makefile` must not be run.** It is the
  delivered Makefile (`all: verify pdf`; `verify: python code/verify.py`;
  `pdf: latexmk … article.tex`; `clean: latexmk -c article.tex`). From the
  report root, `verify` runs **Part I's** `code/verify.py`, which rewrites
  Part I's records; `pdf` rebuilds the whole report in place, overwriting the
  committed `article.pdf` and leaving auxiliary files; `clean` deletes those
  auxiliary files. From `code/`, where it lives, none of its paths resolve. It
  is shipped only as a delivered record. The same applies to the commands in
  Part II's Appendix D, which are the delivery's (Appendix D carries a note).
- Part I's `Makefile` and Appendix B use bare `python`.

## Delivered text that no longer matches this layout

- `02-schur-recurrences-STATUS.md` says "See `data/verification.json` for
  ranges": in this directory that is Part I's record; Part II's is
  `data/02-schur-recurrences-verification.json`. Its sentence "The PDF was
  compiled and rendered for layout inspection" refers to the delivered 22-page
  PDF, which is not shipped.
- `code/02-schur-recurrences-verify.py` says `Run: python code/verify.py`
  (line 4); in this directory that path is Part I's verifier.
- `data/02-schur-recurrences-pdf_checks.json` records the layout of the
  delivered 22-page PDF, not of `article.pdf`; it is hand-written (the
  verifier does not produce it) and was not listed in the delivered README.
- Part II's Appendix D lists the archive's `article.tex`, `article.pdf`,
  `README.md` and `Makefile`, and gives the delivery's commands; Section 20.1
  names `code/verify.py` and the `data/` records under their delivery names.
  Both carry dated notes with the shipped names.
- Part I's Appendix B and `STATUS.md`, `SOURCES.md` describe the original
  Cardinals-collection package and the manifest supplied with it, as
  delivered.

## Relation to neighbouring reports and to the formal project

- `cigler-conjecture-8-schur` (same directory) treats the different family
  `b_n(t)` by a Laurent–Gram/Schur method that Part II credits. Its "Exact
  generic recurrence" theorem, with reduced denominator
  `Π_{j=0}^{k} (1 − t^j z)^{2j(k−j)+1}` for `s_(n^k)(1^k, t^k)`, is the
  two-cluster case of Part II's Theorem 16.1 (nodes `1`, `t`, multiplicities
  `k`, `k`, height `k`; allocation `(k−j, j)` has degree `2j(k−j)`). This
  observation of the merge is not recorded in that report.
- `ballot-polynomial-hankel-determinants` treats Cigler's Conjectures 13–15
  (the family `a_n(t)`, Section 5); Part I explains why its target differs.
- `shifted-catalan-hankel-polynomials` treats weighted Catalan moments and
  never `c_n(t)`; nothing here bears on it.
- **Formal status.** No ProveIt Lean or Rocq development states any result of
  this report: no declaration mentions Cigler's polynomials (`git grep -i
  cigler -- '*.lean'` is empty), and the collection's placement under
  `SetTheory/Cardinals` confers no formal status. Part II's Section 20.3 is
  only a proposed three-layer formalization plan.

## Small usage example (Part I's code)

```python
import sys
sys.path.insert(0, "code")
from sympy.polys.rings import ring
from sympy.polys.domains import ZZ
from hankel import parity_formula, auxiliary_closed, stable_coefficient

R, t = ring("t", ZZ)
p = parity_formula(4, 2, t, auxiliary_closed)
print(p)
print(stable_coefficient(4, 3))  # 8; the actual cubic coefficient is 4
```

Use `parity_formula` at exceptional numerical parameters such as `t=0`.
`normalized_source` is deliberately a quotient computation and cannot evaluate
`0/0` before polynomial cancellation. At `t=1` and `t=-1`, `auxiliary_closed`
falls back to the nonsingular principal-minor definition.
