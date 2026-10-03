# Exact Dynamics of a Three-Dimensional Keller Map

**Degree growth, Newton faces, shear spectra, and arithmetic escape**

This is a research report of ProveIt's research-report collection (category
`jacobian-conjecture`). It continues the formal project
`Algebra/JacobianConjecture`, whose map it studies, but it is about
**iteration**, which neither that project nor its three sibling reports
touch. It is built from **one manuscript**, dated 30 September 2026, author
line "Prepared for Vladimir Reshetnikov" and "AI-assisted research draft";
the delivered PDF metadata (kept in `article.tex:15`) names the author as
"ChatGPT; prepared for Vladimir Reshetnikov".

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| the manuscript | batch 70, manuscript 06 | `ProveIt_Keller_Dynamics` (inner directory of the same name, main file `article.tex`, 23-page A4 PDF; delivered in `1b3960d8a`) | `a866ff9a2` | `51c6943bf` (new report) | the whole of `article.tex`, apart from the text marked `[write]` |

Every result, proof, example, table, question and limitation of the
manuscript is printed; nothing was merged and nothing selected away.
Between the pin and the placement commit nothing under
`Algebra/JacobianConjecture` or under the category's other reports changed.
**Status: AI-assisted and unrefereed. None of the report's new results is
formalized in Lean or Rocq.** Placement beside the Lean/Rocq development of
the Jacobian project confers no formal status on it (see "The formal
project" below).

```
README.md                    this guide (replaces the delivered README)
SOURCES.md                   the manuscript's source and attribution ledger, with retrieval limits, as delivered
STATUS.md                    the manuscript's claim and verification boundary, as delivered
article.tex                  the report: the manuscript as delivered, plus [write] notes and Appendix C
article.pdf                  the compiled report, 25 pages (unnumbered title page, abstract and
                             contents pages 1-2, text pages 3-22, Appendices A-C pages 22-24,
                             references page 24)
code/Makefile                the delivered Makefile (targets assume the delivered package root)
code/degrees.py              integer-arithmetic degree calculator from the proved formulas (standard library)
code/verify_results.py       thirteen groups of exact checks (SymPy)
data/build_review.json       the delivered build and rendered-page review record of the 23-page PDF
data/calculator_checks.json  summary of a comparison of the calculator with the matrix recurrences and
                             characteristic-three formulas (930 degree vectors, n = 0..30)
data/requirements.txt        sympy==1.14.0
data/verification.json       recorded output of verify_results.py (13 groups PASS)
data/verification.txt        recorded console output of verify_results.py
```

Delivered names: `requirements.txt` and `Makefile` were at the package root
and are shipped as `data/requirements.txt` and `code/Makefile`; every other
file keeps its delivered path. Not shipped: the delivered `README.md`
(replaced by this guide), the delivered `article.pdf` (`article.pdf` here is
a build of the present `article.tex`), and the checksum manifest
`SHA256SUMS` (all 13 entries verified at placement, then retired by
repository policy). Every shipped file other than `article.tex`,
`article.pdf` and this README is byte-identical to the delivery.

## Labels

Every label in `article.tex` carries the prefix `kmd:`. The manuscript's 87
labels (`sec:`, `eq:`, `thm:`, `prop:`, `lem:`, `cor:`, `rem:`, `app:`) were
prefixed at the write and are otherwise unchanged (for example `thm:main` is
`kmd:thm:main`); every `\ref`, `\eqref`, `\cref` (including lists) and
`\Cref` was updated, and every label kept its number. One label was added,
`kmd:app:provenance` (Appendix C): 88 in all, all distinct. The manuscript's
macros are kept as delivered. No delivered file shipped here (`SOURCES.md`,
`STATUS.md`, `code/`, `data/`) cites a label name. No label has a Lean or
Rocq mapping. Theorem numbers below are those of the built `article.pdf`.

## Setting and notation

`K` is a field of characteristic zero unless characteristic 2 or 3 is named.
`u = 1+xy`, `H = u²z + y²(1+3u)`, and the map is
`F = (P,Q,R) = (uH, y+3xH, x(5−3u−x²z))`, with `det JF = −2` and the
collision `F(−1,1,5) = F(0,−2,−16) = (0,−2,0)`. The source shear is
`T_h(x,y,z) = (x, y, z + y²h(xy))` and `F_h = F ∘ T_h`, with `m = deg h`.
`d_n = deg F^n`, `e_n = deg F_h^n`, and `λ₁(G) = lim deg(G^n)^{1/n}`. Watch
for these readings:

- The manuscript's **`H`** is the project's (and both sibling reports')
  **`h = u²z + y²(1+3u)`**. The manuscript's **`h(t)`** is the **shear
  polynomial**, as in `weighted-keller-rigidity`'s `T_h` (that report's
  README already warns that `h` is overloaded there).
- `τ = y + 1/x` (Proposition 2.2) is the variable that
  `arithmetic-local-global-fibers` writes `t`, a root of the same cubic
  `g_{A,B,C}(T) = CT³ − 2T² + BT − 2A` with `g′(τ) = 2/x`. It is **not**
  the shear invariant `xy`, which the project's research notes and
  `weighted-keller-rigidity` write `t`.
- Three degrees are kept apart: **ordinary** degree (largest total degree of
  a component), **generic** degree (field degree, 3 here; the top dynamical
  degree is 3 in characteristic zero), and the **first dynamical** degree
  `λ₁ = 3+√10`. The second dynamical degree is not computed.
- `B_0` in (4.5) is an exponent matrix, not the target coordinate `B` of the
  cubic (the text says so). `L` is used locally three times: the field
  `K(P,Q,R)` in the proof of Proposition 2.2, the linear form `xz+3y` of
  (4.5), and a vector of logarithms in Section 7.
- "Characteristic three" statements concern **formal polynomial iteration**,
  not the set maps on finite fields.

The `[write]` note after (1.2) in the article records the same dictionary.

## What the report claims

- **Baseline degrees (Theorem 1.1, Theorems 3.3-3.4).** Over any field of
  characteristic ≠ 3: `d_0 = 1`, `d_1 = 7`, `d_{n+2} = 6d_{n+1} + d_n`
  (so `1, 7, 43, 265, 1633, 10063, 62011, …`), generating function
  `(1+z)/(1−6z−z²)`, and `λ₁(F) = 3+√10`. Every positive weighted degree
  is explicit (Theorem 3.3), via two exponent matrices `M`, `N` and a
  one-step invariant cone (Lemmas 3.1-3.2).
- **Upper Newton geometry (Theorems 4.1-4.2, Corollary 4.3, Lemma 4.4).**
  The downward-completed Newton polyhedron of every coordinate of every
  iterate has exactly two vertices; on the positive-weight wall `a+c = b`
  the initial forms are explicit monomials times powers of `xz+3y`. A
  coefficient-robustness corollary and a general weighted-eigenvector lemma.
- **Shear spectrum (Theorem 5.2, Corollary 5.3).** For nonzero `h` of
  degree `m`, outside characteristic three: `e_0 = 1`, `e_1 = 2m+8`,
  `e_{n+2} = (2m+7)e_{n+1} + (m+3)e_n`, and
  `λ₁(F_h) = (2m+7+√(4m²+32m+61))/2`, depending only on `m`. All these
  characteristic-zero maps are Keller, noninjective, of generic degree three
  and in **one tame left-right equivalence class**; their first dynamical
  degrees are **unbounded**. `h = 0` is a separate case, not degree zero.
- **Characteristic three (Theorem 6.1, Corollary 6.2).** `Q = y` exactly, and
  the coordinate degrees are `(7·4^{n−1}, 1, 7·4^{n−1}−3)` for `h = 0`,
  `(8·4^{n−1}, 1, 8·4^{n−1}−3)` for nonzero constant `h`, and
  `(a_n, 1, a_n−3)` with `a_{n+1} = (m+3)a_n + m+5` for `deg h = m ≥ 1`;
  hence `λ₁ = 4` or `m+3`. The reduction of an integral shear modulo three
  is governed by its reduced polynomial.
- **Characteristic two (Proposition 2.4).** `F` is dominant of purely
  inseparable degree two; the degree growth is unchanged; no Keller
  condition holds there.
- **Escape and arithmetic degree (Theorems 7.1, 7.3; Corollary 7.2).** A
  general monomial-dominance escape theorem (simple expanding eigenvalue,
  positive right eigenvector, nonnegative left eigenfunctional, strictly
  contracting remaining spectrum), verified for the baseline and every
  shear; it gives a forward-invariant complex escape region with a precise
  logarithmic asymptotic. For integral coefficients: maximal arithmetic
  degree `λ₁` for every integral point of the escape region, and these
  points are Zariski dense.
- **Proposed work.** A formalization route (Section 8.2) and ten research
  questions (Section 9). The route is a plan; no Lean or Rocq source is
  supplied.

## What the report does not claim

These are the manuscript's own boundaries (Sections 1.3, 7, 8.3, Appendix A,
`STATUS.md`), all kept:

- The map, its determinant and collision, its generic degree three, the
  cubic inverse parameter and the source-shear construction are prior work,
  credited. The value `3+√10` was **suggested** in Liam Giannini's public
  Zenodo record (version 1.1, 20 July 2026), whose description lists the
  degrees 7, 43, 265, 1633, 10063, 62011; the manuscript proves it for every
  iterate. Its linked PDF and source repository could not be retrieved, so
  nothing is claimed about their contents, and no exhaustive priority search
  was made: "the suggested value is proved", not "the first proof of a
  long-standing open conjecture".
- No classification of unrestricted Keller maps and no global degree-seven
  minimality. Corollary 5.3 is an existence statement inside one
  equivalence class and an exact spectrum for the source-shear subfamily,
  not a classification over a whole left-right orbit.
- No second dynamical degree, no algebraically stable compactification, no
  topological-entropy formula, no global Green function or canonical height.
- The escape theorem does not say each orbit in the region is Zariski dense,
  nor that arithmetic and dynamical degree agree for every rational point
  with a Zariski-dense orbit.
- Not the full Newton polytope or all lower coefficients.
- No finite-set cycle statistics from polynomial-degree formulas; no Keller
  condition in characteristic two.
- The scripts are exact computer-algebra checks, not kernel certificates.
  The univariate restriction tests are not exhaustive multivariate
  expansions; the all-iterate and all-parameter statements rest on the
  written proofs, and the escape theorem is proved on paper, not simulated.
  The calculator evaluates the proved formulas; it is not an independent
  symbolic degree detector.
- Gao's arXiv paper, Giannini's record and the `shadybrook` audit note were
  read by the manuscript's author (see `SOURCES.md`); none was re-checked at
  placement or at the write.

## Relation to neighbouring reports

- [`../weighted-keller-rigidity`](../weighted-keller-rigidity) constructs the
  shears `T_h`. **The case `n = 1` of Theorem 5.2**, coordinate degrees
  `(2m+8, 2m+7, 2m+5)` (and `(7,6,4)` for `h = 0`), **duplicates its
  Corollary 6.4** (label `wkr:cor:degreespectrum`), stated there for the
  normalized maps `F_{a,b} ∘ T_h`, which differ from `F ∘ T_{h′}` by
  diagonal scalings with `deg h′ = deg h`. The collision of `F_h` used in
  Corollary 5.3 is its Theorem 6.3's transport by `T_{−h}`. What is new
  here is every iterate `n ≥ 2` and `λ₁(F_h)`. This report answers none of
  that report's questions; the alternative placement as its Part III was
  considered and rejected for that reason.
- [`../arithmetic-local-global-fibers`](../arithmetic-local-global-fibers)
  already uses the inverse cubic and the variable `t = y + 1/x` of
  Proposition 2.2 (it credits them in turn to earlier external work); generic
  degree three is Gao's Theorem 3.3. Proposition 2.2 is therefore a second
  route to a known fact for `F`. No arithmetic Hasse-principle result is
  used, and none of that report's questions is answered.
- [`../gao-f6-fiber-geometry`](../gao-f6-fiber-geometry) studies Gao's
  five-dimensional map F6, a different map; Gao's paper is cited here only
  for his Theorem 3.3 on the present map.

`[write]` notes in the article record these credits after Proposition 2.2,
Theorem 5.2 and Corollary 5.3.

## The formal project

`Algebra/JacobianConjecture` proves, in kernel-checked Lean 4 and Rocq, the
baseline facts this report starts from, and nothing else of it:

- the map is the Lean definition `counterexample`
  (`Algebra/JacobianConjecture/Lean/JacobianConjecture/Counterexample.lean:95-101`),
  checked equal term for term (exact expansion) at the batch-70 intake;
- `det JF = −2` over every commutative ring: `jacobianDet_counterexample`
  (`:134`); Rocq `jacobian_det_is_minus_two`
  (`Algebra/JacobianConjecture/Coq/Counterexample.v:182`);
- the collision: `collision₀_value` (`:151`), `collision₁_value` (`:158`) and
  `collision` (`:165`); Rocq `integral_collision_0_value`,
  `integral_collision_1_value` (`Counterexample.v:249`, `:255`).

These declarations are used as stated (the manuscript also rederives them,
Proposition 2.1). Nothing in the project concerns iterates, degrees of
compositions or dynamics, so **none of Theorems 1.1-7.3 is formalized**,
and the manuscript's formalization route (Section 8.2) starts from scratch
above the map. The manuscript's author read the Lean source at the pin but
ran no Lean or Rocq build.

## Build

From a scratch copy of `article.tex` (MiKTeX or TeX Live, pdfLaTeX; no
bibliography program, figures or Python needed; standard packages including
`newtxtext`, `newtxmath`, `amsmath`, `amsthm`, `mathtools`, `microtype`,
`tcolorbox` and `cleveref`; no font files are bundled):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed build has 0 errors, 0 warnings (no undefined or multiply
defined references or citations, no duplicate destinations) and no overfull
or underfull boxes; it is 25 pages. Copy only `article.pdf` back. (The
delivered source, built unchanged, gave 23 pages and one duplicate `page.1`
destination from its title page; the write suppresses the title page's
anchor.)

## Rerunning the checks

Use Python 3.10 or later; the delivered verifier ran with Python 3.13.5 and
SymPy 1.14.0. **`code/verify_results.py` writes its record, by default, to
`data/verification.json`**, so never run it bare in the report directory.
Pass an explicit output path outside the report (or run on a copy):

```sh
uv run --no-project --with sympy==1.14.0 python code/verify_results.py --output /tmp/kmd-verification.json
python code/degrees.py 20
python code/degrees.py 20 --shear-degree 2
python code/degrees.py 20 --shear-degree 2 --characteristic 3
```

Do not use Python's `-O` flag for the verifier: its assertions are its
checks. On Windows the record is written with CRLF line endings; the
shipped files contain none. The intake reran the verifier on a copy: rc 0,
about 17 s, all 13 groups PASS; its record equals `data/verification.json`
apart from line endings and `elapsed_seconds`, and its console output equals
`data/verification.txt` apart from the final path line. `degrees.py` needs
only the standard library and writes nothing; the three commands above
print the first-coordinate degrees `7060678149219361`,
`1536329507178545766677` and `262260437011717` (in characteristic three the
vector is `(262260437011717, 1, 262260437011714)`). For characteristic
specialization pass the **actual degree after reduction**: an omitted
`--shear-degree` means `h = 0`, whereas `0` means a nonzero constant shear.
Polynomial degrees are not degrees of reduced polynomial functions on a
finite set.

`code/Makefile` cannot be used in place: its targets name
`code/verify_results.py` and `article.tex` relative to the delivered package
root (`Makefile:8`, `:11-13`), so they fail from `code/`, and from the
report root its `verify` target would overwrite `data/verification.json`.

## Discrepancies in delivered files

- `code/verify_results.py`: default `--output` is `data/verification.json`
  (see above).
- `data/verification.txt:14` ends with the delivery path
  `/mnt/data/ProveIt_Keller_Dynamics/data/verification.json`.
- `data/calculator_checks.json` is produced by **no shipped script**; it
  records 930 degree vectors (`n = 0..30`, characteristics 0, 2, 3, 5, 7,
  shear degrees none, 0, 1, 2, 3, 7) and four rejected invalid inputs.
- `data/build_review.json` describes the **delivered** 23-page build (TeX
  Live pdfTeX, three runs, rendered at 125 dpi), not the committed PDF. Its
  `"article_sha256"` (`:47`, `66f9e37a…`) is the hash of the delivered
  **PDF**, not of `article.tex` (`195c2f6e…`).
- The manuscript's Appendix B (`article.tex`, delivered text) names
  `requirements.txt`, a `Makefile`, the compiled PDF, `README.md` and
  `SHA256SUMS` at the package root and gives `pip install -r
  requirements.txt` and `python code/verify_results.py`; a `[write]` note
  there gives the shipped layout and the overwrite hazard.
- `SOURCES.md` and `STATUS.md` describe the delivery and the pin
  `a866ff9a2`; `SOURCES.md` reports repository files read "via the GitHub
  connector" at the pin (lines 80-173 of `Counterexample.lean`, blob
  `52bcf58a`, still the blob at the placement commit).
- The PDF metadata author "ChatGPT; prepared for Vladimir Reshetnikov"
  (`article.tex:15`) and the title-page lines are kept as delivered.
- The delivered README (not shipped) called the article "the 23-page
  article" and listed `requirements.txt`, `Makefile` and `SHA256SUMS` at the
  package root; this guide replaces it, keeping its facts.

## Provenance

Appendix C of the report records the single source, its pin `a866ff9a2`,
the arrival commit `1b3960d8a`, the placement commit `51c6943bf`, the one
placement choice (a new report rather than a Part III of
`weighted-keller-rigidity`), and every editorial change: the `kmd:` label
prefix, the `[write]`
notes on the title page, after (1.2), after Proposition 2.2, after the table
following Theorem 5.2, after Corollary 5.3, at the end of Section 8.2 and in
Appendix B; the new Appendix C; and the suppressed title-page anchor. No
mathematical statement, proof or number of the manuscript was changed.
