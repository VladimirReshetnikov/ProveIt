# Two-coin counterexamples to the proposed generalized Shepp–Olkin thresholds

**All finite orders above one, exact rational certificates, and the fixed-mean entropy phase diagram; with sharp dimension boundaries for product-Bernoulli entropy (nine bits, ten bits)**

This is a research report in two parts. Part I is the original report of
20 September 2026 on the Rényi and Tsallis entropy of the **ordinary sum**
`X_1 + … + X_n` of independent Bernoulli variables. Part II was added on
29 September 2026 in batch 43 of ProveIt's incoming-report intake, from a
manuscript written as this report's extension. It takes up Part I's "most
immediate remaining mathematical question" (Part I, Section 10), whether
universal joint concavity holds for all `0 < q < 1`, for a different
observable: the **joint bit vector** `(X_1, …, X_n)`, equivalently a weighted
sum whose `2^n` subset sums are distinct. For that observable it settles the
question. **For the ordinary sum the question stays open in this report.**
Both parts are AI-assisted research drafts prepared for Vladimir Reshetnikov.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection report, 20 Sep 2026 (*Two-coin counterexamples to the proposed generalized Shepp–Olkin thresholds*, 17-page PDF as delivered) | `bernoulli_entropy_research.zip` | (none) | `854a8b4f9` (Cardinals history), in ProveIt since `dc54c3cb3` | Part I: Sections 1–10 (pp. 4–17) and Appendices A–B (pp. 41–42) |
| 02 | batch 43, manuscript 01 (*Nine Bits, Ten Bits: Sharp dimension boundaries for product-Bernoulli entropy*, 29 Sep 2026, 21-page A4 PDF as delivered) | `proveit_product_entropy.zip` (inner `proveit_product_entropy/`, main file `article.tex`) | `ac9107d74` | `faef2ed2a` (prefix `02-product-entropy-`) | Part II: Sections 11–25 (pp. 18–40) |

The pin `ac9107d74` is ProveIt commit
`ac9107d74083fcfe8064b4aaeda7989612e6a5b6`; the manuscript read Part I's
`article.tex` and `README.md` there. Part I's files are unchanged between the
pin and the placement commit (the placement only added the eleven
`02-product-entropy-` files), so Part II's statements about "the repository
report" refer to the Part I printed here. The archive arrived in `06bcc37a8`.
Its manuscript, PDF, delivery README, two figure PDFs and `SHA256SUMS`
(16/16 verified at placement) are not shipped; they survive in the arrival
commit. Its source notes are shipped verbatim as
`02-product-entropy-SOURCES_AND_STATUS.md`. Part II prints every result,
proof, remark, limitation and question of the manuscript; its Section 11
records the provenance, what is and is not settled, the notation, and where
the write had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and no source claims otherwise. Both parts
give written proofs; their exact-arithmetic and symbolic suites are finite
checks, not substitutes for those proofs. Bibliographic priority is not
certified for either part.

## Results

**Part I** (ordinary sum; unchanged apart from six dated pointers, a two-line
Part II notice on the title page, contents entries for the two parts, labels
on seven headings, a page-anchor fix around the title page and two
bibliography entries):

- For every finite real `q > 1`, Rényi-`q` and Tsallis-`q` entropy of a sum of
  independent Bernoulli variables fail even **quasiconcavity** in the
  Bernoulli parameters, already with two coins at strictly interior rational
  parameters, on a mean-preserving segment with opposite parameter slopes
  (Theorem 1.1, dyadic family Theorem 3.2). This refutes the numerical
  thresholds 2 and 3.65986… proposed beside Conjecture 4.2 of Hillion–Johnson,
  arXiv:1503.01570v1.
- A compact exact witness at `q = 2`: endpoints `(3/20, 1/20)`,
  `(1/20, 3/20)`, midpoint `(1/10, 1/10)`; collision probabilities
  54907/80000 at the endpoints and 55088/80000 at the midpoint; Tsallis
  midpoint deficit 181/80000; Rényi deficit `log(55088/54907)`.
- The sharp balanced-point curvature boundary `p_c(q)` (Theorem 4.2), the
  complete fixed-mean two-coin maximizer classification with boundaries
  `p_b(q) < p_c(q)` (Theorem 5.2) and closed forms at `q = 2`, asymptotics of
  both boundaries (Proposition 6.1), fixed-mean two-coin concavity for
  `0 < q ≤ 1` (Theorem 6.2), minimum dimensions (Tsallis `q > 1`: two coins;
  Rényi `1 < q ≤ 2`: two coins; Rényi `q > 2`: one coin; Propositions 7.1,
  7.2) and interior failures near `(p, …, p)` for every `n ≥ 2`
  (Theorem 8.1).

**Part II** (joint bit vector, equivalently collision-free weighted sums;
manuscript Section `n` is Section `n + 11`, Theorem `n.m` is Theorem
`(n + 11).m`):

- **Sharp universal dimension (Theorem 12.2).** `T_{q,n}` is jointly concave
  on `[0,1]^n` for **every** `0 < q < 1` if and only if `n ≤ 9`; for `n ≤ 9`
  it is strongly concave at each fixed order (Theorem 19.1). For every
  `n ≥ 10` it fails at `q = 20/41`.
- **Fixed-order criterion (Theorem 12.3).** `T_{q,n}` is concave iff
  `n Ψ(q) ≤ 1`, with `Ψ` the maximum of a scalar ratio evaluated at the unique
  root of `tanh((1−q)t) tanh t = 1−q`; the largest concave dimension is
  `N(q) = ⌊1/Ψ(q)⌋`. Via a rank-one Hessian (Lemma 13.1) with exactly one
  possible unstable direction.
- **Nine versus ten.** `Ψ(q) < q(1−q)/(2+q(1−q)) ≤ 1/9` (Theorem 15.2, from an
  elementary hyperbolic inequality, Lemma 15.1); `Ψ(1/2) = 1/10`,
  `N(1/2) = 10` (Theorem 16.1); `Ψ(1/3) = 1/11`, `N(1/3) = 11` (Theorem 16.2);
  `Ψ'(1/2) = (9 − 4√3 log(2+√3))/25 < 0` (Theorem 16.4); a quartic bending law
  at the `2^10` degenerate points of `T_{1/2,10}` (Theorem 16.3).
- **Exact counterexamples at `q = 20/41`.** Local failure reduces to a
  positive 96-digit integer `D_cert` (Theorem 17.1); a certified finite
  midpoint gap `8379718/10^14 < Δ < 8379719/10^14` (Proposition 17.3); with
  weights `w_i = 1 + δ 2^(i−1)`, failure persists at constant weighted mean
  (Theorem 18.2), certified at `δ = 10^−6` with
  `8378699/10^14 < Δ_w < 8378700/10^14` (Proposition 18.3).
- **Other orders.** Product Rényi entropy is concave in every dimension
  exactly for `0 < q ≤ 2` (Theorem 19.2); product Tsallis with `n ≥ 2` is
  concave for `1 ≤ q ≤ 2` and fails quasiconcavity for `q > 2`
  (Theorem 19.3); subunit Tsallis counterexamples remain quasiconcave
  (Proposition 19.4).
- **Endpoints, decisions, blocks.** Asymptotics as `q → 0`
  (`N(q) = 2/q + log(4/q) + O(1)`, Theorem 20.1) and `q → 1`
  (`N(q) = 1/(C(1−q)) + O(1)`, `C = t_*² − 1 ≈ 0.4392288`, Theorem 20.2);
  concavity recovers near both endpoints (Corollary 20.3); an exact algebraic
  decision procedure at rational orders (Theorem 21.1) with the threshold
  table (Table 3: `N` = 206, 24, 12, 11, 10, 9, 10, 10, 13, 26, 230 at
  `q` = 1/100, 1/10, 1/4, 1/3, 2/5, 20/41, 1/2, 3/5, 3/4, 9/10, 99/100); a
  block-product curvature criterion (Theorem 22.1); ten research questions
  Q1–Q10 (Section 23).

## What Part II settles, and what it does not

- **Settled, for the joint vector only.** Part I's subunit question, asked
  for the ordinary sum, is answered for the joint vector: Rényi yes in every
  dimension; Tsallis yes exactly when `n ≤ 9` (Section 11.2 of the article).
- **Not settled: the ordinary sum.** Neither Part II nor this report answers
  Part I's question for `X_1 + … + X_n`. Tempting false readings, printed in
  Section 11.2: "ten bits fail, so the ordinary sum fails for `n ≥ 10`" and
  "nine bits are concave, so the ordinary sum is concave for `n ≤ 9`" — neither
  is implied; entropy does not pass continuously from the vector to the sum
  as weights coalesce (Section 18.3).
- **An unverified external claim.** The manuscript records H. Wang,
  arXiv:2609.27433v1 (submitted 23 September 2026), which by the manuscript's
  account states that the ordinary-sum threshold is exactly one. The
  manuscript did not rely on it; **this report has not read or verified it**
  and does not mark Part I's question answered on its strength.
- Part I's other two questions (same-sign slopes; maximizers for three or
  more coins) and partially colliding weights (Q4) are not addressed.
- Part I's delivered `STATUS.md` (20 September 2026) is unchanged; its items
  "General joint concavity for every 0<q<1" and "An all-order interval
  theorem for arbitrary n" remain accurate for the ordinary sum.

## Not claimed

Part I (from its delivery): no proof of universal joint concavity for
`0 < q < 1` for the ordinary sum (only the largest finite universally
admissible order, one, is determined, using the known Shannon theorem); no
same-sign-slope result; no maximizer classification for `n ≥ 3`; no
uniform-in-`n` neighbourhoods; nothing at order zero or for the trivial
Tsallis limit at order infinity; the existential initial-interval statements
of Conjecture 4.2 are not disproved (they could hold with threshold one); the
Shannon theorem is not challenged; no referee review, author approval,
proof-assistant verification or exhaustive priority search. The exploratory
floating-point Hessian search certifies nothing.

Part II (from the manuscript, Sections 12, 15, 18, 19, 20, 21, 22 and 24):

- It concerns the joint vector and collision-free weighted sums, **not** the
  ordinary unweighted sum; partially colliding weight systems are not
  settled, and no conclusion is drawn about the minimum failing dimension
  among weight systems with collisions.
- The subunit counterexamples disprove concavity, not quasiconcavity.
- `1/9` is not claimed to be the sharp continuous bound on `Ψ`; the
  strong-concavity constant is not claimed optimal; the nonconcave orders are
  not proved to form one interval, and global unimodality of `Ψ` is not
  proved (the figures are numerical only).
- The general gcd/root-counting branch of the rational-order decision theorem
  is an algorithmic theorem, not implemented software; the exact script
  implements only the strict-interval branch for its tabulated orders, and
  the symbolic script checks the gcd branch only at `q = 1/2` and `1/3`.
- The block criterion yields no blanket statement about categorical
  distributions.
- The known one-bit Rényi threshold, the ordinary-sum counterexample above
  one and its fixed-mean construction are **not** claimed as new.
- Not refereed, not formalized in Lean; priority not confirmed (targeted
  searches only); the symbolic checks are not a proof-assistant verification;
  running Python is not a proved bridge from the certificates to the real
  inequalities. The proof-assistant decomposition (Section 22.2) and Q10 are
  proposals.

Added at the write: the write read the manuscript's proofs and spot-checked
`Ψ(1/2)`, `Ψ(1/3)`, `Ψ(20/41)`, `Ψ'(1/2)`, `t_*`, `C` and the quartic
coefficients numerically (at placement the rank-one criterion had been
re-derived and the profile values reproduced independently); that is not an
independent proof review.

## Labels

Part I's 56 labels are bare (`thm:main`, `eq:D`, …) and unchanged. The write
added 98 labels (154 in total), all with the report prefix `bep:`: seven on
Part I headings (`bep:sec:problem`, `bep:sec:allorders`, `bep:sec:mindim`,
`bep:sec:verification`, `bep:sec:conclusions`, `bep:app:selection`,
`bep:app:certificate`) and 91 in Part II with the sub-prefix `bep:pe:` — the
manuscript's 70 labels, unchanged after the prefix, plus 21 on Part II's
section headings and the notation table. No label was renamed or removed. The
`.aux` numbers of all 56 Part I labels equal those of a build of the committed
text, and every manuscript label carries its delivered number shifted by
eleven sections (its Figures 1–2 and Table 1 are Figures 3–4 and Table 3
here; Table 2 is the new notation table). The manuscript's bibliography keys
`Wang` and `Tsallis` are `bep:pe:Wang` and `bep:pe:Tsallis`; its `HJ` is
Part I's `HJ2017`, and its `RepoEntropy` (Part I itself) became references to
Part I.

## Notation

Part II keeps the manuscript's symbols; the full table is Table 2 in
Section 11.3. Its entropies use Part I's unnormalized conventions, applied to
the vector: `T_{q,n} = (Z_{q,n} − 1)/(1 − q)`, `R_{q,n} = log Z_{q,n}/(1 − q)`
with `Z_{q,n} = Π h_q(p_i)`, `h_q(p) = p^q + (1−p)^q`. Watch for:

- **`a` flips sign.** Part I: `a = q − 1` throughout. Part II: `a = 1 − q`,
  except in the above-one part of the proof of Theorem 19.2, where `a = q − 1`.
- **`D`.** Part I's `D_q(p)` is the balanced-point quantity (4.1); Part II's
  `D` is the diagonal matrix `diag(d_q(p_i))`. The manuscript's 96-digit
  integer, also called `D` there (and in `data/02-product-entropy-checks.txt`
  and the certificate JSON), is **renamed `D_cert`** — the only renamed
  symbol; no normalization changed.
- **`F`.** Part I's `F_q` is the power sum of the sum; Part II's `F_a(t)`,
  `F(s)` and block product `F` are local, and its power sum is `Z_{q,n}`.
- **`N(q)`** is Part II's *largest concave* dimension; the product model's
  minimum failing dimension is `N(q) + 1`. It is not Part I's minimum number
  of coins for the ordinary sum.
- **`t`** is Part II's half log-odds, Part I's imbalance on `(p + t, p − t)`.
  **`L`**, **`C`**, **`w`**, **`m`**, **`K`**, **`y`**, **`g`** are local
  letters in both parts (Table 2 lists every use).

## Files

```
article.tex                                   the report (Parts I and II), standalone LaTeX, internal bibliography
article.pdf                                   the compiled report, 43 A4 pages (unnumbered title page,
                                              contents pp. 1–3, Part I pp. 4–17, Part II pp. 18–40,
                                              Appendices A–B and references pp. 41–42)
README.md                                     this guide
STATUS.md                                     Part I's delivered status and claim boundaries (20 Sep 2026)
LICENSE.txt                                   Part I's delivered CC0 1.0 dedication
Makefile                                      Part I's delivered make targets (pdf, check, symbolic, figures, clean)
requirements-optional.txt                     Part I's optional Python pins (numpy, scipy, sympy, matplotlib, mpmath)
code/verify_exact.py                          Part I: exact standard-library checks (12,512)
code/verify_symbolic.py                       Part I: SymPy differentiation and identity checks
code/make_figures.py                          Part I: phase-boundary table, CSV and two figures
code/exploratory_hessian_probe.py             Part I: exploratory floating-point search (provenance only)
code/select_area.py                           Part I: the one-draw random-area selection script
results/exact_checks.json                     Part I: recorded exact-check result
results/symbolic_checks.txt                   Part I: recorded symbolic output
results/phase_boundaries.csv                  Part I: numerical phase boundaries
results/phase_table.tex                       Part I: Table 1 (input by the article)
results/exploratory_hessian_probe.log         Part I: exploratory log (not a certificate)
results/environment.txt                       Part I: tool versions
results/pdf_quality_control.txt               Part I: its delivered PDF's layout check
figures/phase_boundaries.pdf                  Part I: Figure 1
figures/collision_profiles.pdf                Part I: Figure 2
notes/selection.json                          Part I: original random draw
notes/area_list.tex                           Part I: the 96-area list (input by Appendix A)
notes/manifest_exclusion.md                   Part I: audit of the 71 excluded manifest entries
notes/sources.md                              Part I: source and novelty audit
02-product-entropy-SOURCES_AND_STATUS.md      Part II: source notes, priority audit, evidence boundaries
code/02-product-entropy-verify_exact.py       Part II: exact standard-library certificates (17,927 checks)
code/02-product-entropy-verify_symbolic.py    Part II: SymPy identity and root-count checks (14)
code/02-product-entropy-make_figures.py       Part II: profile CSV and two Matplotlib figures
code/02-product-entropy-Makefile              Part II: delivered make targets (see below)
data/02-product-entropy-checks.txt            Part II: recorded output of the exact script
data/02-product-entropy-certificates.json     Part II: exact root-enclosure certificates and thresholds
data/02-product-entropy-profile_table.tex     Part II: Table 3 (input by the article)
data/02-product-entropy-symbolic_checks.txt   Part II: recorded output of the symbolic script
data/02-product-entropy-profile_plot.csv      Part II: Ψ(q) at q = 0.001, …, 0.999 (CRLF, as delivered)
data/02-product-entropy-pdf_quality_control.txt  Part II: layout record of the delivered 21-page PDF
```

## Build the article

From this directory, with pdfLaTeX and the `pgfplots` package (Part II's
Figures 3–4 are drawn at build time from
`data/02-product-entropy-profile_plot.csv`):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or two `pdflatex -interaction=nonstopmode -halt-on-error article.tex` runs
(Part I's `make pdf` does the same). No Python is needed. The build used for
the shipped PDF (MiKTeX pdfTeX, 29 September 2026) had no errors, undefined
references or citations, multiply defined labels, duplicate PDF destinations,
or overfull boxes; two mildly underfull lines remain in paragraphs with long
file names. The committed Part I text produced one duplicate-destination
warning (`page.1`, from the title page); the write fixed it with
`\hypersetup{pageanchor=false}` around the title page.

## Rerun the checks

Run every suite on a **copy** of this directory: the scripts write into it.

```sh
cp -r . /path/to/copy && cd /path/to/copy
# Part I
python code/verify_exact.py                      # rewrites results/exact_checks.json
python code/verify_symbolic.py                   # rewrites results/symbolic_checks.txt
python code/make_figures.py                      # rewrites results/phase_*, figures/*.pdf
# Part II (standard library only; then SymPy 1.14.0)
python code/02-product-entropy-verify_exact.py > p2-checks.txt
python code/02-product-entropy-verify_symbolic.py > p2-symbolic.txt
python code/02-product-entropy-make_figures.py   # needs Matplotlib
```

Compare `p2-checks.txt` with `data/02-product-entropy-checks.txt` and
`p2-symbolic.txt` with `data/02-product-entropy-symbolic_checks.txt`. The Part
II exact script also writes `results/certificates.json` and
`results/profile_table.tex` (compare with the `data/02-product-entropy-`
copies); the figure script writes `results/profile_plot.csv` and
`figures/profile.pdf`, `figures/ten_bit_detail.pdf`. None of these names
collides with a Part I file, but they are strays in the shipped layout.
**Do not** redirect the Part II symbolic output to `results/symbolic_checks.txt`
(that is Part I's record), and **do not** use `code/02-product-entropy-Makefile`
here: its `check`, `symbolic` and `figures` targets run the delivered names
`code/verify_exact.py`, `code/verify_symbolic.py`, `code/make_figures.py`,
which in this directory are Part I's scripts, and its `pdf`/`clean` targets act
on the combined article.

Rerun on 29 September 2026, on a copy (Python 3.14.4; SymPy 1.14.0 via
`uv run --no-project --with sympy==1.14.0`): the Part II exact script passed
17,927 checks and the symbolic script 14; both outputs, `certificates.json` and
`profile_table.tex` equal the recorded files apart from line endings (the
scripts write CRLF on Windows). The placement run gave the same result.

## Discrepancies and delivery names

- The shipped Part II files keep their delivered text, which uses delivery
  names: `02-product-entropy-SOURCES_AND_STATUS.md` names `article.tex` and
  the report path; `code/02-product-entropy-Makefile` names
  `code/verify_exact.py`, `code/verify_symbolic.py`, `code/make_figures.py`
  and `article.tex`; the scripts write `results/certificates.json`,
  `results/profile_table.tex`, `results/profile_plot.csv` and
  `figures/{profile,ten_bit_detail}.pdf`, not the prefixed `data/` names.
  Delivery-to-shipped map: `results/X` → `data/02-product-entropy-X` (six
  files), `code/X` → `code/02-product-entropy-X`, `Makefile` →
  `code/02-product-entropy-Makefile`, `SOURCES_AND_STATUS.md` →
  `02-product-entropy-SOURCES_AND_STATUS.md`.
- The delivery README (not shipped) lists `article.pdf`, `figures/` and
  `SHA256SUMS` of the package; none is shipped. The two figure PDFs are
  replaced by `pgfplots` redraws from the shipped CSV, whose step in `q` is
  0.001 (the delivered detail figure sampled `[0.48, 0.51]` at step `10^−5`).
- `data/02-product-entropy-pdf_quality_control.txt` describes the delivered
  21-page PDF, not this build.
- The Part II exact script and its certificate JSON call the 96-digit integer
  `D`; the article calls it `D_cert`.
- Part I's own delivered files (`STATUS.md`, `Makefile`, `notes/sources.md`,
  `results/pdf_quality_control.txt`, Section 9 of the article) describe
  Part I's 17-page package; they are unchanged. Part I's Section 9 carries a
  dated pointer to Part II's reproduction section.
- Part I's delivered README said the PDF has 17 pages and gave its contents
  and selection record; this README replaces it, and keeps its content above
  and below.

## Relation to neighbouring reports and to formal work

- No other report of the collection treats Shepp–Olkin concavity or Rényi or
  Tsallis entropy of Bernoulli families; the neighbours in
  `log-concavity-and-unimodality/` concern real roots, log-concavity of
  sequences and unimodality of polynomials.
- ProveIt has **no** Lean or Rocq development of Rényi or Tsallis entropy,
  Bernoulli sums or the Shepp–Olkin problem (no `.lean` or `.v` file mentions
  them), so no statement of either part is formalized, and none is claimed
  formalized.

## Random selection (Part I)

Part I's area was fixed before a single OS-backed call to
`secrets.randbelow(96)`, which returned index 57 (one-based 58), **Discrete
probability**; there was no redraw. `notes/selection.json` is the preserved
record. Re-running `code/select_area.py` makes a fresh draw and writes
`code/selection.json`; it cannot reproduce the original randomness and is not
part of the verification or the build.

## License

`LICENSE.txt`, delivered with Part I, dedicates Part I's newly generated
article, code and data to the public domain under CC0 1.0. The Part II
manuscript states no license of its own. No third-party paper, font file or
software package is redistributed by either part.
