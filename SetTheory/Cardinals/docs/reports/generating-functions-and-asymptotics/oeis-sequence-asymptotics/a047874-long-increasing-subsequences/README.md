# Finite Fredholm Truncation for Long Increasing Subsequences

**A proof of fixed-sector holonomicity for the LIS arrays A047874 and A214152
(the sector question of Kauers and Wang), and uniform all-orders tail
asymptotics with five correction terms for A269021**

A research report dated 3 October 2026, built from one manuscript. Its title
page reads "Prepared for Vladimir Reshetnikov / ChatGPT", and its PDF author
field reads "ChatGPT": the package names ChatGPT as the tool that wrote it and
names no human author.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 85, manuscript 08 | `LIS_fixed_sector_research_package.zip` (wrapper directory `LIS_fixed_sector_research/`, 340,699 bytes), arrival commit `9d6968c8a`; main file `article.tex` | `6bf7f30d0` (`6bf7f30d0352f7596e70928b3d4f304914075907`, quoted in Section 1.3, in the bibliography entry for ProveIt and in `SOURCE_AUDIT.md`) | `ddf8df5d5` (batch 85C) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The manuscript calls
itself "an unrefereed conventional mathematical proof". Its central step,
holonomic closure of a fixed-dimensional multisum (Section 3.4), **needs
independent review** (see below). The exact computations check finite
identities on recorded ranges; the asymptotic tables are 100-digit
floating-point diagnostics, not interval bounds.

## What it proves

`A(N,k)` counts permutations of `N` letters whose longest increasing
subsequence (LIS) has length exactly `k` (OEIS A047874); `T(N,k)` counts those
with LIS at least `k` (A214152). The diagonals `T(2n,n)` and `A(2n,n)` are
A269021 and A267433. For a partition `λ`, `Y_k(λ) = #{i : λ_i − i ≥ k − 1}`
counts shifted rows beyond a threshold, and
`C_j(N,k) = Σ_{λ ⊢ N} (f^λ)² C(Y_k(λ), j)`.

- **Theorem 1.1 (finite-moment holonomic extensions).** Every `C_j` (fixed
  `j`) is a holonomic bivariate array; the truncation
  `T_R = Σ_{j ≤ R} (−1)^(j+1) C_j` and `A_R(N,k) = T_R(N,k) − T_R(N,k+1)`
  are globally holonomic and equal `T` and `A` whenever `N < (R+1)(k+R)`.
  Taking `R = r − 1`: **for every fixed `r ≥ 2`, `A` and `T` are D-finite in
  the sector `N ≤ rk`** in the regional sense of Kauers and Wang (agreement
  with a globally D-finite array). This answers the sector question of
  Kauers and Wang, arXiv:2609.02220 (see "What Kauers and Wang state").
- Lemma 2.1 (rectangle obstruction: `Y_k ≥ j` iff `λ_j ≥ k + j − 1`);
  Proposition 2.2 (Bonferroni residual, odd truncations upper bounds, even
  lower); **Proposition 2.3**: the first failure, at `N = (R+1)(k+R)`, is
  exactly `(−1)^(R+1) (f^μ)²` for the rectangle `μ = (k+R)^(R+1)`, so the
  cutoff is sharp for this construction.
- **Theorem 3.1:** an explicit proper-hypergeometric multisum for
  `C_j/(N!)²` with `4j` summation variables per pair of permutations, from
  the Borodin–Okounkov–Olshanski discrete Bessel kernel and Cauchy–Binet.
- **Corollary 4.1:** `A` and `T` are P-recursive along every rational ray
  `(an + a₀, bn + b₀)`, `a ≥ b ≥ 1`, and along rounded rays
  `(N, ⌊pN/q⌋ + c)`, `0 < p ≤ q`.
- **Theorem 5.2:** single sums for `C_1`, hence for `T` and `A` when
  `N ≤ 2k + 1`, including single sums for both OEIS diagonals.
- **Proposition 6.1:** `C_1 − T` is zero for `N < 2k + 2` and smaller than
  every algebraic order (`≤ C_I exp(−c_I N log N)` relative to `B`) in the
  linear regime.
- **Theorem 1.2 (uniform tail expansion).** With `ρ = (N−k)/k` in a compact
  subset of `(0, ∞)` and `B = (N!)²/((k!)²(N−k)!)`,
  `T/B = e^(−2ρ) (Σ_{d ≤ M} c_d(ρ)/k^d + O(k^(−M−1)))` for every `M`, with
  `c_1 = 2ρ − ρ²` and `c_2`, `c_3` explicit (`c_4`, `c_5` in Appendix B);
  Proposition 7.1: `c_d ∈ Q[ρ]`, `deg c_d = 2d`, leading coefficient
  `(−1)^d/d!`; an explicit coefficient algorithm (Section 7.2).
- Corollaries 8.1–8.3: the exact-length expansion through `k^(−3)`, the
  conditional overshoot `P(LIS ≥ k+d | LIS ≥ k) ~ (ρ/k)^d`, and the mean
  number of length-`k` increasing subsequences given LIS ≥ k,
  `e^(2ρ)(1 − (2ρ − ρ²)/k + O(k^(−2)))`.
- **Corollary 9.1 (A269021):**
  `a_n = 16^n (n−1)!/(π e²) · [1 + 3/(4n) + 137/(32n²) + 757/(128n³)
  − 41429/(2048n⁴) − 3803959/(40960n⁵) + O(n⁻⁶)]`; equation (9.4) gives
  A267433 through `n⁻³`: `1 − 1/(4n) + 49/(32n²) + 273/(128n³)`.
- Section 10: eight research questions (certify the `r = 3` operators via
  `C_1 − C_2`, recurrence complexity in `R`, the exponentially small
  sectors, `ρ → 0` and `ρ → ∞`, the conditional witness distribution,
  rational-ray OEIS families, a staged formalization).

## What is not claimed

- **Kauers and Wang's guessed recurrences are not certified.** The theorem
  is an existence statement; it does not show that any guessed operator for
  the one-third sector `n/3 < k < n/2` lies in the annihilator, and gives no
  minimal orders, degrees or holonomic ranks (Section 4.3).
- **No global holonomicity** of `A` or `T`: the required `R` is unbounded as
  `k/N → 0`. No irrational-slope rays; no effective small order along a ray.
- **Earlier results are credited, not claimed.** The case `r = 2` (sector
  `N ≤ 2k`) is Kauers and Wang's Theorem 1, with explicit recurrences; here
  it is only a second route to existence. Conjecture 17 of Kauers–Koutschan
  (2023), the order-four A269021 recurrence, was proved by Kauers and Wang,
  and the package does not claim it. The leading A269021 asymptotic
  `16^n (n−1)!/(π e²)` is Václav Kotesovec's (OEIS, 2016), and the A267433
  leading equivalent was proved by David Moews (Math. Stack Exchange 4771623,
  2023). The new asymptotic content is the uniform all-orders development
  and the correction terms.
- External inputs are imported, not re-proved: Robinson–Schensted, the
  discrete Bessel correlation theorem (Borodin–Okounkov–Olshanski,
  Theorem 2 and Proposition 2.9), the Wilf–Zeilberger proper-hypergeometric
  multisum theorem and Koutschan's definite-summation closure.
- No full expansion of the exponentially small contribution beyond
  Proposition 6.1's bound; Theorem 1.2 is a Poincaré expansion on compact
  `ρ`-intervals, not uniform as `ρ → 0` or `ρ → ∞`, and not convergent.
- Corollary 8.3 is about the mean only: no Poisson limit, concentration or
  limiting law of the witness count.
- The numerical tables are not interval-certified; the tests "supplement
  the written proof" and are not a substitute for it. Priority beyond the
  checked sources is not asserted ("This is not an exhaustive literature
  search or a guarantee of priority", `SOURCE_AUDIT.md`).

## What Kauers and Wang state

The manuscript's headline is that it "establishes the fixed-sector existence
conjecture stated by Kauers and Wang". The arXiv abstract of
arXiv:2609.02220 (Manuel Kauers and Chen Wang, "Recurrences for permutations
with long increasing subsequences", v1, submitted 2 September 2026) does not
mention a sector question, so the placement could not confirm the wording.
On 3 October 2026 the writing step read the paper's HTML text
(`https://arxiv.org/html/2609.02220v1`, licensed CC BY 4.0):

- Section 1 defines "D-finite inside a region R" as the existence of a
  D-finite array coinciding with the original array in R, which is the
  convention of the manuscript's Section 1.1, and proves (Theorem 1) two
  bivariate recurrences valid for `n/2 ≤ k`, from which it derives
  Kauers–Koutschan Conjecture 17. Its `a_{n,k}` is the manuscript's
  `A(N,k)`, and its `b_{n,k}` is `T(N,k)`.
- At the end of Section 2, after displaying a guessed recurrence of higher
  order and degree for `n/3 < k < n/2`, the authors write: "We suspect that
  for every r=2,3,…, the sequence a_{n,k} is D-finite in the range k≥n/r."
  They add that this would not give D-finiteness on all of `k ≥ 0`, and that
  one hopes for a uniform approach to all such slices.

So the statement is an informal conjecture, phrased as a suspicion and not
numbered; "the fixed-sector existence conjecture" is the manuscript's name
for it. Its content coincides with the sector assertion of Theorem 1.1
(`k ≥ n/r` is `N ≤ rk`), and the manuscript's description of the paper
(Sections 1–2; `SOURCE_AUDIT.md`) is accurate. A dated `[write]` note at
the end of Section 1.3 records this.

## Needs independent review: the holonomic-closure step

Theorem 1.1's holonomicity rests on Section 3.4: that the multisum of
Theorem 3.1, rewritten in gap coordinates, is a fixed-dimensional sum of
proper-hypergeometric terms to which definite-summation closure applies with
`N` and `k` free. The manuscript argues this explicitly, including the
summation boundaries, but the intake did not verify it, and the package's
own audit says that "independent mathematical review remains appropriate".
A dated `[write]` note in Section 3.4 lists what a reviewer should check:
joint holonomicity of the summand in all `4j + 2` variables under the
reciprocal-factorial and cube-restriction conventions, applicability of the
cited closure theorems with the `N`-dependent support `h ≥ 0`, and the
treatment of the boundary terms of creative telescoping. The executable
checks test the identity of Theorem 3.1 and the truncation identities on
finite ranges, not holonomicity. Sections 5–9 (single sums, the uniform
expansion, the OEIS corrections) do not depend on this step; Corollary 4.1
does.

## Checks made at intake

- The delivered verifier passed on scratch copies twice: at placement
  (`uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0`, 53 s
  idle) and in the writing step (Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0,
  71 s script time; the delivered summary records 4.6 s on the producer's
  machine). Every regenerated data file equals the shipped one: the six CSV
  files byte for byte, `coefficients.tex` and `symbolic_coefficients.json`
  after stripping CR; `verification_summary.json` differs only in
  `elapsed_seconds`.
- An independent hook-length program, written in the writing step and not
  shipped, reproduced the single sum for `C_1` for all `N ≤ 14`,
  `1 ≤ k ≤ N + 1`, the truncation identity and the exact first failure for
  `R = 1, 2, 3` in that range, and `T(2n,n) = 1, 2, 23, 588, 24553, 1438112,
  108469917` and `A(2n,n) = 1, 1, 13, 381, 17557, 1100902, 87116283` for
  `n ≤ 6`, as in the table of Section 9.2.
- By hand: the A269021 corrections through `n⁻²` and the A267433
  corrections through `n⁻³` follow from `c_d(1)`, the exact-length
  coefficients and the central-binomial expansion (9.2), and the
  exact-length polynomials of (8.2) equal the `point_c_rho` entries of
  `data/verification_summary.json`.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats Young tableaux, the
Robinson–Schensted correspondence or longest increasing subsequences, and
the report's place in the collection confers no formal status. The
manuscript uses no repository theorem.

**Neighbouring reports.**

- Other conjectures of the same Kauers–Koutschan (2023) paper are proved in
  `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/a181280-binary-matrix-formula`
  (Conjecture 20; the package's audit says A181280 was rejected as a target
  because that report exists),
  `SetTheory/Cardinals/docs/reports/enumerative-combinatorics/a195806-hexagonal-lattice`
  (Conjecture 11) and Part IV of
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a215561-fixed-composition-excursions`
  (Conjecture 15). Conjecture 17, on A269021, is Kauers and Wang's result.
- The batch-85 sibling
  `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a181199-shifted-rectangles`
  (labels `shr:`) treats fixed-height shifted rectangles; it shares the
  rectangle tableau count but no theorem.
- The rectangle formula (2.6) (`lis:eq:rectanglehook`) is the classical
  hook-length count printed as `t2:eq:tableaux` in
  `Analysis/Transseries/docs/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`.
- `a047909-beta-renewal-subsequences` concerns complete increasing
  subsequences of multiset permutations: a different object.

**Stale claims.** "A targeted identifier search did not surface an A269021
report" (Section 1.3; `SOURCE_AUDIT.md`: "returned no matches") is true at
the pin and was confirmed at placement for A047874, A214152, A269021 and
A267433; the repository's only treatment of them is now this report. The
statement stays as dated provenance.

## Notation

Some letters carry two meanings: `a_n`, `b_n` of Section 9 are `T(2n,n)`
and `A(2n,n)`, while Kauers and Wang's `a_{n,k}` and `b_{n,k}` are the
arrays `A` and `T` (their `b_{2n,n}` is `a_n` here); `R` is the truncation
rank here and a region in Kauers and Wang; `j` is the moment order and a
summation index (Sections 5 and 7); `m` is a summation index (Lemma 5.1,
Theorem 5.2) and the deficit `N − k` (Theorem 1.2, Section 7); `q` is
`N/(k+2)²` in Proposition 6.1, the variables `q_a` of Theorem 3.1 and a
denominator in Corollary 4.1; `C_1` is a shifted-row moment, not the mean
witness count; `L_ℓ` (7.4) and `L_n` (Section 9.3) are unrelated. A table in
the first `[write]` note fixes each one. No symbol was renamed.

## Labels

Every label carries the prefix `lis:`. The manuscript's 83 labels (64
`eq:`, 5 `cor:`, 4 each `thm:`, `prop:` and `sec:`, 2 `lem:`) were prefixed
before anything cited them, and every reference to them was updated (64
`\eqref`, 15 `\ref`); no label was added or removed, so the report has 83
labels. (The placement dossier's figure of 85 counted two occurrences of
the word "label" in the proof of Proposition 6.1.)

The writing step also:

- added three dated `[write]` notes: end of Section 1.3 (provenance, the
  "ChatGPT" attribution, what Kauers and Wang state, review status and the
  intake's independent checks, repository neighbours, the notation table);
  end of the main paragraph of Section 3.4 (needs independent review); end
  of Appendix A (shipped layout, OEIS licence, the intake rerun);
- added to the preamble the `writenote` environment, and wrapped the title
  page in `\hypersetup{pageanchor=false}` … `\hypersetup{pageanchor=true}`:
  the `titlepage` environment resets the page counter, and the delivered
  source produced a duplicate `page.1` PDF destination.

No statement, proof or number of the manuscript was changed; apart from the
label prefixes and these additions, `article.tex` is the delivered file.

## Files

```text
README.md                         this guide (replaces the delivery README)
article.tex                       the report (delivered main file; labels prefixed, three [write] notes)
article.pdf                       compiled report, 21 pages
SOURCE_AUDIT.md                   the package's source and novelty audit (as delivered)
code/verify.py                    exact, symbolic and numerical checks (delivered at the package root)
code/build.sh                     the package's PDF build script, three pdflatex passes (delivered at the package root)
data/requirements.txt             sympy>=1.12, mpmath>=1.3 (delivered at the package root)
data/small_counts.csv             A, T and C_1..C_4 for 0 <= N <= 15, 1 <= k <= N+1 (136 rows; the run checks N <= 26; CRLF)
data/bessel_checks.csv            fixed moments C_j from the rational Bessel-series route, N <= 14 (140 rows; CRLF)
data/a269021.csv                  T(2n,n), 0 <= n <= 60 (CRLF)
data/a267433.csv                  A(2n,n), 0 <= n <= 60 (CRLF)
data/asymptotic_checks.csv        A269021 relative errors, n = 20 ... 400, truncations M = 0, 1, 3, 5 (CRLF)
data/uniform_checks.csv           off-diagonal checks, rho = 1/2, 1, 2 (CRLF)
data/symbolic_coefficients.json   c_0..c_5, exact-length coefficients, A269021 corrections
data/coefficients.tex             c_0..c_5 as LaTeX (not \input by the article)
data/verification_summary.json    recorded run: scope and outcome of every check
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery. Placement moved `verify.py` and `build.sh`
to `code/` and `requirements.txt` to `data/`, shipped the delivered
`results/` directory as `data/`, and staged the delivery README as
`README.md`, which this guide replaces. Not shipped: the delivered 20-page
`article.pdf` (302,144 bytes) and the checksum manifest `SHA256SUMS.txt`
(16 of 16 entries verified at placement; repository policy abolishes such
manifests). Both, and the delivery README, survive in the archive:
`git show 9d6968c8a:docs/incoming/LIS_fixed_sector_research_package.zip > <scratch>/LIS_fixed_sector_research_package.zip`.
Nothing was excluded as heavy. `code/build.sh` and `data/requirements.txt`
are byte copies of files already shipped in other collection reports (for
example `adjacency-bounded-132-avoiders/code/06-critical-moments-build.sh`
and `a202061-ascent-120-deficit/data/41-sharp-requirements.txt`), shipped
again because a rerun of this report needs them.

**Third-party data.** `code/verify.py` embeds the first sixteen terms each
of A269021 and A267433 (lines 190–200, "Independent published OEIS display,
0..15 (retrieved 2026-10-03)"), copied from The On-Line Encyclopedia of
Integer Sequences (https://oeis.org/A269021, https://oeis.org/A267433).
OEIS content is published by The OEIS Foundation Inc. under the Creative
Commons Attribution-ShareAlike 4.0 licence (CC BY-SA 4.0); these terms are
third-party data under that licence, **not** MIT-0 like the rest of the
repository. The program compares its own output against them and never
contacts OEIS. The quotation from Kauers and Wang above is from a CC BY 4.0
text, with attribution.

Delivered text that names the delivery layout or a file not shipped:
`code/verify.py` (docstring "Run: python verify.py --output results"; the
default `--output` is a `results/` directory beside the script, which in the
shipped layout would be a new `code/results/`); `code/build.sh` (changes to
its own directory and builds `article.tex` there, which in the shipped
layout is not in `code/`); Appendix A of the article ("python verify.py
--output results", "File under `results/`", two `pdflatex` passes where
`build.sh` runs three; a dated note there says so). The delivered README that named `results/`, `requirements.txt` and
`build.sh` at the package root is replaced by this guide.

**Byte-level notes.** The six CSV files are CRLF throughout (Python's `csv`
module); six lines
`docs/reports/…/a047874-long-increasing-subsequences/data/<name>.csv -text`
in `SetTheory/Cardinals/.gitattributes` keep their bytes. The program writes
JSON and `.tex` files in text mode, so on Windows a rerun emits them with
CRLF where the shipped ones are LF; compare after stripping `\r`.

## Rerun the checks (on a scratch copy)

Never run `code/verify.py` without an explicit `--output` outside the
report: the program writes every output file into its output directory and
overwrites what is there. Copy the verifier to a scratch directory and write
into a fresh output directory (Git Bash, from this directory):

```sh
T=$(mktemp -d); cp code/verify.py "$T/"
( cd "$T" && py verify.py --core-only --output core )   # standard library only
( cd "$T" && uv run --no-project --with sympy==1.14.0 --with mpmath==1.3.0 \
    python verify.py --output full )                    # exact + symbolic + numerical
for f in "$T"/full/*; do b=$(basename "$f")
  tr -d '\r' < "$f" | cmp -s - <(tr -d '\r' < "data/$b") \
    && echo "same  $b" || echo "DIFF  $b"; done
```

(On a POSIX host use `python3` for `py`. Python 3.10 or newer is required.)
At intake (3 October 2026, Windows) the core run passed in 49 s and
reproduced the four exact CSV files byte for byte; the full run passed in
71 s, and only `verification_summary.json` differed (its `elapsed_seconds`;
the core run's summary also lacks the symbolic and numerical sections, as
expected). The recorded run checks 378 `(N,k)` cells with `N ≤ 26`,
truncation ranks 1–4, 140 Bessel-minor comparisons, 16 OEIS terms of each
diagonal, 61 generated terms of each, five symbolic orders, 15
finite-product cross-checks and 9 uniform checks, with numerical
diagnostics at 100 digits.

## Build the PDF

pdfLaTeX (geometry, amsmath, amsthm, mathtools, newtx, microtype, booktabs,
array, longtable, xcolor, enumitem, fancyhdr, listings, hyperref). The
article needs no BibTeX, figures or input files. Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX: 21 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source, built the same way, gives 20 pages and one duplicate `page.1`
destination.

## Provenance

- Sources cited by the manuscript: Kauers–Wang, arXiv:2609.02220v1 (2026);
  Kauers–Koutschan, J. Integer Seq. 26 (2023), Article 23.4.5;
  Borodin–Okounkov–Olshanski, J. Amer. Math. Soc. 13 (2000) 481–515;
  Wilf–Zeilberger, Bull. Amer. Math. Soc. 27 (1992) 148–153; Koutschan,
  "Creative telescoping for holonomic functions" (2013); Schensted, Canad.
  J. Math. 13 (1961) 179–191; Moews, Math. Stack Exchange 4771623 (2023);
  OEIS A047874, A214152, A269021, A267433.
- Repository input: the pin `6bf7f30d0` (3 October 2026), used for a
  bounded non-duplication search; no repository theorem is used.
- Batch 85 of `docs/incoming`, manuscript 08; arrival `9d6968c8a`,
  placement `ddf8df5d5` (batch 85C), written in the batch-85 write phase
  (3 October 2026). Single source, so the write made no merge choices.
