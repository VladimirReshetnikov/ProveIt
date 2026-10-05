# Column-Convex Permutominoes (OEIS A196275)

**Exact generating function, spectral measure, all-orders secondary
asymptotics, and inversion**

A research article dated 2 October 2026 ("Report 96" of a session bundle),
built from one manuscript. Its title page names no person (author line
"Research report for OEIS A196275"); its PDF metadata give the author as
"Research report prepared with OpenAI". The package carries no "prepared for
private review" line, no e-mail address and no personal data.

| Source | Bundle report | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | Report 96 (batch 101) | `A196275_Exact_Asymptotics_and_Inversion_Source.zip` (wrapper directory `a196275/`, 18 files, 1,611,688 bytes), arrival commit `60f54ea06`; main file `source/permutomino_asymptotics_standalone.tex` | none: the package names no ProveIt commit, path or report | `f7c612c72` (batch 101) | the whole report |

**Status:** AI-assisted, unrefereed, not formalized: no Lean or Rocq
declaration exists for any statement of this report. The proofs are
conventional mathematical proofs. The exact and high-precision checks
corroborate identities, indexing and constants; they are not interval
certificates and certify no asymptotic statement.

## Trust boundaries

- **Tomás's recurrence is an external input.** The report starts from the
  triangular recurrence of A. P. Tomás (FCT 2015, Section 5.2), reindexed by
  size `n = r + 1` (`ccp:eq:init`–`ccp:eq:sum`), and does not re-derive it.
  The intake checked only that it reproduces all 200 terms of the shipped
  OEIS b-file (the verifier does the same; an intake script rechecked
  `n ≤ 60` independently). Tomás's prose says "r vertices" where the count
  is by r *reflex* vertices; the source notes this harmless typo.
- **The literature-status claims are the source's and are unchecked.** The
  report says that Beaton–Disanto–Guttmann–Rinaldi (FPSAC 2011, §3.3)
  conjectured the factorial-exponential equivalent numerically, that
  Rinaldi–Socci (2014) and Duchi–Rinaldi–Socci (2018) still call it
  conjectural, and that its bounded search of 2 October 2026 found no prior
  solution. **The intake read none of these papers and made no search.** The
  OEIS entry, read on 5 October 2026, states no formula and no asymptotic.
- **The numerics are uncertified.** Quadratures use arbitrary precision with
  precision-stability tests, not interval arithmetic.

## What it proves

`a_n` (A196275, offset 1: 1, 4, 22, 152, 1262, …) counts column-convex
permutominoes with `n` rows and `n` columns, unidentified under symmetry.
Put `b_n = a_n/(n+1)!` with the artificial `b_0 = 1/2`, `B(z) = Σ b_n z^n`,
`h = 1/(1 − W_0(1/e)) = 1.38593327599819425386…` and
`k = (2h−1)(h−1)/2 = 0.34191113152179550788…`. Theorem numbers follow the
section counter.

- **Lemma 2.1 (`ccp:lem:bernstein`), Bernstein embedding:** the operator
  `(Tf)(x) = (1−x) f(x) + ∫_0^{1−x} f` on `L²[0,1]` maps Bernstein bases
  exactly onto the recurrence, so `b_n = ½⟨1, Tⁿ1⟩`.
- **Proposition 2.2 (`ccp:prop:positive`):** `T` is positive and
  self-adjoint with essential spectrum `[0,1]`, and `1` is cyclic.
- **Lemma 3.1 (`ccp:lem:resolvent`)** and **Proposition 3.2
  (`ccp:prop:pole`):** an explicit resolvent vector,
  `m(λ) = (2λ−1)ℓ/(2λ−1−λℓ)`, and a single eigenvalue `h` off `[0,1]`, simple,
  with residue `2k`.
- **Theorem 1.1 (`ccp:thm:main`):**
  `B(z) = −(2−z) log(1−z) / (2z(2 − z + log(1−z)))`;
  `b_n = k hⁿ + ½∫_0^1 tⁿ w(t) dt` with an explicit density `w ≥ 0`
  (`ccp:eq:density`); hence `a_n ~ k (n+1)! hⁿ` and
  `r_n = b_n − k hⁿ ~ 1/(2n log² n)`. The source presents the first
  equivalent as a proof of the BDGR 2011 numerical conjecture (see the trust
  boundary above).
- **Theorem 5.1 (`ccp:thm:logs`):** the inverse-logarithmic expansion of
  `r_n` to every fixed order, with
  `c_j = (1/π) Im[(∂_α + 1 + iπ)^{j+1} Γ(α+1)]_{α=0}` and `c_0`…`c_4` in
  closed form (`c_5`, `c_6` in `verification-README.md`).
- **Theorem 6.1 (`ccp:thm:mixed`):** a mixed inverse-power /
  inverse-logarithmic expansion with explicit coefficient functions
  `𝓕_j(L)`, remainders at the level of each power sector, and explicit
  `C_{j,k}`.
- **Section 7:** the spectral interpolation `𝒜(x)` is real-analytic and
  strictly increasing on `[1, ∞)`, so the integer threshold is
  `⌈𝒜^{-1}(y)⌉`; the Lambert-W/Stirling expansion of the Gamma-envelope
  inverse.
- **Theorem 8.1 (`ccp:thm:inverse`):** for that interpolation, a Lagrange
  series of exponentially small inverse sectors about the exact envelope
  inverse converges for large `y`; two sectors explicit, and the leading term
  of every sector.
- **Theorem 9.1 (`ccp:thm:rounding`):** for every `n ≥ 1`,
  `𝓔(n) < a_n < 𝓔(n + 1/2)` with `𝓔(x) = k Γ(x+2) hˣ`; so rounding
  `𝓔^{-1}(a_n)` recovers `n`. **Corollary 9.2 (`ccp:cor:threshold`):** at
  most one exact comparison decides `N(y) = min{n : a_n ≥ y}`.
- **Theorem 10.1 (`ccp:thm:nondfinite`):** `B` is not D-finite, and neither
  `(a_n)` nor `(b_n)` is P-recursive (infinitely many simple poles
  `z_j = 1 − W_j(1/e)` on the logarithmic covering).
- **Section 11:** the scalar recurrence implied by the generating function
  (`ccp:eq:scalarcheck`) and the validation tables (below).

Added by the write (5 October 2026), with proofs, marked `[write]`:

- **Proposition 8.2 (`ccp:prop:disk`):** the convergence step of
  Theorem 8.1 written out. The source asserts the bound
  `|S(X_*+u)| ≤ C S(X_*)` on a disk of radius `c/F'(X_*)` with a one-line
  hint; the write proves it with an elementary log-derivative bound on the
  Laplace transform (`C = 2h^{1/4}` on radius `1/(4F'(X_*))`) and writes out
  the Rouché and Cauchy steps, giving the remainder bound
  `(8KS_*)^{M+1}/(4p)`, which is the source's `O_M(S^{M+1}/F')`.
- **The smoothed profile (Question 2 of Section 12.1):** the eigenvector of
  `T` at `h` is `g_h(x) = (2h−1)/(h−1+x) − log((h−1+x)/(h−x))`, and the
  Bernstein-smoothed row `(2/n!) Σ_p P_{n,p} B_{p−1,n}` differs from its
  projection `hⁿ P1` in `L²[0,1]` by exactly `√(2 r_{2n})`, where
  `2 r_{2n} = ∫_0^1 t^{2n} w(t) dt ~ 1/(2n log² n)`; so the distance tends to
  `0` like `(2n log² n)^{-1/2}`, and is at most `√(1 − 2k) < 0.57` for every
  `n ≥ 1`. (The write first stated only the bound `≤ 1`; the sharper form is
  the independent check's, adopted with a dated note keeping the first
  wording.) This makes explicit the source's "smoothed profile limit"; it
  says nothing about the coefficients `P_{n,p}` themselves.
- Credits to repository results and the dated notes listed under "Labels".
- *[Independent check, 5 October 2026.]* An adversarial check made by the
  intake after the write found both write-added proofs valid
  (Proposition 8.2 and the profile statement of Question 2), with no
  counterexample and no gap in either proof chain. The profile bound `≤ 1`
  was true but far from sharp and is replaced where it stands by the exact
  distance above. The tests (mpmath, 30–50 digits, on a copy of
  `code/verify_a196275.py`): every constant of Proposition 8.2 (`M_H ≈ 1.480`,
  `A_0(1/4) = 0.5126`, the bound `H ≥ 1/(4 log²(1/u))` on `u ≤ e^{-7}` with
  minimum ratio 4.07, `I(X − 1/4)/I(X) ≤ 2` already from `X = 1.5`); on the
  circle `|u| = 1/(4p)` at `X_* = 3, 4, 8, 20, 40` the claimed bounds
  `2h^{1/4} ≈ 2.170`, `0.45` and `K ≈ 5.425` hold with observed values
  `≤ 1.171`, `≥ 0.885` and `≤ 1.105` (crude by factors of about 2 and 5,
  but correct); the hypothesis `R ≥ 2` of part (4) fails at `X_* = 3`
  (`8KS_* ≈ 0.66`) and holds from `X_* = 4` (`8KS_* ≈ 0.31`), so in practice
  part (4) applies from about `X_* = 4`; the Lagrange series, with
  coefficients by DFT on `|u| = 1/(8p)`, converges at `X_* = 4, 8` to the
  `findroot` inverse well inside the stated remainder (remainder `1.2·10⁻²⁴`
  after `M = 6` at `X_* = 8`); and for Question 2, `T g_h = h g_h` to
  `10⁻⁵¹`, `‖P1‖² = 2k` to all digits, and the `L²` distance equal to
  `√(2 r_{2n})` to ten digits at `n = 1, 2, 5, 10, 20, 45`. A careful reading
  with numerical tests, not a formal verification; recorded in a dated
  paragraph at the end of Section 12.1.

## What is not claimed

From the source, kept in the article (collected in the note at the end of
Section 1):

- Numerical tests are supporting checks, not the proof; nothing is
  interval-certified or formalized ("not a claim of formal proof-assistant
  verification or certified interval quadrature").
- The literature search was bounded and "does not establish global
  priority".
- Theorem 8.1 is interpolation-specific: "Arbitrary functions agreeing with
  a_n at integers can have different exponentially small inverse terms."
- The rounding of Theorem 9.1 applies to exact sequence values, "not an
  arbitrary-y threshold rule"; forward rounding of `𝓔(n)` already fails at
  `n = 4` (`𝓔(4) = 151.378…`, `a_4 = 152`).
- Theorem 6.1 claims no convergence of the inverse-logarithmic series, and
  fixed-order sums need not improve monotonically at modest `n`.
- `b_0 = 1/2` is a normalization, not a count.
- `C_{0,5}` and `C_{0,6}` (verifier README) are "derived here from the
  supplied formula; not attributed to an external publication".
- Third-party PDFs, extracted text and page images are not redistributed; no
  OEIS entry was edited, and the verifier makes no network request.

The write adds: the literature-status statements and the correctness of
Tomás's recurrence beyond the 200 b-file terms are not checked by ProveIt.

## Further questions

Section 12.1 of the article ("Further questions and research",
`ccp:sec:further`) states every unproved claim of the source as an open
question, with its sketch and what is missing (Vladimir's standing rule of
4 October 2026). The intake found **no false claim** in the source.

1. **A combinatorial reason for the denominator** `2 − z + log(1−z)`
   (`ccp:q:combinatorial`); the write notes the renewal form of
   `ccp:eq:scalarcheck` that a model would have to explain.
2. **Local asymptotics of `P_{n,p}`**, especially near the boundaries
   (`ccp:q:profile`); the smoothed `L²` statement above (distance exactly
   `√(2 r_{2n})`) is proved, the coefficient analysis is not.
3. **Optimal truncation, late-term growth and exponentially improved
   estimates** in the logarithmic sector (`ccp:q:uniform`). Evidence: at
   `n = 1000` the normalized residual is `0.97490…`, the sum through `L^{-3}`
   `0.97668…`, through `L^{-4}` `0.96752…`.
4. **Interval-certified inversion** of `𝓔` (`ccp:q:certified`).
5. **Other triangular recurrences** that close in the Bernstein basis
   (`ccp:q:recurrences`).
6. **Written-out tail estimates** in the proofs of Theorems 5.1 and 6.1
   (`ccp:q:sketches`), which the source argues in condensed form; the
   intake checked them and believes them correct. The analogous step of
   Theorem 8.1 is now Proposition 8.2.
7. **External inputs** (`ccp:q:literature`): the literature status of the
   2011 conjecture and the absence of a prior solution (unchecked), and
   Tomás's recurrence (proved by Tomás, not here).

## Checks made at intake

On copies of the delivered layout (5 October 2026; Windows, Python 3.14.4,
SymPy 1.14.0, mpmath 1.3.0):

- `manifest.json`: all 17 SHA-256 entries match; `verification/run_manifest.json`:
  all 9 match; `source_manifest.json`'s hash of the b-file matches.
- `verify_a196275.py --output <scratch>` (normal mode): all checks passed, in
  **9 min 13 s** on a heavily loaded machine (the verifier's README says
  "approximately a minute or two"). Its exact counts (`n ≤ 1000`) equal the
  delivered table after CR stripping; its results JSON equals the delivered
  one except `exact_counts_file` (the output name) and `software.python`
  (3.14.4 against 3.12.14). The `python -O` run was not repeated; the
  delivered `verification_results_optimized.json` records it, and differs
  from `verification_results.json` only in `exact_counts_file`.
- `render_validation_tables.py` regenerates `validation_summary.tex`
  identically after CR stripping (rerun at the write: about 1 s).
- Independent intake scripts: the triangle against the b-file (`n ≤ 60`);
  the generating function by exact-rational division; `∫w = 1 − 2k` to 40
  digits; quadrature moments against `b_n` at `n = 0, 1, 2, 5, 10`;
  Theorem 9.1 for `n = 1..200` at 600 digits; `𝓔(4) = 151.378… < 152`; and
  the closed forms of `c_0`…`c_6` against the Gamma-derivative formula. All
  passed. The proofs of Lemma 2.1, Lemma 3.1, Proposition 3.2, Theorem 9.1
  and the second-order formula of Theorem 8.1 were rederived by hand.
- `build_local.sh` was not run (Debian TeX Live paths; it builds the
  unshipped modular source). The shipped `article.tex` as delivered builds
  with MiKTeX pdfLaTeX in 14 pages, without warnings.

The delivered `manifest.json` (not shipped) records the source's own review
notes: `"proof_review": "Core transfer/resolvent, mixed sectors, inverse
Lagrange series, integer rounding, and non-D-finiteness independently
audited"` and `"visual_review": "Every report page rendered and visually
inspected; no layout overflow or unresolved LaTeX references"`. Neither
review is shipped, and neither is an external review.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or
Rocq, no formal development in ProveIt treats permutominoes or this
recurrence, and the report's place in the collection confers no formal
status.

**Neighbouring reports and volumes** (no shared theorem; credits are dated
notes in the article):

- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a126764-lconvex-polyominoes`
  (`lcp:`): L-convex polyominoes by area, a different class with no shared
  question. Both reports invert a *specified* interpolation and recover
  integer thresholds by a ceiling (its Section 9.2 and
  `lcp:ao:cor:brackets`); its brackets carry asymptotic existence constants
  without a finite starting index, and batch 101's Report 95 (its Part III,
  written separately) finds eventual rounding of a Lambert model of A126764
  wrong for `2 ≤ n ≤ 555`. Theorem 9.1 here is explicit from `n = 1`. Its
  Lambert branch is `W_{-1}`, here `W_0`.
- `generating-functions-and-asymptotics/oeis-sequence-asymptotics/a113227-powered-catalan`
  (`pcn:`): counts as moments of a positive measure (`pcn:eq:moments`) read
  off a Stieltjes-type transform (`pcn:eq:Fmeasure`); there the measure is
  discrete, here an atom plus a density.
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`
  (not a collection report): the leading inverse equation of Section 7.1 is
  `p0:prop:factorial-core` with `κ = 1`, `d = log h − 1`; the threshold
  identity `⌈𝒜^{-1}(y)⌉` is `p0:thm:staircase` (1); Theorem 9.1 supplies the
  hypothesis `η < 1/2` of its part (3) explicitly for every `n ≥ 1`, and
  Corollary 9.2 replaces its separation condition (2); the
  interpolation-dependence caveat of Theorem 8.1 is `p0:rem:three-differ`.
  No novelty is claimed for these inversion steps.

**Stale claims.** The manuscript makes no claim about the repository and has
no pin; nothing to correct. At the time of writing no other file of the
repository mentions A196275 or permutominoes.

## Notation

The article reuses many letters with local meanings. A table in the
`[write]` note at the end of Section 1 fixes each one, with tempting false
readings: `n`/`r` (size against Tomás's reflex-vertex index), `a_n`/`b_n`,
`h`/`k`/`H`, `w` (the density, and the covering coordinate `log(1−z)` in
Theorem 10.1), `B` (series, Bernstein, Bernoulli), `W`, `ℓ`, `m`, `c`,
`D`/`d` (`D(λ)` and `D(z)` differ by a factor `λ`), `ρ`, `q`, `p`, `N` (`n+1`
and the threshold `N(y)`), `A`/`a`, `S`, `F`/`𝓕`/`𝓔`, `u`/`v`, `x`/`X`,
and the fitted constant `e` of BDGR's `r_n ≈ e n^g` (not Euler's number).
**Symbol clash in the shipped files:** the renderer
`code/render_validation_tables.py`, `data/validation_summary.tex` and
`verification-README.md` call the Gamma envelope `F(x) = k Γ(x+2) hˣ`; the
article calls it `𝓔` and reserves `F` for its logarithm in `X = x + 1`
(`ccp:eq:envelopeF`). The article's inlined copy of the fragment writes `𝓔`
(the delivered README discloses this). No symbol was renamed.

## Labels

Every label carries the prefix `ccp:`. The manuscript's 59 labels (all
`eq:`, `thm:`, `lem:`, `prop:`, `cor:`) were prefixed before anything cited
them, and every reference was updated (42 `\eqref`, 6 `\ref`). The write
added 12: `ccp:sec:interp`, `ccp:sec:rounding`, `ccp:sec:validation`,
`ccp:sec:further`; the seven questions `ccp:q:combinatorial`,
`ccp:q:profile`, `ccp:q:uniform`, `ccp:q:certified`, `ccp:q:recurrences`,
`ccp:q:sketches`, `ccp:q:literature`; and `ccp:prop:disk`. The report has
71 labels; a build of the delivered text and of this one give every
delivered label the same number.

The write also added the `[write]` notes: status and trust boundary (title
page); the literature-status caveat after Theorem 1.1; provenance,
repository relations, the notation table and the collected non-claims (end
of Section 1); condensed-proof notes after Theorems 5.1 and 6.1; credits in
Sections 7, 8 and 9; Proposition 8.2; the shipped layout and intake reruns
(end of Section 11); and Section 12.1. No statement, proof or number of the
manuscript was changed. After the write, the intake's independent check
added an unlabelled dated paragraph at the end of Section 12.1 and sharpened
the write's own profile statement in Question 2 (dated note there); no label
was added or renumbered.

## Files

```text
README.md                                 this guide (replaces the delivery README)
article.tex                               the report (delivered source/permutomino_asymptotics_standalone.tex; labels prefixed, [write] notes, Section 12.1)
article.pdf                               compiled report, 21 pages
verification-README.md                    the verifier's README (delivered verification/README.md)
code/build_local.sh                       Debian/TeX Live build of the modular source (delivered source/build_local.sh)
code/render_validation_tables.py          writes validation_summary.tex from verification_results.json (delivered verification/)
code/verify_a196275.py                    exact and high-precision verifier (delivered verification/)
data/oeis_b196275.txt                     frozen OEIS b-file, n = 1..200, fetched 2026-10-02 (delivered verification/); CC BY-SA 4.0
data/run_manifest.json                    receipt of the normal and -O runs, sentinels, hashes (delivered verification/)
data/source_manifest.json                 URLs and SHA-256 of the b-file and of Tomás's PDF (delivered verification/)
data/validation_summary.tex               renderer output, raw (delivered verification/)
data/verification_results.json            recorded verifier output, python (delivered verification/)
data/verification_results_optimized.json  recorded verifier output, python -O (delivered verification/)
```

Every file except `README.md`, `article.tex` and `article.pdf` is
byte-identical to the delivery.

**Not shipped**, all recoverable from the arrival commit's archive:

- `pdf/permutomino_asymptotics.pdf`, the delivered 14-page PDF (364,318
  bytes);
- `source/permutomino_asymptotics.tex` (34,553 bytes) and
  `source/validation_summary.tex` (4,305 bytes): the modular edition of the
  same text, of which `article.tex` is the inlined form (the fragment
  differs from `data/validation_summary.tex` only in writing `𝓔` for `F` on
  four lines; the standalone file inlines it without its final blank line);
- `manifest.json` (2,218 bytes), a checksum manifest of all 17 delivered
  files (repository policy ships no checksum manifests; verified 17/17);
- the delivery README (2,690 bytes), staged at placement and replaced by
  this guide (its content is kept under "From the delivery README" below);
- **the two exact-count tables**
  `verification/verification_results_exact_counts.json` and
  `verification/verification_results_optimized_exact_counts.json`, each
  1,263,683 bytes and byte-identical (SHA-256 `4cb8a02e9a18…`): heavy and
  regenerable, see the next section.

**Delivered text that names the delivery layout or files not shipped.**
`verification-README.md` lists the two exact-count tables, `tomas2015.pdf`
and its extracted text (never delivered: "local source-review materials"),
and says to run from `verification/`; `data/source_manifest.json` names
`tomas2015.pdf`; `data/run_manifest.json` hashes the two exact-count tables
and the verifier README under its delivered name `README.md`; the result
JSONs name their companion tables in `exact_counts_file`;
`code/build_local.sh` builds `permutomino_asymptotics.tex` (not shipped) and
writes `../pdf/`. The scripts locate their inputs relative to themselves:
`verify_a196275.py` reads `oeis_b196275.txt` from its own directory and, by
default, writes `verification_results.json` and
`verification_results_exact_counts.json` there; `render_validation_tables.py`
reads `verification_results.json` and writes `validation_summary.tex` in its
own directory. **Flattening into `code/` and `data/` breaks these paths**,
so nothing runs in place; use the routes below.

**Third-party data.** `data/oeis_b196275.txt` (and the OEIS terms recorded in
the result files) are from The On-Line Encyclopedia of Integer Sequences
(https://oeis.org/A196275; the entry credits the table to Václav Kotěšovec,
computed by Anthony J. Guttmann). OEIS content is published by The OEIS
Foundation Inc. under the Creative Commons Attribution-ShareAlike 4.0
licence (CC BY-SA 4.0); this file is third-party data under that licence,
not MIT-0 like the rest of the repository.

## Reconstructing the excluded data

The two 1.26 MB exact-count tables were excluded at placement as heavy and
regenerable (Vladimir, 2 October 2026: "Exclude heavy regenerable
artifacts"). Three ways to get them back:

1. **Retrieve** them from the arrival commit:

   ```sh
   T=$(mktemp -d)
   git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A196275_Exact_Asymptotics_and_Inversion_Source.zip > "$T/a.zip"
   cd "$T" && unzip -j a.zip a196275/verification/verification_results_exact_counts.json \
                            a196275/verification/verification_results_optimized_exact_counts.json
   sha256sum verification_results_*exact_counts.json   # both 4cb8a02e9a1855bb…6a205a4ded
   ```

2. **Regenerate the table alone** from the shipped verifier, in seconds
   (tested at the write: 4 s, byte-identical, SHA-256 `4cb8a02e…`). It
   imports the verifier's own `triangle` and writes the table in the
   verifier's format (needs mpmath and SymPy, which the verifier imports):

   ```sh
   R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196275-column-convex-permutominoes
   T=$(mktemp -d); cp "$R/code/verify_a196275.py" "$T/"; cd "$T"
   python3 - <<'EOF'
   import importlib.util, json
   spec = importlib.util.spec_from_file_location('v', 'verify_a196275.py')
   v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
   a, _ = v.triangle(1000)
   with open('verification_results_exact_counts.json', 'w', newline='\n') as fh:
       fh.write(json.dumps({str(n): str(a[n]) for n in range(1, 1001)}, indent=2) + '\n')
   EOF
   ```

   The optimized-run table is the same bytes under the name
   `verification_results_optimized_exact_counts.json`.

3. **Rerun the full verifier** (route A or B below): it writes
   `<output stem>_exact_counts.json` beside its `--output` file, after its
   exact checks and before the quadratures. The full run took 9 min 13 s at
   the intake under heavy load. On Windows the output has CRLF line endings;
   strip CRs before comparing.

## Rerun the checks (on a scratch copy)

Requirements: Python 3.12 or later, mpmath 1.3.0 and SymPy 1.14.0 (for
example `uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 python`).
The verifier makes no network request. Never run anything in the
repository: the defaults write beside the scripts and would overwrite the
shipped records.

**Route A, delivered layout** (restore `a196275/` from the arrival commit):

```sh
T=$(mktemp -d)
git -C /path/to/ProveIt show 60f54ea06:docs/incoming/A196275_Exact_Asymptotics_and_Inversion_Source.zip > "$T/a.zip"
cd "$T" && unzip -q a.zip && cd a196275
python3 -c "import json,hashlib; m=json.load(open('manifest.json')); print(all(hashlib.sha256(open(p,'rb').read()).hexdigest()==h for p,h in m['files'].items()))"   # True
cd verification
python3 verify_a196275.py --output "$T/normal.json"            # also writes $T/normal_exact_counts.json
python3 -O verify_a196275.py --output "$T/optimized.json"
cmp "$T/normal_exact_counts.json" verification_results_exact_counts.json
python3 render_validation_tables.py                             # rewrites the extracted copy's validation_summary.tex
```

`$T/normal.json` should equal `verification_results.json` except for
`exact_counts_file` and `software.python`. `--quick` skips the mixed-sector
and continuous-inverse quadratures; `--max-n`, `--gf-n` and `--round-n` set
the finite ranges (defaults 1000, 250, 200).

**Route B, from the shipped files** (recreate the verifier's neighbourhood):

```sh
R=/path/to/ProveIt/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196275-column-convex-permutominoes
T=$(mktemp -d)
cp "$R/code/verify_a196275.py" "$R/code/render_validation_tables.py" \
   "$R/data/oeis_b196275.txt" "$R/data/verification_results.json" "$T/"
cd "$T"
python3 render_validation_tables.py && cmp validation_summary.tex "$R/data/validation_summary.tex"
mkdir out && python3 verify_a196275.py --output out/verification_results.json
```

The renderer step was run this way at the write (about 1 s; identical after
CR stripping on Windows). The verifier step was run at placement on the
delivered layout (route A) and not repeated.

## Build the PDF

pdfLaTeX (amsmath, amssymb, amsthm, mathtools, lmodern, microtype,
geometry, hyperref, xurl, booktabs, array, enumitem, graphicx, fancyvrb, and
longtable for the write's notation table); the bibliography is embedded.
Build in a scratch copy:

```sh
B=$(mktemp -d); cp article.tex "$B/"; cd "$B"
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built this way with MiKTeX (rebuilt on
5 October 2026 after the independent check with three pdfLaTeX passes;
every label keeps its number and page): 21 pages; no errors or
warnings, no undefined references or citations, no multiply defined labels,
no duplicate PDF destinations, no overfull or underfull boxes. The delivered
source built the same way gives 14 pages, equally clean. The article keeps
the delivered preamble lines that suppress PDF dates and trailer
identifiers.

## From the delivery README

The delivery README (replaced by this guide) summarized the report as
proving "the exact factorial-normalized generating function, exact
Lambert-W growth constant and prefactor, positive spectral representation,
complete mixed secondary asymptotics, specified interpolation's convergent
inverse sectors, all-positive-index inverse rounding, and
non-P-recursiveness", with numerical tests as "supporting checks, not the
proof" and a literature search that "does not establish exhaustive
novelty". Its instructions, translated to the shipped names:

- *Compile:* run `pdflatex` twice on the standalone source (here
  `article.tex`; see "Build the PDF"). `build_local.sh` (here
  `code/build_local.sh`) reproduces the delivered modular PDF in the
  source's Debian/TeX Live environment, with a locally generated format, a
  fixed `SOURCE_DATE_EPOCH` and three passes; it writes `build/` and
  `../pdf/permutomino_asymptotics.pdf` and needs the unshipped modular
  source, so it runs only in a restored `a196275/source/`.
- *Reproduce:* `python verify_a196275.py`, then
  `python -O verify_a196275.py --output verification_results_optimized.json`,
  then `python render_validation_tables.py`, all from `verification/` (here:
  routes A and B above, with explicit output paths). "Both normal and
  optimized-mode runs passed"; the two exact-count outputs are identical
  and were both retained "to document the independent normal and optimized
  runs" (neither is shipped here; see above).
- *Symbols:* the renderer's `F` is the article's `𝓔` (see "Notation").
- *Sources:* "Third-party article PDFs, extracted text, and page images are
  not redistributed." `source_manifest.json` records the hashes of Tomás's
  PDF and the OEIS table; `manifest.json` (not shipped) recorded all
  delivered file hashes. The report is "an analytical derivation, not a
  claim of formal proof-assistant verification or certified interval
  quadrature."

## Provenance

- Sources cited by the manuscript: Beaton, Disanto, Guttmann and Rinaldi,
  DMTCS Proc. AO (FPSAC 2011) 111–122; Tomás, FCT 2015, Section 5.2;
  OEIS A196275 (accessed 2 October 2026); Rinaldi and Socci, Electron. J.
  Combin. 21(1) (2014) P1.35; Duchi, Rinaldi and Socci, J. Comb. 9(1) (2018)
  57–94; Duchi, arXiv:1904.02691; DLMF §§4.13, 5.11.
- Repository input: none; the package names no ProveIt commit or path.
- Batch 101 of `docs/incoming`, bundle Report 96; arrival `60f54ea06`,
  placement `f7c612c72`, written 5 October 2026. Single source, so the write
  made no merge choices. The delivered modular edition and the standalone
  file are the same text; the standalone file was staged as `article.tex`.
