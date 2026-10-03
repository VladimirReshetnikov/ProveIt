# Historic Tree Asymptotics and a High-Order Obstruction

**Reduced 5- and 7-historic trees (OEIS A333497, A336009): factorial-pole
equivalents with logarithmically oscillating corrections to every fixed grade,
and the failure of Burghart–Wagner's Conjecture 1 for every order `m ≥ 29`**

A research report dated 2 October 2026, built from one manuscript. Its author
line reads only "Research article and reproducibility report"; the delivery
names no author and no tool, and the PDF metadata has an empty Author field.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 77, manuscript 24 | `historic-tree-report.zip` (wrapper directory `historic-tree-release/`), arrival commit `096ee7b87`; main file `historic-trees.tex`, now `article.tex`, with its `\input` file `extensions.tex` | none: no ProveIt commit is named and no repository path is continued | `34f1acd4b` | the whole report |

**Status:** presumed AI-assisted (the delivery names neither an author nor a
tool), unrefereed, not formalized: no Lean or Rocq declaration exists for any
statement of this report. Exact rational and integer certificates corroborate
the finite algebraic identities and the finite spectral bridge; the fitted
constants, residual tables and figure are exploratory and not interval
certified.

## What it proves

`h_n` are the exponential coefficients of the solution of `H''' = H²`,
`H(0) = H'(0) = H''(0) = 1` (reduced 5-historic trees, OEIS A333497, by
recurrence: 1, 1, 1, 1, 2, 4, 8, 18, 48, 144, …). The order-`r` all-one family
`H_r^(r) = H_r²` has conjecture parameter `m = r − 1` and historic-tree order
`2m + 1`.

- **Theorem 1.1 (A333497).** `H` has a finite positive blowup point `ρ` with
  `180^(1/4) ≤ ρ ≤ 60^(1/3)`, the unique singularity on its circle of
  convergence, and a convergent local expansion
  `H = 60 t^(-3) 𝓕(C t^λ, C̄ t^λ̄)`, `t = ρ − z`, `λ = (13 + i√71)/2`,
  `C ≠ 0`. For every fixed grade `d`,
  `h_n / (30 (n+2)! ρ^(-n-3)) = Q_d(n) + O(n^(-13(d+1)/2))` with exact Gamma
  ratios in `Q_d`.
- **Corollary 1.2 (oscillation).** `R_n − 1 = 2|K| n^(-13/2) cos(arg K − ω log n)
  + O(n^(-15/2))`, `ω = √71/2`, `K ≠ 0`; so `R_n − 1` changes sign infinitely
  often and is not `O(n^(-7))`.
- **Theorem 7.1 (inverse).** An eventual shrinking two-ceiling window for
  `N(X) = min{n : h_n ≥ X}` at every fixed grade, with existence constants;
  a Lambert-W starting value and the first oscillatory displacement.
- **Theorem 8.1 (A336009, `G'''' = G²`).** `g_n = 140 (n+3)! ρ_4^(-n-4)
  (1 + O(n^(-11/2)))`, a convergent three-mode local expansion with the exact
  real-mode coefficient `D = −1/18052070400` (from the conserved energy
  `1/6`), a nonzero complex amplitude (backward Metzler argument), all fixed
  grades and inverses.
- **Theorem 9.1 (obstruction).** For every ODE order `r ≥ 30` no `ρ > 0`
  gives `h_n^(r) ~ ((2r−1)!/((r−1)!)²) (n+r−1)! ρ^(-n-r)`: Burghart and
  Wagner's Conjecture 1 (Theor. Comput. Sci. 1070 (2026), Section 4) is false
  for every `m ≥ 29`. Method: an unstable conjugate pair (exact rational
  bridge for `30 ≤ r ≤ 37`, rational inequalities for `r ≥ 38`), a closed
  sign-variation cone containing the actual orbit, strict sign-regularity of
  order three, and a generalized stable manifold.
- Lemma 8.2: finite positive blowup for every order `r ≥ 2`.

## What is not claimed

- No replacement high-order asymptotic and no periodic limiting profile for
  `m ≥ 29`; no claim that `m = 29` is the first failure (the orders
  `4 ≤ m ≤ 28` are unresolved); Conjecture 2 (even order) is not addressed.
- Numerical constants (`ρ ≈ 3.77462757572068`, `C`, `K`) are fitted and not
  interval certified; no infinite transferred coefficient sum at fixed `n` is
  asserted; the inverse constants `M_d`, `X_d` are existence constants and no
  unconditional ceiling rule is claimed.
- Credited, not claimed: Astashova's real-axis blowup laws (2013, Theorem 3,
  orders 3 and 4), the B-urn spectral family (Chauvin–Gardy–Pouyanne–Ton-That
  2016, Section 4.1), Kozlov's large-order instability (1999, Lemma 5.3), the
  sign-regularity theorems (Weiss–Margaliot 2021; Alseidi–Margaliot–Garloff
  2019) and Lanford's generalized stable manifold. The obstruction's new
  ingredient is the orbit-specific sign-variation constraint.
- Priority rests on "a bounded negative finding, not an exhaustive priority
  certificate" (source check of 2 October 2026).
- **Claims about external sources, kept as the manuscript's:** Theorem 9.1
  refutes a published conjecture; Section 11 says the journal's Table 1 heads
  its column `ρ_m^(-1)` but lists the radius `3.7746` (a reciprocal-label
  error). The intake checked the conjecture's constants
  `30 = 5!/(2!)²`, `140 = 7!/(3!)²`, recomputed the exact gaps `20/2997` and
  `392864/776223`, and reran the certificates; it did not re-read the
  journal's table.
- **The inversion is an instance of repository results; no novelty is
  claimed for the method.** The Lambert start is `p0:thm:lambert-core`
  (`a = b = 1` for `u = log(x/(eρ))`, branch `W_0`), the two-ceiling window has
  the form of the separation condition, part (2) of `p0:thm:staircase`, and the
  first oscillatory displacement is the first-order term of
  `p0:thm:perturbed-inversion`, all in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/transseries_and_inversion.tex`.
  A dated `[write]` note at the end of Section 7 says so.

## Relation to the repository

**Formal status.** No statement of this report is formalized in Lean or Rocq,
and its place in the collection gives it no formal status; the manuscript used
no ProveIt theorem. The generic staircase arithmetic named in the Section 7
note is formalized as `Fabius.staircase_ceil` and `Fabius.staircase_separation`
in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`; those
lemmas concern an arbitrary monotone function, not `h_n`.

**Neighbouring reports.** None: no other repository report treats historic
trees, B-tree histories, A333497, A336009 or the Burghart–Wagner conjectures
(searched at placement). Batch 77 delivered several other tree reports to this
collection (galled trees, tree-child networks, relaxed and compacted trees,
bounded identity trees); they share only generic singularity analysis with
this one.

## Notation

The manuscript reuses letters with section-local meanings (`ρ` four ways; `a`,
`A`, `B`, `b`, `D`, `K`, `P`, `Q`, `R`, `s`, `L`, `η`, `W`/`Z` two to four ways
each; `G` is both the A336009 generating function and, in Section 9, the
comparison pole `A_r(ρ−x)^(-r)`). A table in the first `[write]` note (end of
Section 1) fixes each symbol by section, with the tempting false readings. No
symbol was renamed.

## Labels

Every label carries the prefix `his:`. The manuscript's 106 labels (66 in
`article.tex`, 40 in `extensions.tex`) were prefixed before anything cited them
(every `\ref`/`\eqref` updated in both files), and ten section labels
`his:sec:…` were added for the notes: 116 labels in all. The writing step also
added three dated `[write]` notes (Section 1: provenance, external-source
claims, notation table; Section 7: the transseries-instance note; Section 10.3:
the shipped layout). No statement, proof or number of the manuscript was
changed; `extensions.tex` differs from the delivery only by its label prefixes.

## Files

```text
README.md                                   this guide (replaces the delivery README)
REPRODUCIBILITY.md                          delivered replay guide (delivery paths; see below)
article.tex                                 the report (delivered as historic-trees.tex)
extensions.tex                              Sections 8-9, \input by article.tex (labels prefixed)
references.bib                              delivered bibliography (BibTeX)
article.pdf                                 compiled report, 28 pages
figures/oscillation.pdf                     the article's figure (exploratory)
figures/oscillation.csv                     its data, written by make_figure.py (CRLF, kept by a -text line)
code/build.sh                               delivered PDF build (compiles historic-trees.tex in its own directory)
code/replay.sh                              delivered replay entry point (runs code/run_replay.py)
code/run_replay.py                          replay driver: provenance check, ten stages, comparison summary
code/make_figure.py                         figure/CSV regeneration (needs matplotlib)
code/verify_symbolics.py                    exact symbolic checks; h_0..h_202
code/numerical_expansion.py                 120- and 150-digit fits of rho, Re C, Im C
code/verify_inverse.py                      exploratory inverse experiments
code/independent_checks.py                  independent exact h_0..h_600, rational recurrence, DOP853 ODE
code/extensions-verify_stability.py         Routh certificates r = 2..40, root counts, compound graph, finite bridge
code/extensions-verify_audit.py             independent order-30 certificate
code/extensions-verify_r4_checks.py         exact order-4 supplement
code/extensions-verify_phase.py             independent finite-bridge phase/modulus check
code/extensions-verify_uniform_constants.py rational constants for r >= 38
data/producer-exact_values_0_202.json                    exact h_0..h_202
data/producer-symbolic_validation.json                   exact symbolic checks
data/producer-numerics_120dps.json                       120-digit fit (exploratory)
data/producer-numerics_150dps.json                       150-digit fit (exploratory)
data/producer-inverse_validation.json                    inverse experiments (exploratory)
data/independent-exact_h_0_600.txt                       exact h_0..h_600 (SHA-256 aa02b70d…bf635, as printed in Section 10.1)
data/independent-independent_checks.json                 independent checks (mixed exact/float)
data/extensions-routh_certificates_2_40.json             exact Routh certificates, orders 2..40
data/extensions-independent_complex_root_counts.json     exact complex root counts at orders 29, 30
data/extensions-compound_graph_certificate.json          order-30 third-compound graph
data/extensions-certificate.json                         independent order-30 certificate
data/extensions-rational_phase_certificates_30_37.json   finite-bridge phase/modulus margins
data/extensions-phase_certificate.json                   independent phase check
data/extensions-phase_finite.json                        second original phase reference
data/extensions-r4_exact_certificate.json                exact order-4 supplement
data/extensions-exact_h_r4_0_100.json                    exact g_0..g_100 (A336009)
data/extensions-uniform_threshold_certificate.json       rational constants for r >= 38
data/provenance.json                        original and bundled SHA-256 of scripts and reference artifacts
data/verified_replay.json                   earliest replay snapshot (order 3)
data/verified_extension_replay.json         intermediate snapshot (orders 4 and 30)
data/verified_final_replay.json             final replay snapshot
data/requirements.txt                       mpmath 1.3.0, sympy 1.14.0, numpy 2.3.5, scipy 1.17.0
data/requirements-figure.txt                adds matplotlib 3.10.8
```

Every file except `README.md`, `article.tex`, `extensions.tex` and
`article.pdf` is byte-identical to the delivery. Placement renamed
`historic-trees.tex` to `article.tex`, moved `build.sh`, `replay.sh` and
`make_figure.py` to `code/`, flattened `code/extensions/` to
`code/extensions-*.py` and `data/{producer,independent,extensions}/` to
`data/<subdirectory>-*`, and moved both requirements files to `data/`.
Not shipped: the delivered 26-page PDF `historic-trees.pdf` and
`MANIFEST.sha256` (a checksum ledger, verified 44/44 at placement and
retired). Both survive in the archive:
`git show 096ee7b87:docs/incoming/historic-tree-report.zip > <scratch>/historic-tree-report.zip`.
Nothing heavy was excluded: the largest data file is the 286 KB exact table.

Delivered text that names the delivery layout or unshipped files:
`REPRODUCIBILITY.md` (`./replay.sh`, `requirements.txt`, `data/producer/…`,
`code/extensions/…`), `code/build.sh` (compiles `historic-trees.tex`),
`code/replay.sh` and `code/run_replay.py` (expect `code/` and
`data/{producer,independent,extensions}/` under one root, and
`data/provenance.json` records those paths), `code/make_figure.py` (reads
`data/producer/…` and `data/independent/…` relative to its own directory and
rewrites `figures/oscillation.{csv,pdf}` there), and Sections 10.1 and 10.3 of
the article (`bash replay.sh`, `bash build.sh`, `MANIFEST.sha256`; the second
has a dated note). The delivery README, which this guide replaces, listed
`MANIFEST.sha256` and began its replay with `sha256sum -c MANIFEST.sha256`.

Byte-level notes. `figures/oscillation.csv` is the only CRLF file
(Python's `csv.writer` output, 522 CRLF lines); the line
`.../a333497-historic-trees/figures/oscillation.csv -text` in
`SetTheory/Cardinals/.gitattributes` keeps its bytes. Five JSON certificates
(`data/extensions-{compound_graph_certificate,independent_complex_root_counts,phase_finite,rational_phase_certificates_30_37,routh_certificates_2_40}.json`)
have no final newline; keep them so, because `data/provenance.json` hashes the
exact bytes.

## Rerun the checks (on a scratch copy)

The scripts use delivery-relative paths, and `run_replay.py` first checks every
script and reference artifact against `data/provenance.json` at its delivered
path. Rebuild the delivered layout on a copy, then replay into an empty
directory outside it (Git Bash, from this directory):

```sh
R=$(mktemp -d)/historic-tree-release
mkdir -p "$R"/code/extensions "$R"/data/producer "$R"/data/independent "$R"/data/extensions "$R"/figures
for f in code/*; do b=${f#code/}; case $b in
  extensions-*) cp "$f" "$R/code/extensions/${b#extensions-}";;
  make_figure.py|build.sh|replay.sh) cp "$f" "$R/$b";;
  *) cp "$f" "$R/code/$b";; esac; done
for f in data/*; do b=${f#data/}; case $b in
  producer-*) cp "$f" "$R/data/producer/${b#producer-}";;
  independent-*) cp "$f" "$R/data/independent/${b#independent-}";;
  extensions-*) cp "$f" "$R/data/extensions/${b#extensions-}";;
  requirements*) cp "$f" "$R/$b";;
  *) cp "$f" "$R/data/$b";; esac; done
cp figures/* "$R/figures/"; cp article.tex "$R/historic-trees.tex"; cp extensions.tex references.bib "$R/"
cd "$R"
PYTHONUTF8=1 uv run --no-project --with mpmath==1.3.0 --with sympy==1.14.0 \
  --with numpy==2.3.5 --with scipy==1.17.0 python code/run_replay.py --output-dir "$(mktemp -d)"
```

(`bash replay.sh` from `$R` does the same with `python3`.) The driver never
writes into the release tree and checks that the shipped data are unchanged.
At intake (2 October 2026, heavily loaded machine) one call took 143 s and all
ten stages exited 0 with matching provenance hashes. **On Windows the driver
reports `FAIL`**: the producers write with `Path.write_text`, which emits CRLF
there, while `run_replay.py` compares bytes against LF references. Byte
identity holds on POSIX; on Windows compare after CRLF→LF — at intake all
twelve exact artifacts (including `exact_h_0_600.txt` and
`routh_certificates_2_40.json`) and the three producer float JSONs were then
byte-identical, and the only other difference was the last digit of the
double-precision `rho_approx` in `independent_checks.json`. Regenerating the
figure (`python make_figure.py` in `$R`, needs `requirements-figure.txt`)
rewrites `figures/oscillation.{csv,pdf}` in the copy only.

## Build the PDF

pdfLaTeX and BibTeX (amsmath, amssymb, amsthm, mathtools, booktabs, graphicx,
microtype, enumitem, hyperref, lmodern). From this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The committed PDF was built in a scratch directory with MiKTeX: 28 pages, no
errors or warnings (LaTeX or BibTeX), no undefined references or citations, no
multiply defined labels, no duplicate PDF destinations, no overfull or
underfull boxes. (The delivered source built to 26 pages, also clean.)
`code/build.sh` is kept as delivered; to use it, copy it to a scratch
directory together with `article.tex` renamed to `historic-trees.tex`,
`extensions.tex`, `references.bib` and `figures/`.

## Provenance

- Burghart–Wagner, Theoret. Comput. Sci. 1070 (2026) 115821 (Conjecture 1),
  and AofA 2024, LIPIcs 302, 10 (Conjecture 10); Astashova, Adv. Difference
  Equ. 2013:220 and St. Petersburg Math. J. 31 (2020); Kozlov, Ark. Mat. 37
  (1999); Chauvin–Gardy–Pouyanne–Ton-That, ALEA 13 (2016); Weiss–Margaliot,
  Automatica 123 (2021); Alseidi–Margaliot–Garloff, J. Math. Anal. Appl. 474
  (2019); Lanford, ETH lecture notes (1997); Ilyashenko–Yakovenko (2008);
  Flajolet–Sedgewick (2009); OEIS A333497, A336009 (inspected 2 October 2026).
- Repository input: none recorded; no pin.
- Batch 77 of `docs/incoming`, manuscript 24 (cluster P3); arrival
  `096ee7b87`, placement `34f1acd4b`, written in the batch-77 write phase
  (2 October 2026). Single source, so the write made no merge choices.
