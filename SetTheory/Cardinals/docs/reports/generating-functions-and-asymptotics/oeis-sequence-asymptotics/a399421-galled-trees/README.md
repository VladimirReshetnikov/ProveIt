# Galled Trees by Gall Count (OEIS A399421)

**The cube-root crossover, positive density, and the near-maximal endpoint**

This research report was built on 2 October 2026 from three manuscripts of
batch 77. They count one triangle: g(n,k), the number of rooted binary,
nonplane, unlabeled simplex time-consistent galled trees with n leaves and k
galls (OEIS A399421; row sums A397952), defined by equation (47) of
Agranat-Tamir, Fuchs, Gittenberger, Rosenberg and Seetharaman (Adv. Appl.
Math. 180 (2026) 103131). Each manuscript treats a different range of the gall
count. All three are dated 2 October 2026 and name no author: the author lines
read "Mathematical research report" (sources 21 and 22) and "Research report"
(source 23).

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 21 | 21 | `galled-crossover-reproducibility.zip` (`galled_crossover.tex`, 676 lines, 18-page PDF) | none | `34f1acd4b` | Part I, Sections 2–11 |
| 22 | 22 | `galled-density-reproducibility.zip` (`galled_density.tex`, 778 lines, 20-page PDF) | ProveIt `4b874cea0` (the two repository sources it credits as methodology) | `34f1acd4b` | Part 0 (its Subsections 1.1–1.2), Part II, Sections 12–22, Appendix A |
| 23 | 23 | `galled-endpoint-report.zip` (`manuscript/endpoint.tex`, 678 lines, 18-page PDF) | none | `34f1acd4b` | Part III, Sections 23–33, Appendix B |

All three archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive>`). Source 22 is the base: it
has the fullest model section, the support proposition, the global nested
analyticity, the prior-work discussion, and it poses the other two regimes as
its open questions. Source 23's `data/provenance.json` records the hash of
source 22's frozen triangle file, and its `triangle.py` says it was
"refactored from independent_rows.py", source 22's row generator: the three
come from one research workspace. None proves a theorem of another.

A fourth archive of the same arrival, `galled-crossover-reproducibility (1).zip`
(batch-77 manuscript 20; `galled_crossover.tex`, 465 lines, 14-page PDF), is
the earlier leading-order release of source 21. Source 21's delivery README
mentions it only as "the previously released leading-crossover report", which
"is preserved separately in the working archive". Source 21 keeps every
theorem, proof step, number and reference of archive 20 and answers its one
further question ("The next crossover coefficient") by its all-orders
theorem; 16 of archive 20's 21 files are byte-identical in archive 21.
Archive 20 is superseded: nothing of it is printed or shipped, and it survives
in commit `096ee7b87`.

Every result, proof, example, remark, question and limitation of the three
manuscripts is printed. The generating function, the support proposition and
the exact integer recursion, which all three state or use, are printed once
(Part 0).

**Status: AI-assisted, unrefereed, not formalized.** No Lean or Rocq
declaration exists for any statement of this report. The decimal constants
are high-precision evaluations, not interval enclosures, and no remainder
constant is effective.

## Files

```
article.tex        the merged report, standalone LaTeX with an internal bibliography (no \input)
article.pdf        the compiled report, 62 pages: title page and contents 1–4, Guide 5–9,
                   Part 0 10–11, Part I 11–27, Part II 27–43, Part III 43–59,
                   "Across the three regimes" 59–60, Appendices A–B 60–61, references 61–62
README.md          this guide

Source 21 (Part I), files from galled-crossover-reproducibility.zip, delivered under galled-crossover-report/
code/21-crossover-enumerate_rows.py            exact integer triangle through n = 160; checks the reference rows,
                                               49 A399421 cells, 28 A397952 terms, the gall-free column
code/21-crossover-check_algebra.py             symbolic checks of the quartic, local critical branches, pressure, constant
code/21-crossover-numerics.py                  70-digit constants, 16 crossover comparisons, cutoff/precision stability
code/21-crossover-finite_gaussian_generator.py finite Gaussian/Bernoulli transfer generator; evaluates P0, P1
code/21-crossover-verify_p1_symbolic.py        critical-pressure, amplitude, Gaussian/Stirling and P1 identities
code/21-crossover-independent_constants.py     nested-radical constants without row coefficients
code/21-crossover-exact_truncated_rows.py      exact rows modulo u^13 through n = 640 (reads an EXCLUDED file, see below)
code/21-crossover-validate_p1.py               P1 diagnostics from those rows (reads an EXCLUDED file, see below)
code/21-crossover-reproduce.sh                 delivered replay (calls the unshipped build_pdf.sh at the end)
data/21-crossover-reference-rows.json          exact rows and totals through n = 160 (the one shipped copy of the triangle)
data/21-crossover-oeis-numeric-fixture.json    49 A399421 cells and 28 A397952 terms from the inspected OEIS records
data/21-crossover-requirements.txt             mpmath, sympy
data/21-crossover-results-algebra-checks.json  recorded outputs (delivered results/):
data/21-crossover-results-checks-table.tex       Table 1 of the article (printed inline there)
data/21-crossover-results-crossover-checks.json
data/21-crossover-results-exact-checks.json
data/21-crossover-results-finite-generator.txt
data/21-crossover-results-independent-constants.json
data/21-crossover-results-numerical-replay.txt
data/21-crossover-results-p1-diagnostics.json
data/21-crossover-results-p1-symbolic.txt
data/21-crossover-results-p1-table.tex           Table 2 of the article (printed inline there)
data/21-crossover-results-stability.json
data/21-crossover-results-truncated-checks.json
data/21-crossover-results-truncated-replay.txt

Source 22 (Part II, the base), files from galled-density-reproducibility.zip, delivered under galled-density-reproducibility/
22-density-README_REPLAY.md                    delivered replay guide (commands, tolerances, provenance)
code/22-density-independent_rows.py            exact bivariate rows through n = 160 and finite-size statistics
code/22-density-derive.py                      critical constants, Puiseux coefficients to degree 13, d_1..d_5
code/22-density-density_checks.py              saddle checks at densities 0.1, 0.2, 0.3 (55 digits)
code/22-density-check_amplitude.py             independent scalar amplitude diagnostic (85 digits)
code/22-density-replay.py                      replay driver (writes only to its own output folder)
code/22-density-replay.sh                      location-independent entry point for replay.py
code/22-density-verify_results.py              exact and tolerance comparisons with the frozen outputs
code/22-density-verify_manifest.py             checks the unshipped MANIFEST.sha256
code/22-density-reproduce.sh                   delivered wrapper: manifest, replay, PDF of galled_density.tex
code/22-density-build_pdf.sh                   delivered PDF build of galled_density.tex
data/22-density-oeis-reference.json            public OEIS integers (28 + 49) with source notes
data/22-density-requirements.txt               mpmath==1.3.0, sympy==1.14.0
data/22-density-results-expected-README.md     readme of the frozen outputs (delivered results/expected/):
data/22-density-results-expected-amplitude-check.json
data/22-density-results-expected-constants.json
data/22-density-results-expected-density-checks.json
data/22-density-results-expected-density-numerics.txt
data/22-density-results-expected-numerics.txt
data/22-density-results-expected-stability-cutoff120-dps80.json   (delivered results/expected/stability/)
data/22-density-results-expected-stability-cutoff160-dps60.json   (delivered results/expected/stability/)
data/22-density-results-expected-stability-summary.json
data/22-density-results-expected-triangle-verification.json
data/22-density-results-validated-runtime.json       release-validation summaries (delivered results/)
data/22-density-results-validated-verification.json

Source 23 (Part III), files from galled-endpoint-report.zip, delivered under galled-endpoint-report/
code/23-endpoint-code-README.md                delivered code/README.md: methods, inputs, numerical limits
code/23-endpoint-triangle.py                   exact triangle through n = 160 from equation (47)
code/23-endpoint-critical_jets.py              independent U and critical Taylor jets at truncations 220, 320
code/23-endpoint-all_orders.py                 finite-K symbolic generator, gamma-ratio and Puiseux helpers
code/23-endpoint-ratios.py                     16 exact-count comparisons with the leading, C1 and C2 forms
code/23-endpoint-inversion.py                  K = 2 Lambert-W0/Newton model; 6320 monotonicity pairs
code/23-endpoint-verify.py                     recomputes and checks everything (reads an EXCLUDED file, see below)
code/23-endpoint-run_checks.sh                 entry point for verify.py
code/23-endpoint-check_manifest.py             checks the unshipped SHA256SUMS
code/23-endpoint-reproduce.sh                  delivered wrapper (calls the unshipped build_pdf.sh)
data/23-endpoint-first-rows.json               13 low-order reference rows
data/23-endpoint-constants-220.json            critical-jet runs at truncations 220 and 320
data/23-endpoint-constants-320.json
data/23-endpoint-audit-reference-constants.json  earlier independent audit snapshots
data/23-endpoint-ratios.csv                    the 16 cases behind Table 4 of the article (which prints 10)
data/23-endpoint-ratios.json
data/23-endpoint-inversion.json
data/23-endpoint-provenance.json               provenance hashes (names unshipped workspace files, see below)
data/23-endpoint-requirements.txt              mpmath==1.3.0, sympy==1.14.0
data/23-endpoint-checks-constant-agreement.json  recorded check outputs (delivered checks/):
data/23-endpoint-checks-portable-replay.json
data/23-endpoint-checks-portable-replay.log
data/23-endpoint-checks-replay.log
data/23-endpoint-checks-summary.json
data/23-endpoint-checks-symbolic-through-C4.json
data/23-endpoint-checks-symbolic.json
data/23-endpoint-checks-triangle-checks.json
data/23-endpoint-verif-clean-replay.json       release verification records (delivered verification/)
data/23-endpoint-verif-visual-qa.json
```

That is 82 files: the three report files, one delivered Markdown guide at the
root, 29 files in `code/` and 49 in `data/`. Every delivered file is
byte-identical to its archive.

**Delivery names.** The slugs are `crossover` (21), `density` (22) and
`endpoint` (23). Scripts and build files, from the package root or its
`code/`, are shipped as `code/NN-<slug>-<name>`. Outputs and inputs at
`<dir>/<name>` are shipped as `data/NN-<slug>-<dir>-<name>`, with the
directory `data/` dropped, nested directories joined by hyphens
(`results/expected/stability/x` is `data/22-density-results-expected-stability-x`)
and `verification/` shortened to `verif`. Exceptions: every requirements file
is `data/NN-<slug>-requirements.txt` (source 22's was in `code/`); source 22's
`README_REPLAY.md` is at the root as `22-density-README_REPLAY.md`; source
23's `code/README.md` is `code/23-endpoint-code-README.md`.
Source 22's `galled_density.tex` became `article.tex` at the placement and is
now the merged report; its delivered `README.md` was the placement's
`README.md` and is replaced by this guide (its content is summarized under
"Notes and discrepancies").

## Labels

Every label carries the prefix `gal:`: `gal:` for Part 0 and the material
written at the merge (the Guide, Section 34, the bibliography notes),
`gal:cx:` for Part I, `gal:dn:` for Part II, `gal:ep:` for Part III. The
article has 222 labels (22 `gal:`, 64 `gal:cx:`, 71 `gal:dn:`, 65 `gal:ep:`),
all unique. The placement commit staged source 22's text as `article.tex`
with 76 unprefixed labels; no label had been cited outside this directory.

## What the report claims

- **Part I (source 21), the cube-root crossover.** Uniformly for k/n^(1/3) in a
  compact subset of (0, ∞),
  g(n,k) = L0(n,k) exp(−2 γ0 k^(3/2)/√n) (1 + O(n^(−1/3))), where L0 is the
  fixed-k expression γ0/(2√π) R^(−n) n^(−3/2) (cn)^(2k)/(2k)! and
  γ0 = 1.130033716398972… (Theorem 2.1). The expansion holds to every fixed
  order in ε = n^(−1/3), with a finite Gaussian-moment generator and the
  explicit first correction P1(λ) = γ0√λ/4 + 𝓑λ², 𝓑 = −0.19668… (Theorem 2.2).
  The proof isolates the physical sheet (a closer critical value of the full
  quartic is not a singularity), transfers on shrinking contours, and shows the
  exact odd cancellation in the Fourier extraction. A leading-order inverse of
  the normalized crossover curve follows.
- **Part II (source 22), positive density.** For k/n in a compact subset of
  (0, 1/2), g(n,k) = ρ(u)^(−n) u^(−k) / (√(2πβ(s)) n²) times an expansion to
  every fixed order in 1/n with explicit generator and explicit Q1
  (Theorem 12.1). The proof establishes strict nested subcriticality, a unique
  critical phase on the bitorus, strict positivity of the tilted variance and
  the full density range (0, 1/2). Consequences: CLT with mean
  0.19741431 n and variance 0.05548588 n, local CLT, precise interior large
  deviations, logarithmic inverse models and q-spaced integer brackets. It
  also records that the inspected arXiv and author versions of the source
  paper print γ ≈ 0.3846 where the defining equation gives
  0.3835758866628… (the value already credited on OEIS to V. Kotěšovec).
- **Part III (source 23), the near-maximal endpoint.** With d = n − 2k − 1 and
  d/√n in a compact subset of (0, ∞),
  g = 2 h* r*^(−n) n^(−3/2) (an)^d/d! e^(βd²/n) {Σ C_j(d/√n) n^(−j/2) + …} to
  every fixed order, with β = −0.821555224599447 and explicit C1, C2
  (Theorem 23.1). The factor 2 comes from the exact parity of two moving
  square-root singularities. Also: the fixed-d formula, joint analyticity of
  the nested equation by an explicit Banach-algebra inverse, and an inverse
  for a supplied integer deficiency (Lambert W0 seed, Newton steps, spacing-two
  brackets, monotonicity checked on all 6320 pairs through n = 160).
- **The merge** adds a Guide (sources, notation dictionary with false
  readings, union of non-claims, repository instances), Part 0, and Section 34,
  which collects the open problem of matching the regimes.

## What the report does not claim

- No uniformity across regimes: each theorem holds on a compact window fixed
  before n → ∞ and for each fixed order. Open: k → ∞ with k = o(n^(1/3));
  n^(1/3) ≪ k ≪ n; √n ≪ d ≪ n; and 0 ≤ d ≤ C√n in one statement
  (Section 34).
- No convergence of the formal series, no uniformity in the order, no
  effective remainder constants, no interval-certified constants, no certified
  finite-n inverse, no monotone floor-ray inverse, no exact ceiling rule, no
  density-free inverse. Only P1 (Part I) and C1, C2 (Part III) are explicit;
  no P2 is given.
- No priority beyond bounded searches. The generating function, the fixed-k
  asymptotic, the scalar leading term, the maximal-gall identity
  (Proposition 9 of Agranat-Tamir et al.) and the corrected scalar amplitude
  (Kotěšovec, on OEIS) are prior work. The cube-root mechanism is prior work of
  Fuchs and Hao Yu for leaf-labeled classes; the shrinking-saddle mechanism is
  classical (Gardy, De Angelis, Lladser). No journal erratum is asserted for
  the γ diagnostic: the journal text was not obtained.
- OEIS terms beyond the displayed 28 + 49 are generated from the recurrence,
  not checked against a b-file.

## Relation to neighbouring reports and to the repository

- **Transseries volume.** Part II's carrier inverse (W₋₁) and Part III's seed
  (W₀) are instances of theorem `p0:thm:lambert-core` of
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`;
  Part II's inverse model is a perturbed reversion (`p0:thm:perturbed-inversion`);
  the lattice brackets of Parts II and III are the separation step of
  `p0:thm:staircase`. Source 22 credits that volume, at its pin `4b874cea0`, as
  prior methodology. The generic separation condition `p0:eq:separation` is
  formalized in Lean as `Fabius.staircase_separation`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`);
  nothing specific to this report is formalized.
- **`a215561-fixed-composition-excursions`** (beside this report): source 22
  credits its Gaussian-moment method for fixed composition as prior
  methodology. Nothing of it is re-proved; the objects differ.
- **Batch-77 siblings.** `a213863-tree-child-networks` treats another class of
  phylogenetic networks (labeled tree-child networks, Airy-type stretched
  exponentials); it shares no lemma with this report. The cube-root paper of
  Fuchs and Hao Yu cited in Part I concerns tree-child and galled networks of a
  different class.
- **Placement confers no formal status.** No Lean or Rocq development in the
  repository treats galled trees or A399421.

## Where the merge had to choose

- **Order and base.** Parts are ordered by gall count (21, 22, 23); source 22 is
  the base.
- **Printed once.** The generating function, the support proposition and the
  integer recursion S = G/(1 − G) are printed once, in Part 0, from source 22's
  Subsections 1.1–1.2. Source 21's statements of them (its §1.1 and the display
  in its §9.1) and source 23's display of equation (47) are replaced by
  references; source 21's sentences that Part 0 lacks are quoted in Remark 1.2.
- **Kept in each Part.** The plane majorant (with different numerical
  supersolutions in Parts I and II), the Bernoulli gamma-ratio generator and the
  square-root transfer generator h_j recur in all three proofs in three
  parametrizations (tilt u = t⁴, u = e^s, u = ε⁻²). They stay where the proofs
  use them; the Guide's notation table identifies them.
- **Notation.** Each Part keeps its source's notation; the Guide's table lists
  every clash (A, B, a, b, c, d, β, γ, Q/q, h/H, K, L, Λ, α, D, ε, t, λ, and
  the two different "Fuchs–Yu" papers) with the tempting false reading. One
  symbol is renamed: source 22's A = −log R (Section 19.2) is Λ_R. Source 22's
  "Fuchs and Yu" is printed "Fuchs and T.-C. Yu".
- **Open questions.** Source 21's question 1, source 22's questions 1 and 2,
  and source 23's question 2 each point at another Part's regime. They are
  merged, with all their content, into Section 34; each list keeps a dated
  pointer, and source 22's question 2 is marked as answered by Part III for
  fixed d and d ≍ √n.
- **Cross-references added.** Source 21's "separate from a theorem at a fixed
  positive density k/n" now cites Theorem 12.1; source 22's fixed-k prior
  formula gains a note that Part I multiplies it by the crossover factor.
- **Bibliography.** One merged bibliography. Source 23 cited Agranat-Tamir et
  al. by its arXiv version only; the entry has the journal form with each
  source's inspected versions. Source 23's OEIS item, never cited in its text,
  is now cited (Section 23) and split into A399421, A397952 and A001190. The
  two Fuchs–Yu papers (Hao Yu, arXiv:2608.20860; T.-C. Yu, AofA 2026) keep
  separate entries.
- **Tables.** Source 21 reads its two tables from `results/checks-table.tex` and
  `results/p1-table.tex`; they are printed inline, from the shipped
  `data/21-crossover-results-*.tex`.
- **Numbering.** Sections, theorems and equations run through the report;
  source 23's equations, numbered through its paper, are now numbered within
  sections.

## Build

```sh
cp article.tex <scratch>/ && cd <scratch>
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX (MiKTeX here) with standard packages; the article needs no other file.
The committed `article.pdf` (62 pages) was built this way: no errors, no
undefined references or citations, no multiply defined labels, no duplicate
PDF destinations, no overfull boxes. Copy back only `article.pdf`.

## Rerunning the programs

Never run the delivered programs inside the repository: every script resolves
its paths relative to its own parent directory as delivered (`results/`,
`data/`, `checks/`), and several write there (source 21's scripts overwrite
`results/*` in place; source 23's `verify.py` writes `checks/` by default). Run
them on a copy laid out as delivered. From Git Bash, with `REPORT` the path of
this directory and `W` an empty scratch directory:

```sh
# Part I: galled-crossover-report/
mkdir -p "$W/gc/code" "$W/gc/data" "$W/gc/results"
for f in "$REPORT"/code/21-crossover-*.py; do cp "$f" "$W/gc/code/${f##*/21-crossover-}"; done
cp "$REPORT/code/21-crossover-reproduce.sh" "$W/gc/reproduce.sh"
cp "$REPORT/data/21-crossover-requirements.txt" "$W/gc/requirements.txt"
for f in "$REPORT"/data/21-crossover-results-*; do cp "$f" "$W/gc/results/${f##*/21-crossover-results-}"; done
for f in oeis-numeric-fixture.json reference-rows.json; do cp "$REPORT/data/21-crossover-$f" "$W/gc/data/$f"; done
# Part II: galled-density-reproducibility/
mkdir -p "$W/gd/code" "$W/gd/data" "$W/gd/results/expected/stability"
for f in "$REPORT"/code/22-density-*.py "$REPORT/code/22-density-replay.sh"; do cp "$f" "$W/gd/code/${f##*/22-density-}"; done
cp "$REPORT/code/22-density-reproduce.sh" "$W/gd/reproduce.sh"
cp "$REPORT/code/22-density-build_pdf.sh" "$W/gd/build_pdf.sh"
cp "$REPORT/22-density-README_REPLAY.md" "$W/gd/README_REPLAY.md"
cp "$REPORT/data/22-density-requirements.txt" "$W/gd/code/requirements.txt"
cp "$REPORT/data/22-density-oeis-reference.json" "$W/gd/data/oeis-reference.json"
for f in "$REPORT"/data/22-density-results-expected-*; do
  b=${f##*/22-density-results-expected-}
  case $b in stability-cutoff*) b=stability/${b#stability-};; esac
  cp "$f" "$W/gd/results/expected/$b"
done
for f in "$REPORT"/data/22-density-results-validated-*; do cp "$f" "$W/gd/results/${f##*/22-density-results-}"; done
# Part III: galled-endpoint-report/
mkdir -p "$W/ge/code" "$W/ge/data" "$W/ge/checks" "$W/ge/verification"
for f in "$REPORT"/code/23-endpoint-*.py "$REPORT/code/23-endpoint-run_checks.sh"; do cp "$f" "$W/ge/code/${f##*/23-endpoint-}"; done
cp "$REPORT/code/23-endpoint-code-README.md" "$W/ge/code/README.md"
cp "$REPORT/code/23-endpoint-reproduce.sh" "$W/ge/reproduce.sh"
cp "$REPORT/data/23-endpoint-requirements.txt" "$W/ge/requirements.txt"
cp "$REPORT/data/23-endpoint-requirements.txt" "$W/ge/code/requirements.txt"
for f in "$REPORT"/data/23-endpoint-*; do
  b=${f##*/23-endpoint-}
  case $b in
    checks-*) cp "$f" "$W/ge/checks/${b#checks-}";;
    verif-*) cp "$f" "$W/ge/verification/${b#verif-}";;
    requirements.txt) ;;
    *) cp "$f" "$W/ge/data/$b";;
  esac
done
```

This recreates every shipped file at its delivered path, byte for byte (80
files). Then rebuild the excluded triangle files (next section) and run, with
Python 3 plus mpmath 1.3.0 and SymPy 1.14.0:

```sh
cd "$W/gc" && for s in enumerate_rows check_algebra numerics finite_gaussian_generator \
    verify_p1_symbolic independent_constants exact_truncated_rows validate_p1; do python3 code/$s.py; done
cd "$W/gd" && sh code/replay.sh            # full replay; --quick for the smoke test
cd "$W/ge" && bash code/run_checks.sh --output-dir results
```

Tested on such a copy on 2 October 2026 (Windows, Python 3.14.4, mpmath 1.3.0,
SymPy 1.14.0), after the reconstruction below. Part III: all checks PASS
(18 s). Part II: the quick replay PASS (4 s) and the full replay PASS
(238 s, of which 168 s for the density checks; the intake run on a loaded
machine had stopped that stage after 170 s). Part I: all eight scripts run
without error (between 1 s and 97 s each, the longest `exact_truncated_rows.py`),
and every recorded output they rewrite (`algebra-checks.json`,
`crossover-checks.json`, `exact-checks.json`, `independent-constants.json`,
`stability.json`, `checks-table.tex`, `truncated-checks.json`,
`p1-diagnostics.json`, `p1-table.tex`) equals the shipped
`data/21-crossover-results-*` file apart from CRLF line endings.

Hazards:
- **Unshipped manifests.** `reproduce.sh` of source 22 starts with
  `verify_manifest.py`, which needs `MANIFEST.sha256`; source 23's
  `check_manifest.py` needs `SHA256SUMS`; source 21's README starts with
  `sha256sum -c MANIFEST.sha256`. The manifests were verified at placement
  (36/36, 30/30, 40/40 and 19/19) and retired; recover them with
  `git show 096ee7b87:docs/incoming/<archive>` if wanted.
- **Unshipped PDF builds.** `reproduce.sh` of sources 21 and 23 end with
  `bash build_pdf.sh`, which is not shipped (it builds the member manuscripts,
  which are printed in `article.tex` instead). Source 22's `build_pdf.sh` is
  shipped but builds `galled_density.tex`, the delivered manuscript, which is
  not in the repository any more (`article.tex` is the merged report).
  Source 21's `build_pdf.sh` stalled under MiKTeX in the intake run (its TeX
  Live fallback). Use the commands above instead of the `reproduce.sh`
  wrappers.
- **CRLF.** On Windows, Python's `write_text` writes CRLF, so regenerated text
  files differ from the delivered LF files by line endings only; compare with
  `diff --strip-trailing-cr` or parsed JSON. Source 22's `verify_results.py`
  compares values and is unaffected.
- **Interpreter.** The shell entry points call `python3` (source 22's honours
  `PYTHON`); where `python3` is a Windows Store alias, set up a real one first.

## Reconstructing the excluded data

Vladimir's direction for batch 77 was to exclude heavy regenerable artifacts.
The n ≤ 160 triangle shipped six times in the delivered archives (twice in
archive 20, twice in 21, once each in 22 and 23), and source 21 also shipped a
640-row table truncated at gall degree 12, twice. Only
`data/21-crossover-reference-rows.json` (353,510 bytes) is shipped. Five files,
3.49 MB together, are excluded; three programs read them
(`exact_truncated_rows.py` and `validate_p1.py` of source 21, `verify.py` of
source 23), and source 22's replay compares against the third. Rebuild them in
the copy laid out above (Git Bash; `py` may replace `python3`):

```sh
# Part I (gc = galled-crossover-report/)
cd "$W/gc"
python3 code/enumerate_rows.py        # results/exact-rows.json, 353,518 B
sed '/^reference=json.loads/d;/^assert out==reference/d' code/exact_truncated_rows.py > code/_regen_truncated.py
python3 code/_regen_truncated.py && rm code/_regen_truncated.py   # results/exact-truncated-rows.json, 1,186,712 B
python3 -c "d=open('results/exact-truncated-rows.json','rb').read().rstrip(b'\r\n'); open('data/reference-truncated-rows.json','wb').write(d)"   # 1,186,711 B
# Part II (gd = galled-density-reproducibility/)
cd "$W/gd"
python3 code/independent_rows.py --max-n 160 --output results/expected/independent-rows.json   # 360,750 B
# Part III (ge = galled-endpoint-report/)
cd "$W/ge"
python3 code/triangle.py --limit 160 --output data/triangle-160.json   # 401,372 B
```

The `sed` line removes the two lines of `exact_truncated_rows.py` that read and
assert against the excluded reference file; the copy is otherwise the delivered
program and writes the table it would have checked. Sizes are for LF line
endings (POSIX). On Windows the files are written with CRLF (353,519,
1,186,713, 360,751 and 408,344 bytes); the derived
`reference-truncated-rows.json` is byte-identical on both. The delivered
`independent-rows.json` lacks a final newline (360,749 bytes); the regenerated
file has one, and source 22's verifier compares values.

Verified on 2 October 2026 on copies of the delivered packages, with the
original files removed first: all five regenerated files equal the delivered
ones apart from line endings and that final newline (parsed-JSON equality for
the last), and `reference-truncated-rows.json` is byte-identical. Times on
this laptop: `triangle.py` 13 s, `enumerate_rows.py` 29 s,
`independent_rows.py` 27 s, the truncated enumeration 143 s (101 s in a
second run). Source 22
records 2.2 s for its row generator on its validation machine, and source 23's
code README expects its whole check to take a few seconds.

Byte-exact originals are in the arrival commit:

```sh
git show 096ee7b87:"docs/incoming/galled-crossover-reproducibility.zip" > gc.zip
unzip -o gc.zip 'galled-crossover-report/data/reference-truncated-rows.json' 'galled-crossover-report/results/exact-*.json'
git show 096ee7b87:"docs/incoming/galled-density-reproducibility.zip" > gd.zip
unzip -o gd.zip 'galled-density-reproducibility/results/expected/independent-rows.json'
git show 096ee7b87:"docs/incoming/galled-endpoint-report.zip" > ge.zip
unzip -o ge.zip 'galled-endpoint-report/data/triangle-160.json'
```

(`exact-*.json` also extracts the small shipped `exact-checks.json`.)

## Delivered texts that use delivery names or name unshipped files

- The three manuscripts' reproducibility passages (Section 10.4, Appendices A
  and B) and `22-density-README_REPLAY.md`, `code/23-endpoint-code-README.md`
  and `data/22-density-results-expected-README.md` use delivery paths
  (`code/replay.sh`, `results/expected/…`, `data/triangle-160.json`,
  `requirements.txt`, …) and name the PDFs and manifests, which are not
  shipped.
- `22-density-README_REPLAY.md` lists `results/validated-stability-summary.json`;
  it was not shipped because it is byte-identical to
  `data/22-density-results-expected-stability-summary.json`.
- `data/23-endpoint-provenance.json` hashes "prior computational materials"
  that were never in any archive (`ENDPOINT-PROOF.md`, `ALL-ORDERS.md`,
  `INVERSION.md`, `independent-audit/*`) and two files of source 22's
  workspace (`independent_rows.py` in an earlier version, and
  `independent-rows.json`, the excluded frozen triangle). Source 23 labels them
  "provenance only"; nothing at run time needs them.
- `data/23-endpoint-verif-clean-replay.json` records the hash and 18 pages of
  the unshipped `output/endpoint.pdf`.
- The `reproduce.sh` wrappers call unshipped `build_pdf.sh` scripts (sources
  21, 23) or build an unshipped manuscript (source 22); see the hazards above.

## Notes and discrepancies

- **Source 22's delivered README** (replaced by this guide) said "The paper
  credits neighboring gall-count CLTs and standard singularity, saddle-point
  and ProveIt machinery." The paper of Agranat-Tamir et al. does not credit
  ProveIt; the report does (Section 21.2). Correct reading: this report credits
  neighbouring gall-count CLTs and standard singularity, saddle-point and
  ProveIt machinery as prior work. That README also described the 20-page
  `galled_density.pdf`, the `MANIFEST.sha256`, and a full numerical replay of
  about 45 s on its validation machine.
- **Frozen JSON without final newlines.** Several of source 22's frozen files
  lack the final newline its scripts write; `verify_results.py` compares
  parsed values, so this is harmless.
- **Archive 20.** See the opening section; its 21 files are not shipped.
- **Two Fuchs–Yu papers.** Part I's "Fuchs–Yu" is M. Fuchs and Hao Yu
  (arXiv:2608.20860); Part II's is M. Fuchs and T.-C. Yu (AofA 2026). Source 21's
  README stresses that "Hao Yu is not T.-C. Yu".
- **Repository pin.** Source 22 inspected the repository at `4b874cea0`
  (185 selected text files); the two sources it credits are at the same paths
  today.
- **Not shipped** (all survive in `096ee7b87`): the three PDFs; the checksum
  manifests (`MANIFEST.sha256` of 21 and 22, `SHA256SUMS` and
  `checks/CODE-DATA-SHA256SUMS` of 23); the manuscripts, delivery READMEs and
  `build_pdf.sh` of sources 21 and 23; the five heavy triangle files above;
  byte-identical copies (21's four `results/*.txt` equal to their `.json`;
  22's `results/validated-stability-summary.json`; 23's
  `checks/recomputed-*`, `checks/inversion-checks.json` and
  `code/requirements.txt`); and all 21 files of archive 20.
