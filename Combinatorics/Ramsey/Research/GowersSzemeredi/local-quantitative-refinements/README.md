# Local Quantitative Refinements of Gowers's Proof of Szemerédi's Theorem

**Density transfer and phase-flat partitions; energies, restriction and dependent random choice; cube and progression counts; floor patterns and the Proposition 17.7 phase extraction**

This is a research report built on 6 October 2026 (write batch 115) from five
research manuscripts, all dated 6 October 2026 and prepared for Vladimir
Reshetnikov. Each sharpens local estimates of W. T. Gowers, *A new proof of
Szemerédi's theorem*, GAFA 11 (2001), 465–588. Each compares its statements
with the *corrected* statements of ProveIt's formal project beside this
directory: the edited transcription
[`Papers/sz-thm-gowers-proof`](../../../Papers/sz-thm-gowers-proof) and the Lean
development [`Lean/GowersSzemeredi`](../../../Lean/GowersSzemeredi), with the
ledger [`gowers-proof-status.json`](../../../gowers-proof-status.json). The report
is filed under `Combinatorics/Ramsey/Research/` by Vladimir's direction (6 October
2026), not in the research-report collection. That placement gives it **no formal
status**.

Every manuscript spans two to four themes, so the article is arranged in five
**thematic Parts**, with each source's sections printed whole inside them:

- **Part I — density transfer and phase-flat partitions** (sources 01, 02, 03, 05).
  - A sharp one-sided density–mass bound `P(X > t) ≥ ((a+t)T − at)/(a(b−t))`,
    proved independently in four sources.
  - A sharp one-cell phase envelope `C² ≤ (1−ρ²)F² + ρ²L²`.
  - Lemma 5.15 with cell size `α(2+α)N/(2(4−α)(M−1))`.
  - The optimal lower constant **1/3** in Lemma 2.3, and Corollary 2.4 with
    `36π` and `3α/4`.
  - Three density-sensitive Fourier increments.
  - Simultaneous phase-flat partitions with the optimal exponent `1/(m+1)`, a
    spectral-energy extraction, and a refinement theorem under the partition
    input `PP(K,R₀)`.
- **Part II — the inverse step** (02, 03, 04).
  - A mixed, weighted extension of Proposition 6.1 on every finite abelian
    group, with coefficient one.
  - Lemma 7.4 with `7δ³n/(3√6)`, and an elementary Proposition 7.3 with
    `(c/8, 2¹⁹c⁻⁹)`.
  - Exact moment interpolation; a polynomial restriction theorem over prime
    fields, with order eight `2⁻⁹⁵γ¹¹²η¹⁵|B|¹⁵`; arrangement moments with a
    cross-section profile.
- **Part III — cube and progression counts** (03, 04).
  - The exact fourth-order term of the centered cube count on every finite
    abelian group.
  - The sharp gap `‖f‖⁸_{U³} ≥ 2‖f‖⁸_{U²}` (real, centered, odd order), hence
    the sharp leading constant `6√2`, and the correction exponent `16/3`.
  - Density-weighted progression counting, and the lifting lemma, which is
    already formal.
- **Part IV — floor patterns** (01, 04).
  - `|F(r)| = (∏ 2rᵢ) C_k`, with `2^{k(k−1)/2} ≤ C_k ≤ R(H_k, k)`.
  - `log₂ C_k ~ k²`, using the classical threshold-function count.
  - Certified `C₁..C₄ = 1, 2, 10, 154` and `A₁..A₃ = 2, 6, 38`.
  - The local coefficient `2^{−k²−k log₂ k−O(k)}` at Proposition 17.7.
- **Part V — formal interface, ledger crosswalk, research questions.** The
  write's crosswalk to the ledger, the write's deduplicated list of the sources'
  46 questions, and each source's formalization plan, questions, conclusions and
  appendices.

| No. | Delivered title | Archive (bytes, files) | Manuscript | Pin | Placed | Printed in |
|---|---|---|---|---|---|---|
| 01 | *Sharp Local Refinements of Gowers's Szemerédi Argument: density transfer, carry-pattern entropy, and formalization interfaces* | `Gowers_Quantitative_Refinements (1).zip` (541,437 B, 15) | `gowers_refinements.tex`, 1,980 lines, 31 pp. | `3a25020a6` | `aefb0b44a` | F.6; I.1–I.7; IV.1–IV.5; V.3–V.7 |
| 02 | *Energy-Sensitive Inverse Steps and Sharp Density Extraction* | `Gowers_Szemeredi_Refinements.zip` (492,008 B, 7) | `gowers_refinements.tex`, 823 lines, 20 pp. | none (observed branch ref `66c02f8a1`) | `aefb0b44a` | F.7; I.8–I.12; II.1–II.4; V.8–V.11 |
| 03 | *Sharper local estimates in Gowers's proof of Szemerédi's theorem: density increments, exact cube expansions, and dependent random choice* | `gowers_local_refinements.zip` (408,961 B, 10) | `gowers_local_refinements.tex`, 2,392 lines, 36 pp. | `3a25020a6` | `aefb0b44a` | F.8; I.13–I.15; II.5–II.6; III.1–III.2; V.12–V.15 |
| 04 | *Sharper Local Bounds in Gowers's Proof of Szemerédi's Theorem: polynomial homomorphism restriction, sharp cube estimates, and floor-pattern complexity* (**base**) | `gowers_quantitative_refinements.zip` (788,239 B, 14) | `gowers_quantitative_refinements.tex`, 2,987 lines, 40 pp. | `327773149` | `aefb0b44a` | F.9; II.7–II.10; III.3–III.4; IV.6; V.16–V.20 |
| 05 | *Sharp Finite Phase Partitions and Density-Sensitive Increments* | `gowers_strengthening.zip` (399,349 B, 8) | `article.tex`, 847 lines, 18 pp. | `327773149` | `aefb0b44a` | F.10; I.16–I.20; V.21–V.24 |

The five archives arrived in `66f24b0d0` ("New research reports", 6 October
2026) and survive there (`git show 66f24b0d0:docs/incoming/<archive> > <archive>`).
The placement commit `aefb0b44a` ("Place batch 115 (1/2)") staged their files here
and retired the archives. Sources are numbered in arrival order and then in ASCII
order of archive name. The intake record is dossier `dossier115_GOWERS`.

**Status.** Unrefereed; nothing proved here has been checked by a proof
assistant. The one exception, a lifting lemma, was formalized before the sources
arrived (below). **Authorship disclosures:**
- Source 01 credits ChatGPT. Its author line reads "Research report prepared for
  Vladimir Reshetnikov / Mathematical development and computational checks with
  ChatGPT", and its PDF author field "Research report prepared with ChatGPT".
- Sources 02–04 say "prepared for Vladimir Reshetnikov". Source 05 is a "research
  note prepared for Vladimir Reshetnikov" with an empty PDF author field.
- No source names a human author.
- Source 03 mentions "independent mathematical reviews" that are not part of its
  delivery and are recorded nowhere in the repository.

Every result, proof, example, remark, question and limitation of the five
manuscripts is printed. No proof was replaced by a pointer.

**Five more sources are pending.** Sources 06–10 (arrival `62e21161f`) were
placed in this directory by `ad37962c4` ("Place batch 115 (2/2)"), as prefixed
code, data, figures and two root markdown files (listed below). The article does
not use them yet. A follow-up write will add them to Parts I–V as dated additions
without renumbering anything here.

## Why thematic Parts, and how they are filled

Sources 01 and 04 are independent manuscripts, not editions of each other: their
titles, pins and files differ, and they share 0.23 % of their text. No two of the
five share more than 0.8 % (intake, 8-word shingles). The overlaps are of
*results*, not text, and each theme draws on several sources. So each Part holds
the sections of every source on its theme, in source order. Each section heading
carries a source tag such as `[01]` and a line naming the delivered section. Each
manuscript's abstract and Section 1 are in the front matter (F.6–F.10), with its
title block quoted. Conventions sections open the source's first chapter that uses
them: 03 §2 is in Part I, and 02 §2 and 04 §2 are in Part II. Source 02's
Appendix B, a rational example for its tail theorem, sits in Part I beside that
theorem.

**Results proved by several sources** are printed in each source's own form,
because the forms and hypotheses differ and the proofs are independent. Examples:
general `[−a, b]` against `a = δ`; strict against non-strict events; all groups
against odd-order groups. A dated note at each later print names the first print,
credits every source, and says whether the proof is the same argument or a second
route:
- the one-sided mass bound (02 Thm I.9.1, 03 Thm I.14.1, 01 Thm I.4.1, 05 Lem I.17.3);
- the one-cell envelope (01 Lem I.1.2, 02 Thm I.8.1);
- the Lemma 5.15 replacement (02, 03);
- the simultaneous partition (01 Thm I.5.1, 05 Thm I.18.2);
- the scale barrier (01 for one phase, 05 for m phases);
- cancellation through degree three, and the quartic term
  (03 on every group, 04 on odd order, `P_d = R_d`);
- the `ℤ/3` cosine polynomial;
- generalized von Neumann and the telescoping theorem (03, 04);
- the floor-pattern counts `C_k = F_k` (01, 04).

## Files

The directory holds 87 files: 7 at the root, 33 in `code/`, 40 in `data/`, 7 in
`figures/`. Of these, 40 were placed with sources 01–05 (two of them, the base's
`article.tex` and `README.md`, are replaced by the write), 46 with sources 06–10
(placed, write pending), and `article.pdf` was added in this write.

**Report files**, written in the write:

```
README.md
article.pdf
article.tex
```

**Source 01, prefix `01-carry-transfer-`** (12 files). `code/`: the certificate
generator and exact verifier, the corrupted-certificate rejection test, the
symbolic and numerical checks, the delivered Makefile. `data/`: the exact carry
certificates (1, 3, 49 and 2,061 records for k = 1, …, 4), the verification and check outputs, the
build and supplementary summaries, the tested environment, and the requirements.

```
code/01-carry-transfer-Makefile
code/01-carry-transfer-carry_certificates.py
code/01-carry-transfer-check_certificate_rejection.py
code/01-carry-transfer-check_refinements.py
data/01-carry-transfer-build_summary.txt
data/01-carry-transfer-carry.json
data/01-carry-transfer-carry_verification.txt
data/01-carry-transfer-environment.json
data/01-carry-transfer-refinement_checks.json
data/01-carry-transfer-requirements.txt
data/01-carry-transfer-supplementary_check_summary.txt
data/01-carry-transfer-verifier_negative_tests.json
```

**Source 02, prefix `02-energy-freezing-`** (4 files). `code/`: the verification
script (seed 20261006) and the delivered build wrapper. `data/`: the recorded
results and the requirements file (`numpy`).

```
code/02-energy-freezing-build.sh
code/02-energy-freezing-verify.py
data/02-energy-freezing-requirements.txt
data/02-energy-freezing-verification_results.json
```

**Source 03, prefix `03-local-estimates-`** (7 files). At the root, the pinned
input-source notes. `code/`: the exact cube checks, the estimate checks and the
figure script. `data/`: the two recorded outputs. `figures/`: the comparison
figure of Section V.12.

```
03-local-estimates-SOURCE_NOTES.txt
code/03-local-estimates-make_figure.py
code/03-local-estimates-verify_cubes.py
code/03-local-estimates-verify_estimates.py
data/03-local-estimates-verification_cubes.txt
data/03-local-estimates-verification_estimates.txt
figures/03-local-estimates-local_bound_comparisons.pdf
```

**Source 04 (the base), prefix `04-restriction-cubes-`** (10 files). `code/`: the
energy, cube and coefficient checks; the selection checks; the floor-pattern
census (450 exact certificates); the figure script. `data/`: their recorded
outputs, and the source manifest, a provenance record with 19 blob ids. `figures/`:
the cube figure of Section V.16. Its manuscript was staged as `article.tex` and its
README.txt as `README.md`; both are now replaced.

```
code/04-restriction-cubes-make_figures.py
code/04-restriction-cubes-pattern_census.py
code/04-restriction-cubes-verify_refinements.py
code/04-restriction-cubes-verify_selection.py
data/04-restriction-cubes-pattern_census.json
data/04-restriction-cubes-selection_verification.json
data/04-restriction-cubes-source_manifest.json
data/04-restriction-cubes-verification_results.json
figures/04-restriction-cubes-cube_refinements.pdf
figures/04-restriction-cubes-cube_refinements.png
```

**Source 05, prefix `05-phase-partitions-`** (5 files). At the root, the source
audit. `code/`: the exact partition constructions and their checker, and the
verification runner. `data/`: the exact and the 80-digit Fourier results.

```
05-phase-partitions-SOURCE_AUDIT.md
code/05-phase-partitions-phase_partitions.py
code/05-phase-partitions-verify.py
data/05-phase-partitions-verification_exact.json
data/05-phase-partitions-verification_fourier.json
```

**Sources 06–10, placed by `ad37962c4`, write pending** (46 files; not used in the
article; to be described by the follow-up write):

```
07-transport-rigidity-FORMALIZATION.md
09-cubical-expansions-SOURCE_AUDIT.md
code/06-carry-discrepancy-bound_comparisons.py
code/06-carry-discrepancy-compute_carry_chambers.py
code/06-carry-discrepancy-density_checks.py
code/06-carry-discrepancy-uniformity_checks.py
code/06-carry-discrepancy-verify_carry_certificates.py
code/07-transport-rigidity-Makefile
code/07-transport-rigidity-checks.py
code/08-cube-fourth-order-build.sh
code/08-cube-fourth-order-verify_cube_refinements.py
code/09-cubical-expansions-build.sh
code/09-cubical-expansions-verify_expansion.py
code/09-cubical-expansions-verify_lattices.py
code/10-torsion-energy-make_figure.py
code/10-torsion-energy-run_all.py
code/10-torsion-energy-verify_density_phase.py
code/10-torsion-energy-verify_polynomial.py
code/10-torsion-energy-verify_structural.py
code/10-torsion-energy-verify_torsion.py
data/06-carry-discrepancy-README_VERIFICATION.txt
data/06-carry-discrepancy-bound_comparisons.json
data/06-carry-discrepancy-carry_certificates.json
data/06-carry-discrepancy-carry_results.json
data/06-carry-discrepancy-density_results.json
data/06-carry-discrepancy-package_validation.json
data/06-carry-discrepancy-provenance.json
data/06-carry-discrepancy-uniformity_results.json
data/06-carry-discrepancy-verification_log.txt
data/07-transport-rigidity-BUILD_STATUS.txt
data/07-transport-rigidity-source_manifest.json
data/07-transport-rigidity-verification.json
data/08-cube-fourth-order-layout_validation.json
data/08-cube-fourth-order-source_provenance.json
data/08-cube-fourth-order-verification_results.json
data/09-cubical-expansions-lattice_results.json
data/09-cubical-expansions-requirements-optional.txt
data/09-cubical-expansions-results.json
data/10-torsion-energy-formula_examples.json
data/10-torsion-energy-requirements.txt
data/10-torsion-energy-source_manifest.json
data/10-torsion-energy-verification_results.json
figures/06-carry-discrepancy-bound_comparisons.pdf
figures/06-carry-discrepancy-bound_comparisons.png
figures/10-torsion-energy-phase_frontier.pdf
figures/10-torsion-energy-phase_frontier.png
```

**Not shipped**, all retrievable from `66f24b0d0`:
- the five PDFs;
- the manuscripts of sources 01, 02, 03 and 05, which are printed in the article;
- the delivery READMEs of 01, 02, 03 and 05 (their limitations are carried below);
- source 04's `SHA256SUMS.txt`, verified 13/13 at intake (repository policy drops
  checksum manifests).

**Delivery names.** A shipped file is its delivered path, flattened, behind its
prefix:
- code (`.py`, `.sh`, `Makefile`) goes to `code/`;
- outputs, certificates, manifests and requirements go to `data/`;
- figures go to `figures/`;
- audit and provenance notes go to the root.

For example, source 01's `certificates/carry.json` is
`data/01-carry-transfer-carry.json` and its `results/environment.json` is
`data/01-carry-transfer-environment.json`. Source 05's `code/verify.py` is
`code/05-phase-partitions-verify.py`.

## Labels and numbering

Label prefix **`gsr:`** (none at HEAD before this report). A label has the form
`gsr:<part>:<source>:<delivered label>`, with Part codes `dt` (I), `en` (II), `cc`
(III), `fp` (IV), `fz` (V) and `fm` (front matter). For example, source 02's
`thm:tail` is `gsr:dt:02:thm:tail`. The delivered labels collide across sources
(`thm:tail` in 01 and 02, `sec:formal`, `sec:questions`, `sec:phase`, …); under
the prefixes they are distinct.

The write added:
- a label on every delivered section, `…:sec:d<k>` (67 labels);
- two labels on remarks of source 03 (`gsr:dt:03:rem:repo`, `gsr:cc:03:rem:rectify`);
- the five Part labels `gsr:<code>:part`;
- the front matter's `gsr:fm:sec:guide`, `…:status`, `…:notation`,
  `…:provenance`, `…:formal`;
- Part V's `gsr:fz:sec:crosswalk` and `gsr:fz:sec:further`, with 32 item labels
  `gsr:fz:q:<theme>:<name>`.

That makes 538 labels in all, all distinct. A comparison of the build's `.aux`
with separate builds of the five delivered `.tex` files found all 424 delivered
labels present.

**Numbering.** Sections restart in each Part and carry its numeral (I.9; F.1–F.10
in the front matter). Statements and equations are numbered within sections. A
delivered statement or equation `k.j` keeps its index `j`: the `.aux` comparison
found every delivered theorem-like and equation number unchanged in `j`. The
exceptions are sources 02 and 03, which numbered equations through the whole
manuscript, and the appendices, which now carry Part-V section numbers. Source
04's tags (M1)–(M7), (R1)–(R32), (A1)–(A14), (Q1), (Q2) and (∗) are kept.
**Bare numbers such as "Lemma 5.15" refer to Gowers's paper**, as in the sources;
this report's own numbers always carry a Part numeral or an F. The front matter's
Section F.1 holds the full concordance of delivered sections with sections here.

## Notation

No delivered symbol was renamed. Section F.3 lists every letter whose meaning
changes across sources, with the tempting false readings, and each Part opens with
a reading-conventions table. The main collisions:
- **ℰ/E**: 02's `ℰ(w)` (N⁻³-normalized energy on `G × Ĝ`), 04's `ℰ_j` (unnormalized
  transform), 03's `ℰ(f) = ‖f‖⁴_{U²}` and `ℰ₍₂₎`, 05's captured energy `E`.
- **R**: 03's `R_d` (parallelogram count) is 04's `P_d`; 04's `R_d` is a remainder;
  04's `R_d(H)` is 01's `R(H, d)`, with the arguments reversed.
- **B_k**: 01's and 04's translation budgets are different numbers.
- **Q, T, κ, ρ, s, L, M, m, q**: several meanings each.
- **α**: a norm power in Gowers's α-uniformity; a correlation elsewhere.
- **Arcs**: 01's `r` and 05's `ε` are widths in turns; 02's `ρ = sin θ`, which is
  01's `s`.

## What the report claims

Section F.2 of the article is the full status table. In short:

**Part I.**
- The sharp one-sided bound with extremizers (02, 03; case `a = δ`: 01, 05).
- 01's short-arc density tail with phase parameter `s`, occupied-mass exceptions,
  the optimal forced maximum and its trade-off. These are sharp in the finite
  weighted model, not claimed for arithmetic characters.
- The envelope `C² ≤ (1−ρ²)F² + ρ²L²` for real `f` (01, 02); 02's complex
  counterexample shows that real values are needed.
- The Lemma 5.15 replacement (02, 03). It needs `α > 0` and nonempty cells.
- Lemma 2.3 with `√(rs/(9M))`, and `1/3` optimal, also under the exact Lean
  hypotheses (05).
- Corollary 2.4 with `36π`, `3α/4` and the same upper length (05).
- Fourier increments:
  - 01: `δ + 3δbκ/(4−(4−3δ)κ) ≥ δ + 3η/8` at length
    `⌊√((N/2π) arcsin(η/4δb))⌋`, for a real frequency, bounded weights and any `N`;
  - 05: `δ + δα/(4δ−α)` at length `≥ √(αN/(16πδ(1−δ)))`, with an exact integer
    length and a popularity bound;
  - 03: an adjustable version.
- Simultaneous partitions (01, 05), the optimal exponent `1/(m+1)` (05), and the
  one-phase barrier `ℓ ≤ 1+√(3r(N−1))` (01).
- Spectral extraction with a Gram correction and width allocation (05).
- The phase-to-density transfer and refinement theorem, *conditional on*
  `PP(K,R₀)` (02).

**Part II.**
- 02's `𝒯_w(f,g)⁴ ≤ min{m(f)⁴𝒰(g), m(g)⁴𝒰(f)}ℰ(w)` on every finite abelian
  group, with coefficient 1 optimal, plus its deficits, alignment and rigidity.
- 03's cubic DRC certificate and its optimal scalar tangent `κ* = 0.95378…`.
- 03's elementary BSG bound, far weaker than Reiher–Schoen.
- 04's exact interpolation (M1)–(M7).
- 04's restriction theorem with `κ_d = 1/(2(400d)^d)`, `Λ_d = 2(1+C(2d,2))(400d)^d`,
  over prime fields only.
- 04's arrangement interpolation.

**Part III.**
- 03's exact quartic term `δ^{m−4}(R_d ℰ(f) + T_d ℰ₍₂₎(f))`. `K_d` is optimal over
  all groups, the power 4 is optimal for sets, and the fifth-order remainder is
  necessary.
- 04's norm gap with equality and stability; the three-cube bound with leading
  `6√2 δ⁴u⁴`; the `u^{16/3}` correction with optimal exponent for
  `gcd(|G|, 6) = 1`; sharpness for sets.
- Generalized von Neumann and the telescoping error `(k−2)α` in place of `2^k α`
  (03, 04).
- The lifting lemma (04 Lemma III.4.5; 03's remark).

**Part IV.**
- `|F(r)| = (∏ 2rᵢ) C_k` (01); integer intervals and the modular count (04).
- `C_k ≤ R(H_k, k)` (01, 04).
- `C_k ≥ 2^{⌊k²/4⌋}` (01) and `C_k ≥ 2^{k(k−1)/2}` (04).
- `log₂ C_k ~ k²` and `log₂ A_k ~ k²`, using the classical threshold-function
  count of Zuev and Kahn–Komlós–Szemerédi as recorded by Baldi–Vershynin; this is
  an external input, not reproved.
- The polynomial floor entropy (lower half external: Baldi–Vershynin).
- The certified counts.
- 04's local phase-extraction coefficient.

**Proved in the write** (dated notes, each with its proof; listed in the article's
Section F.1):
1. **01's increment is at least 3/2 times 05's** (and 03's at `λ = 1/2`) at the
   stated parameters. With `κ = η/(2δb)`, the ratio is
   `3/2 + (3/2)(2−δ)κ/(4−(4−3δ)κ)`. The lengths are of the same order.
   Caveat, also proved there: 03's `λ → 0` and 05's `ε → 0` buy larger increments
   at much shorter lengths.
2. **The four forms of the one-sided bound coincide** (`T = D/2`, `a = δ`,
   `b = 1−δ`).
3. **`c₃^odd = 2^{−1/2}`**, attained exactly by real parts of characters. It
   follows from 04's norm gap and answers 03's Research question for `d = 3`; the
   best odd-order leading constant is `R₃ c₃^odd = 6√2`.
4. **04's lower bound `2^{k(k−1)/2}` beats 01's `2^{⌊k²/4⌋}` for every `k ≥ 3`**,
   and equals it at `k = 1, 2`: `k(k−1)/2 − k²/4 = k(k−2)/4`. The intake dossier
   said "for every k ≥ 2", which is wrong at `k = 2`.

## What the report does not claim

No source claims a new bound for `r_k(N)`. All cite Leng–Sah–Sawhney's
`r_k(N) ≪ N exp(−(log log N)^{c_k})`, `k ≥ 5`, as the benchmark. No source
claims literature priority or an exhaustive priority search, Lean compilation, or
kernel verification. Further limitations, kept in place and collected in Section
V.2:
- sharpness in the weighted model, not for arithmetic characters (01);
- `36π` and `3/4` not claimed optimal, and sharpness only for linear phases,
  uniform arcs and symmetric widths (05);
- the coefficient 6 of the `u^{16/3}` term not claimed optimal, nor the
  higher-dimensional `P_d/√2` (04);
- the restriction theorem is prime-only and does not prove the Lean
  Lemma 9.3/Corollary 9.4 (04);
- `PP(K,R₀)` is imported (02);
- `R_d` is not claimed optimal on odd-order groups (03; for `d = 3` it is not);
- finite and numerical checks prove nothing general (all).

From the delivery READMEs:
- 05's spectral diagnostics test only the cyclic-character specialization, not the
  Gram corollary, and its exact constructions are not fast algorithms for very
  large `N`.
- 01's finite certificates are proof evidence for the finite counts only, and its
  verifier is ordinary Python.

## Further questions, and the standing rule

Section V.2 applies Vladimir's standing rule of 4 October 2026. It groups the
sources' 46 questions (01: 10, 02: 7, 03: 9, 04: 12, 05: 8) into 32 items under
five themes, with credits:
- **I**, density transfer: 10 items, 14 questions;
- **II**, the inverse step: 8 items, 9 questions;
- **III**, cubes and progressions: 7 items, 8 questions;
- **IV**, floor patterns: 5 items, 7 questions;
- **V**, integration and formalization: 2 items, 8 questions.

Items are numbered within themes, so the follow-up write for sources 06–10 can
extend them.

- **Answered inside the report** (dated notes at the questions):
  - 04's Question 8, the leading constant of `log₂ F_k/k²` and `log₂ A_k/k²`, is
    answered by 01: it is 1, using the classical threshold count, and 01 certifies
    `F₄ = C₄ = 154`.
  - 03's question on `c_d^odd` is settled for `d = 3` by 04, as above; with it,
    03's Remark III.2.9 is settled at `d = 3`. 04's Question 3 is the same
    question for `d ≥ 4` and is merged with it.
- **Not certified**, recorded as item IV.2: the intake's recount gives
  `C₅ = 8410` and `A₄ = 770`. It used floating-point LPs with every feasibility
  witness re-evaluated exactly, but the infeasibility side rests on solver
  status. Both values lie within the proved bounds
  `1024 ≤ C₅ ≤ 2,138,410` and `270 ≤ A₄ ≤ 242,825`.
- **Refuted:** nothing. No claim of the five manuscripts was found false, and
  none asserts an unproved theorem as proved.
- **Moved to further questions:** no unproved claim needed moving. The external
  inputs, the threshold counts and `PP(K,R₀)`, are listed with their status.

## What was checked, and what was not

**At intake** (dossier of batch 115, 6 October 2026), all five manuscripts were
read. Every headline was re-derived, and the computable ones were checked. The
checks included:
- the nine-point parity obstruction;
- the `36π` arithmetic;
- 02's identities on non-cyclic groups;
- the Lemma 5.15 replacement;
- the DRC constants;
- 04's norm gap, by adversarial minimization on `ℤ/5, ℤ/7, ℤ/9, ℤ/15, ℤ/3×ℤ/3, ℤ/25`;
- 04's cube bounds, re-evaluated at 60 digits after a float search flagged
  rounding noise;
- the two-frequency identity on `ℤ/17`;
- `R_d = P_d`;
- the carry counts.

All delivered suites were rerun on copies; they reproduced the recorded outputs,
except last-ulp floating-point diagnostics.

**At the write:**
- every comparison with the formal project was checked against the ledger and
  the Lean declarations at HEAD (Section V.1, with files and lines);
- the four statements above were proved;
- the Table rows quoted in notes were recomputed;
- the short suites were rerun on copies, on Windows with Python 3.14.4. The
  routes are below; all outputs were byte-identical to the shipped ones after
  removing carriage returns.

**Not verified:** the external threshold-count theorems and the published
literature the sources compare with; the long proofs beyond the intake's
re-derivations.

## Relation to the formal project

The ledger (`gowers-proof-status.json`) moved during this write; the Lean
development is being extended concurrently. At the pins it recorded 88 exact
companions and 32 open statements. At HEAD `25df8755d` (6 October 2026) it records
98 and 22. The ten statements closed since the pins are Corollaries 5.6, 5.7 and
5.11 and Lemmas 5.9, 5.10, 5.14, 16.1, 16.3, 16.5 and 16.6. Each source's
comparison with a corrected statement is accurate at HEAD except two stale claims,
which the article corrects in dated notes:
- source 02 calls its partition input `PP(K,R₀)`, i.e. Corollary 5.6, "not … Lean-verified". It is now
  `corollary_5_6_holds` (`Proofs05FullPartition.lean`), with identical constants.
  The affine pullback of polynomials is formal (`polynomialOn_affine_pullback`),
  but 02's refinement theorem itself is not.
- source 03 (and implicitly 01) quotes the ledger as 88/32.

**Formalized:** exactly one statement of the five sources, 04's Lemma III.4.5
(lifting a modular progression from a short interval) with 03's rectification
remark. They are `hasNatAP_of_short_modular_sequence` and
`hasNatAP_of_hasModAP_image` (`Proofs18IntervalTransfer.lean`, lines 22, 92),
added in `327773149`, which is 04's own pin, before arrival. Some baselines that
the sources improve are already proof-level facts of the development:
- Corollary 2.5's stronger pair, in `cor25_large_scale`;
- Lemma 9.2's exact Parseval, inside `lemma_9_2_holds`.

**Nothing else here is formalized, and the report gains no formal status.**
Pointers for `FORMALIZATION_STATUS.txt` are left to the session that maintains
the Lean development.

## Relation to other reports

No other ProveIt report treats Gowers's proof, Gowers norms or Szemerédi's
theorem (searched 6 October 2026). The neighbours are the formal project itself
and the source paper in `Papers/sz-thm-gowers-proof`.

## Delivery names, renames and discrepancies

- **Byte-identical.** Every delivered file other than the base's manuscript and
  README keeps its bytes; only names changed. `article.tex` and this README
  replace the base's two files.
- **Renamed modules break imports and paths, so nothing runs in this directory.**
  - 01's `check_certificate_rejection.py` imports `carry_certificates`, reads
    `ROOT/certificates/carry.json` and writes `ROOT/results/verifier_negative_tests.json`.
  - 01's `check_refinements.py` writes `../results/refinement_checks.json`.
  - 01's Makefile and 02's `build.sh` name the delivered files.
  - 02's `verify.py` overwrites `verification_results.json` beside itself.
  - 05's `verify.py` does `from phase_partitions import …`.
  - 03's `make_figure.py` and 04's `make_figures.py` write into `./figures/`
    beside themselves.

  Rerun on copies (below).
- **Source defects**, disclosed and not fixed in the delivered files:
  - 04's `.tex` wrote `_{epsilon\in\Omega_k}` twice, without the backslash; it is
    corrected in the article, with a dated note.
  - 05's `SOURCE_AUDIT.md` says its pinned read of `Proofs02Partition.lean`
    "included lines 580–780". That file has 702 lines; its blob `291b149` and the
    construction described are correct.
  - 02 and 05 link some repository files through the moving branch `main`; their
    blob ids are correct.
  - 02 records no pin in its README; its Appendix A gives the observed branch
    ref `66c02f8a1`.
  - 01's bibliography gives the public Gowers PDF under `users/gasarch`, the
    others under `~gasarch`.
- **Delivery names inside shipped text.**
  - 04's `source_manifest.json` and 03's `SOURCE_NOTES.txt` name delivered files.
  - 04's manuscript comment ("See README.txt") is quoted in F.9.
  - 01's `environment.json` records a generic Linux sandbox and no user paths.
- **Edits of delivered text in the article**, listed in F.1:
  - prefixed labels and unified citation keys;
  - source tags on headings;
  - 02's plain "Section 3" made a live reference;
  - two figure paths;
  - two bookmark strings;
  - the missing backslash restored.

## Rerunning the checks

Run on copies with the delivered layout, never in this directory. From the
repository root, with `R` this directory and `T` a scratch directory:

```sh
R=Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements
T=/path/to/scratch; PY=python3
same() { tr -d '\r' < "$1" | cmp - "$2"; }      # Windows writes CRLF
mkdir -p "$T/r01/code" "$T/r01/certificates" "$T/r01/results"
for f in carry_certificates check_certificate_rejection check_refinements; do
  cp "$R/code/01-carry-transfer-$f.py" "$T/r01/code/$f.py"; done
cp "$R/data/01-carry-transfer-carry.json" "$T/r01/certificates/carry.json"
(cd "$T/r01" && $PY code/carry_certificates.py verify certificates/carry.json &&
  $PY code/check_certificate_rejection.py &&
  same results/verifier_negative_tests.json "$OLDPWD/$R/data/01-carry-transfer-verifier_negative_tests.json")
mkdir -p "$T/r02" && cp "$R/code/02-energy-freezing-verify.py" "$T/r02/verify.py"
(cd "$T/r02" && $PY verify.py >/dev/null &&
  same verification_results.json "$OLDPWD/$R/data/02-energy-freezing-verification_results.json")
mkdir -p "$T/r03" && for f in verify_cubes verify_estimates; do
  cp "$R/code/03-local-estimates-$f.py" "$T/r03/$f.py"; done
(cd "$T/r03" && $PY verify_cubes.py > cubes.txt &&
  same cubes.txt "$OLDPWD/$R/data/03-local-estimates-verification_cubes.txt")
mkdir -p "$T/r04" && for f in pattern_census verify_selection verify_refinements; do
  cp "$R/code/04-restriction-cubes-$f.py" "$T/r04/$f.py"; done
cp "$R/data/04-restriction-cubes-pattern_census.json" "$T/r04/pattern_census.json"
(cd "$T/r04" && $PY -S pattern_census.py --verify pattern_census.json &&
  $PY -S verify_selection.py --report sel.json &&
  same sel.json "$OLDPWD/$R/data/04-restriction-cubes-selection_verification.json")
mkdir -p "$T/r05/code" && for f in phase_partitions verify; do
  cp "$R/code/05-phase-partitions-$f.py" "$T/r05/code/$f.py"; done
(cd "$T/r05/code" && $PY verify.py --part exact --output ../verification_exact.json &&
  same ../verification_exact.json "$OLDPWD/$R/data/05-phase-partitions-verification_exact.json")
```

Requirements and run times:
- 02 needs NumPy; 05's `verify.py` needs mpmath (even for `--part exact`).
- Do not run Python with `-O`: the 02 and 05 checkers rely on assertions (their
  delivery READMEs say so).
- Everything else uses the standard library.
- Each command runs in under a minute (05 exact: about 40 s).

At the write this block, run verbatim from the repository root (Git Bash on
Windows, `PY=py`), completed all five comparisons. The
longer checks also run on these copies:
- 01: `check_refinements.py` (NumPy, SymPy);
- 03: `verify_estimates.py`, compared with `verification_estimates.txt`;
- 04: `-S verify_refinements.py --output out.json` (two float diagnostics differ
  in the last digit);
- 05: `verify.py --part fourier` (mpmath, 80 digits).

The intake ran all of these. Regenerating certificates needs SciPy; regenerating
figures needs Matplotlib.

## Building the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Use pdfLaTeX (MiKTeX or TeX Live), in a scratch copy that contains `figures/`.
The build gives 167 pages, with no warnings, no undefined references, no duplicate
destinations and no overfull boxes. Packages: amsmath, amssymb, amsthm,
mathtools, lmodern, geometry, microtype, graphicx, booktabs, longtable, tabularx,
array, enumitem, needspace, placeins, xcolor, hyperref, xurl, bookmark. Only
`article.pdf` is committed.

## Licences

Repository text is MIT-0. The sources quote short passages of the cited
literature with attribution. No third-party paper, repository copy or font is
redistributed.
