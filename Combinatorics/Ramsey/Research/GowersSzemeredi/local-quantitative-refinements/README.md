# Local Quantitative Refinements of Gowers's Proof of Szemerédi's Theorem

**Density transfer and phase-flat partitions; energies, restriction and dependent random choice; cube and progression counts; floor patterns and the Proposition 17.7 phase extraction**

This is a research report built on 6 October 2026 from fourteen research
manuscripts, all dated 6 October 2026. Sources 01–05 were merged in the first write
(batch 115, `18507e2b2`); sources 06–10 were added in a second write the same day
(`9f83dbe0f`), and sources 11–14 (batch 116) in a third, each time as dated additions
that renumber and relabel nothing printed before. Each source
sharpens local estimates of W. T. Gowers, *A new proof of Szemerédi's theorem*,
GAFA 11 (2001), 465–588, and compares its statements with the *corrected*
statements of ProveIt's formal project beside this directory: the edited
transcription [`Papers/sz-thm-gowers-proof`](../../../Papers/sz-thm-gowers-proof)
and the Lean development [`Lean/GowersSzemeredi`](../../../Lean/GowersSzemeredi),
with the ledger [`gowers-proof-status.json`](../../../gowers-proof-status.json).
The report is filed under `Combinatorics/Ramsey/Research/` by Vladimir's direction
(6 October 2026), not in the research-report collection. That placement gives it
**no formal status**.

Every manuscript spans several themes, so the article is arranged in five
**thematic Parts**, with each source's sections printed whole inside them:

- **Part I — density transfer and phase-flat partitions** (sources 01, 02, 03, 05; 06, 10; 13).
  - A sharp one-sided density–mass bound `P(X > t) ≥ ((a+t)T − at)/(a(b−t))`,
    proved independently in six sources (01, 02, 03, 05, 06, 10).
  - A sharp one-cell phase envelope `C² ≤ (1−ρ²)F² + ρ²L²`.
  - Lemma 5.15 with cell size `α(2+α)N/(2(4−α)(M−1))` (02, 03), and 06's exact
    optimum for a fixed number `M` of cells, `min{P₊/(b(M−1)), S/(M−2)}`, with
    extremizers; it is strictly better for `α < 1` and equal at `α = 1`.
  - The optimal lower constant **1/3** in Lemma 2.3, and Corollary 2.4 with
    `36π` and `3α/4`.
  - Four density-sensitive Fourier increments (01, 03, 05, 10), with 10's
    optimal cap `δ + δS/(2δ−S)` and its density–length frontier.
  - Simultaneous phase-flat partitions with the optimal exponent `1/(m+1)`, a
    spectral-energy extraction, and a refinement theorem under the partition
    input `PP(K,R₀)`.
  - 13: complete simultaneous partitions with prescribed lengths `v−1` or `v` and
    exponent `1/(3q+2)` for `q` linear phases (no size threshold), a random-slope
    obstruction with independent tolerances, and a joint phase–density–exception
    frontier. The sharp one-sided bound is now proved in seven sources; 13's
    Fourier increment is dominated by 01's at the same length (proved at the write).
- **Part II — the inverse step** (02, 03, 04; 07, 10; 11, 12, 14).
  - A mixed, weighted extension of Proposition 6.1 on every finite abelian
    group, with coefficient one.
  - Lemma 7.4 with `7δ³n/(3√6)`, and two elementary Propositions 7.3,
    `(c/8, 2¹⁹c⁻⁹)` (03) and `(c/4, 2¹⁰c⁻⁵)` (10).
  - Exact moment interpolation; a polynomial restriction theorem over prime
    fields, with order eight `2⁻⁹⁵γ¹¹²η¹⁵|B|¹⁵`; arrangement moments with a
    cross-section profile.
  - **Source 07's chapter (Lemma 10.9):** transport-sensitive rigidity, the sharp
    threshold `δ < 1/(2k)`, Freiman order **five** under exactly the hypotheses of
    the Lean `lemma_10_9`, and order **nine** under further hypotheses of the
    Section 10 construction, which `lemma_10_9` does not have.
  - 10's vertical-fibre Freiman extraction: Corollary 7.6 with `2⁻²⁰⁹γ¹⁰³` in
    place of `2⁻¹⁸⁸²γ¹¹⁶⁴`.
  - **Source 11's chapter (Section 6 endpoint):** sharp cubic profiles
    `ε(f) ≥ 4t − (10+2κ)t² + (6+2κ)t³` with coset extremizers, affine correction
    for `ε < 1/9`, and the exact largest non-affine graph energy for `|G| ≥ 34`.
    **Remark W2** (write): that cutoff cannot simply be dropped —
    `ℤ/12 → ℤ/2` has non-affine energy 1296 against the formula's 1288.
  - **Source 12's chapter (Section 10, Lemmas 10.10–10.14):** sharp Freiman
    extension `3ε + 2κ < 1` with counterexamples on the boundary, the sharp
    majority lemma, finite Bohr-radius selection, fourth-moment smoothing, and
    Theorem 10.13 on a Bohr set of radius `α¹⁹/(3π2¹⁴⁹)`.
  - 14: near-maximal energy `E(A) ≥ (1−ε)m³`, `ε ≤ 1/100`, forces a unique coset
    within `τ(ε)m`, `τ(ε) = (1−√(1−4ε))/2`, sharp; product cosets for cube
    collisions; equality in arrangement moment interpolation. **Remark W3**
    (write) composes this with 11's near-extremizer bounds and answers 11's
    Question 3 in substance.
- **Part III — cube and progression counts** (03, 04; 06, 08, 09, 10; 13, 14).
  - The exact fourth-order term of the centered cube count on every finite
    abelian group (03, 08, 09), and the exact fifth-order term with Stirling
    multiplicities and order-two and order-three torsion statistics (09).
  - The sharp gap `‖f‖⁸_{U³} ≥ 2‖f‖⁸_{U²}` (real, centered, odd order), hence
    the sharp leading constant `6√2`, and the correction exponent `16/3` (04).
  - **The quartic lower bound with coefficient 12 is false** (03, 08, 09):
    Remark W1 records the counterexample on `ℤ/11ℤ`, ratio `15337/1296 < 12`.
  - A determinant-5 configuration: order-five torsion first enters at order six (09).
  - Progression counting: the linear telescope (03, 04, 06, 10), a bound
    quadratic in the uniformity norm (06), torsion-sensitive mixed-`L^p` bounds
    (10), and the lifting lemma, which is already formal.
  - An exact dimension threshold for polynomial colourings without
    symmetrically coloured even progressions (10), and the exact minimum count
    above it, `q^d(q^{max(d−B,0)} − 1)` over `𝔽_q` (14).
  - **The secondary coefficient `(9/4)^{1/3}` of the three-cube extremal problem
    (14), which settles 04's Question 1** (Remark W4, write); exponent 6 on groups
    of exponent five (14); centered three-cube orbit moments and a spectral
    deficit, and interval discrepancy with the sharp exponent `1/4` for Lemma 3.5
    (13).
- **Part IV — floor patterns** (01, 04; 06).
  - `|F(r)| = (∏ 2rᵢ) C_k`, with `2^{k(k−1)/2} ≤ C_k ≤ R(H_k, k)`; general
    coefficient families and modular counts (06).
  - `log₂ C_k ~ k²`, using the classical threshold-function count (01, 06; 06
    also uniformly modulo every `M ≥ 2`).
  - Certified `C₁..C₄ = 1, 2, 10, 154` (twice: 01 and 06) and
    `A₁..A₃ = 2, 6, 38` (04; 06's `D_k`).
  - Local coefficients at Proposition 17.7: `2^{−k²−k log₂ k−O(k)}` (04) and
    `2^{−2k²−O(k log k)}` (06).
- **Part V — formal interface, ledger crosswalk, research questions.** The
  writes' crosswalk to the ledger, the deduplicated list of the sources'
  141 questions, iteration bookkeeping (03, 06, 10), and each source's
  formalization plan, questions, conclusions and appendices.

| No. | Delivered title | Archive (bytes, files) | Manuscript | Pin | Placed | Printed in |
|---|---|---|---|---|---|---|
| 01 | *Sharp Local Refinements of Gowers's Szemerédi Argument: density transfer, carry-pattern entropy, and formalization interfaces* | `Gowers_Quantitative_Refinements (1).zip` (541,437 B, 15) | `gowers_refinements.tex`, 1,980 lines, 31 pp. | `3a25020a6` | `aefb0b44a` | F.6; I.1–I.7; IV.1–IV.5; V.3–V.7 |
| 02 | *Energy-Sensitive Inverse Steps and Sharp Density Extraction* | `Gowers_Szemeredi_Refinements.zip` (492,008 B, 7) | `gowers_refinements.tex`, 823 lines, 20 pp. | none (observed branch ref `66c02f8a1`) | `aefb0b44a` | F.7; I.8–I.12; II.1–II.4; V.8–V.11 |
| 03 | *Sharper local estimates in Gowers's proof of Szemerédi's theorem: density increments, exact cube expansions, and dependent random choice* | `gowers_local_refinements.zip` (408,961 B, 10) | `gowers_local_refinements.tex`, 2,392 lines, 36 pp. | `3a25020a6` | `aefb0b44a` | F.8; I.13–I.15; II.5–II.6; III.1–III.2; V.12–V.15 |
| 04 | *Sharper Local Bounds in Gowers's Proof of Szemerédi's Theorem: polynomial homomorphism restriction, sharp cube estimates, and floor-pattern complexity* (**base**) | `gowers_quantitative_refinements.zip` (788,239 B, 14) | `gowers_quantitative_refinements.tex`, 2,987 lines, 40 pp. | `327773149` | `aefb0b44a` | F.9; II.7–II.10; III.3–III.4; IV.6; V.16–V.20 |
| 05 | *Sharp Finite Phase Partitions and Density-Sensitive Increments* | `gowers_strengthening.zip` (399,349 B, 8) | `article.tex`, 847 lines, 18 pp. | `327773149` | `aefb0b44a` | F.10; I.16–I.20; V.21–V.24 |
| 06 | *Sharp Local Bounds in Gowers' Proof of Szemerédi's Theorem: carry patterns, quadratic counting errors, and optimal density extraction* | `Gowers_Refinements (1).zip` (647,760 B, 19) | `Gowers_Refinements.tex`, 1,958 lines, 27 pp. | `7d99e5dee` | `ad37962c4` | F.11; I.21; III.5; IV.7–IV.9; V.25–V.27 |
| 07 | *Transport-sensitive rigidity in Gowers's approximate-homomorphism argument* | `Gowers_Transport_Rigidity.zip` (359,160 B, 9) | `transport_rigidity.tex`, 1,472 lines, 21 pp. | `ae0e89574` | `ad37962c4` | F.12; II.11 (guide), II.12–II.19; V.28–V.31 |
| 08 | *Fourth-order stability of additive cube counts* | `gowers_cube_refinements.zip` (541,854 B, 8) | `fourth_order_cube_counts.tex`, 1,677 lines, 25 pp. | none (blob ids of `7d99e5dee`) | `ad37962c4` | F.13; III.6–III.15; V.32–V.36 |
| 09 | *Arithmetic Circuit Expansions for Cubical Counts* | `gowers_cubical_expansions.zip` (512,022 B, 10) | `article.tex`, 1,794 lines, 27 pp. | `7d99e5dee` | `ad37962c4` | F.14; III.16–III.27; V.37–V.41 |
| 10 | *Quantitative Refinements Around Gowers' Proof of Szemerédi's Theorem: torsion, density profiles, additive energy, and sharp limits for polynomial colorings* | `gowers_refinements.zip` (664,416 B, 15) | `gowers_refinements.tex`, 2,443 lines, 34 pp. | `7d99e5dee` | `ad37962c4` | F.15; I.22–I.24; II.20–II.21; III.28–III.30; V.42–V.45 |
| 11 | *Sharp Affine Rigidity from Graph Additive Energy: cubic stability, target torsion, and exact non-affine extremizers* | `Gowers_Affine_Rigidity_Research.zip` (406,963 B, 10) | `article.tex`, 1,259 lines, 19 pp. | `40f885098` | `6f530c29c` | F.16; II.22 (guide), II.23–II.32; V.46–V.49 |
| 12 | *Sharp Freiman Extension and Polynomial Bohr Radii* | `gowers_bohr_extension.zip` (550,113 B, 12) | `gowers_bohr_extension.tex`, 1,215 lines, 25 pp. | `9ea383e9b` | `6f530c29c` | F.17; II.33 (guide), II.34–II.42; V.50–V.52 |
| 13 | *Sharp Local Refinements in Gowers' Szemerédi Framework: simultaneous recurrence, extremal density selection, and centered cube counts* | `gowers_local_refinements.zip` (831,549 B, 17; **reuses the name of 03's archive**) | `gowers_local_refinements.tex`, 1,223 lines, 31 pp. | `9ea383e9b` | `6f530c29c` | F.18; I.25–I.29; III.31–III.33; V.53–V.55 |
| 14 | *Sharp Extremal Refinements in Gowers's Szemerédi Framework: secondary cube asymptotics, arrangement stability, and polynomial supersaturation* | `gowers_extremal_refinements.zip` (518,912 B, 14) | `gowers_extremal_refinements.tex`, 2,767 lines, 37 pp. | `9ea383e9b` | `6f530c29c` | F.19; II.43–II.44; III.34–III.38; V.56–V.58 |

The first five archives arrived in `66f24b0d0` ("New research reports", 6 October
2026) and survive there (`git show 66f24b0d0:docs/incoming/<archive> > <archive>`);
the placement commit `aefb0b44a` ("Place batch 115 (1/2)") staged their files here
and retired the archives. Sources 06–10 arrived in `62e21161f` and survive there
in the same way; `ad37962c4` ("Place batch 115 (2/2)") staged them. Sources are
numbered in arrival order and then in ASCII order of archive name. Archive 06
(`Gowers_Refinements (1).zip`) and archive 10 (`gowers_refinements.zip`) are
independent manuscripts, not editions (1.09 % shared text); no two of the ten
share more than 1.14 % (intake, 8-word shingles). The intake record is dossier
`dossier115_GOWERS`. Sources 11–13 arrived in `08ab4187e` and source 14 in
`d179062cc` (both 6 October 2026); `6f530c29c` ("Place batch 116") staged them and
retired the archives (`git show 08ab4187e:docs/incoming/<archive>`, likewise
`d179062cc`); intake record `dossier116_GOWERS`. **Archive 13 reuses the name of
archive 03:** `docs/incoming/gowers_local_refinements.zip` was added in `66f24b0d0`
(source 03, 408,961 B), removed in `aefb0b44a` and added again with different
content in `08ab4187e` (source 13, 831,549 B); retrieve each from its own arrival
commit. 13 is an independent manuscript, not an edition of 03 (0.97 % shared
text); every overlap involving 11–14 is below 1 %.

**Status.** Unrefereed; nothing proved here has been checked by a proof
assistant. The one exception, a lifting lemma, was formalized before the sources
arrived (below). **Authorship disclosures:**
- Source 01 credits ChatGPT. Its author line reads "Research report prepared for
  Vladimir Reshetnikov / Mathematical development and computational checks with
  ChatGPT", and its PDF author field "Research report prepared with ChatGPT".
- Sources 02–04 say "prepared for Vladimir Reshetnikov". Source 05 is a "research
  note prepared for Vladimir Reshetnikov" with an empty PDF author field.
- Source 06 is a "Research report prepared for Vladimir Reshetnikov"; source 07 a
  "Research draft" (title page, running head and PDF author field); source 10 "A
  mathematical research report" (PDF author field "Research report").
- **Source 08** is "Prepared for Vladimir Reshetnikov", and its title page calls
  it "This AI-assisted research draft".
- **Source 09 credits ChatGPT**: its author line and PDF author field read
  "Research manuscript prepared with ChatGPT".
- Source 11 is a "Research article prepared for Vladimir Reshetnikov" (running
  head "Research note"); source 12 a "Research article and reproducibility
  supplement"; source 13 is "Prepared for Vladimir Reshetnikov" (PDF author field
  "Research report prepared for Vladimir Reshetnikov"). 12 and 13 say the
  repository was inspected "through the (user-selected) GitHub connection".
- **Source 14 states ChatGPT authorship**: its title page reads "Research report
  prepared by ChatGPT" and its PDF author field "ChatGPT, prepared for Vladimir
  Reshetnikov" (delivered tex, lines 13 and 62).
- No source names a human author.
- Source 03 mentions "independent mathematical reviews", source 10 an
  "independent review", and source 14 an internal review "within the preparation
  process", none of which is part of their deliveries or recorded in the
  repository. Nothing in the report rests on them.
- Source 14 cites sources 04 and 10 of this report as "earlier unpublished
  project reports" (its Companion2026 and CompanionColoring2026).

Every result, proof, example, remark, question and limitation of the fourteen
manuscripts is printed. No proof was replaced by a pointer.

**Further sources, not yet written in.** Sources 15–17 (`eed2ab863`), 18–20
(`58aa0c493`) and 21–23 (`a902613c9`, placed while the third write was in progress)
are in this directory as prefixed files (listed under Files). The article does not
use them yet; a later write will add them as dated additions without renumbering
anything here. Their placement records 21 as answering 14's exponent-five question
and 23 as answering 13's Question 1; V.2 still states both as open.

## Why thematic Parts, and how they are filled

Sources 01 and 04 are independent manuscripts, not editions of each other: their
titles, pins and files differ, and they share 0.23 % of their text; the same holds
for 06 and 10. The overlaps are of *results*, not text, and each theme draws on
several sources. So each Part holds the sections of every source on its theme,
in source order; the sections of sources 06–10 follow those of 01–05 at the end
of each Part. Each section heading carries a source tag such as `[01]` and a line
naming the delivered section. Each manuscript's abstract and Section 1 are in the
front matter (F.6–F.15), with its title block quoted. Conventions sections open
the source's first chapter that uses them: 03 §2 and 10 §2 are in Part I, and 02
§2 and 04 §2 are in Part II. Source 07 is a chapter of Part II with a guide
written for this report (II.11) and its notation appendix first. Sources 11
and 12 are chapters of Part II with guides (II.22, II.33); logically 11 follows
02's Proposition 6.1 material and 12 continues 07's chapter, but both stand at the
end of Part II because nothing printed earlier may move. Source 02's
Appendix B, 08's Appendix A and 09's Appendices A–B, certificates for nearby
theorems, sit beside those theorems; 06's computation section (§7) is in Part IV
with its carry counts, and 09's Section 13 in Part III.

**Results proved by several sources** are printed in each source's own form,
because the forms and hypotheses differ and the proofs are independent. Examples:
general `[−a, b]` against `a = δ`; strict against non-strict events; all groups
against odd-order groups. A dated note at each later print names the first print,
credits every source, and says whether the proof is the same argument or a second
route:
- the one-sided mass bound (02 Thm I.9.1, 03 Thm I.14.1, 01 Thm I.4.1, 05 Lem
  I.17.3; added: 06 Thm I.21.1 in mass form, 10 Prop I.23.2);
- the one-cell envelope (01 Lem I.1.2, 02 Thm I.8.1);
- the Lemma 5.15 replacement (02, 03), sharpened by 06;
- exceptional sets (01, 06, 10: three models);
- the simultaneous partition (01 Thm I.5.1, 05 Thm I.18.2);
- the scale barrier (01 for one phase, 05 for m phases);
- cancellation through degree three, and the quartic term
  (03 on every group, 04 on odd order, `P_d = R_d`; added: 08 and 09);
- the odd-order three-cube polynomial (04, 08, 09) and the `ℤ/3` cosine polynomial;
- generalized von Neumann and the telescoping theorem (03, 04; added: 06, 10);
- elementary Proposition 7.3 (03, 10);
- the floor-pattern counts `C_k = F_k` (01, 04, 06) and their asymptotics (01, 06);
- rounding to sets (03, 04, 08, 09);
- iteration bookkeeping (03, 06, 10);
- added in the third write: the one-sided bound also in 13 (seven sources), the
  envelope and joint frontier (01, 02, 13), the partition and obstruction (01, 05,
  13), the telescope (also 13), the three-cube identity (08, 13) and support table
  (04, 08, 13, 14), the norm gap and leading `6√2` (04, reproved by 14), the
  colouring threshold (10, reproved by 14), collision-to-mode (07, 11, 12).

## Files

The directory holds 206 files: 10 at the root, 75 in `code/`, 95 in `data/`, 26 in
`figures/`. Of these, 38 were placed with sources 01–05 (besides the base's
`article.tex` and `README.md`, which the first write replaced), 46 with sources
06–10, 39 with sources 11–14, and 80 with later sources not yet written in (below);
`article.pdf` was added by the first write and rebuilt by the second and third.

**Report files**, written in the writes:

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

**Source 06, prefix `06-carry-discrepancy-`** (16 files; delivered under
`verification/` and `figures/`). `code/`: the standard-library certificate
verifier, the SciPy chamber generator that proposes the certificates, the
uniformity and density checkers, and the figure script (Matplotlib). `data/`: the
carry certificates (215 rational witnesses, 1,165 dual certificates), the compact
carry results with file hashes, the uniformity, density and bound-comparison
outputs, the verifier log, the package validation record, the delivered
verification README (`README_VERIFICATION.txt`, a documentation file of the
package, not its delivery README) and `provenance.json` (SHA-256 of 18 files,
verified 18/18 at intake). `figures/`: the comparison figure of Section IV.9.

```
code/06-carry-discrepancy-bound_comparisons.py
code/06-carry-discrepancy-compute_carry_chambers.py
code/06-carry-discrepancy-density_checks.py
code/06-carry-discrepancy-uniformity_checks.py
code/06-carry-discrepancy-verify_carry_certificates.py
data/06-carry-discrepancy-README_VERIFICATION.txt
data/06-carry-discrepancy-bound_comparisons.json
data/06-carry-discrepancy-carry_certificates.json
data/06-carry-discrepancy-carry_results.json
data/06-carry-discrepancy-density_results.json
data/06-carry-discrepancy-package_validation.json
data/06-carry-discrepancy-provenance.json
data/06-carry-discrepancy-uniformity_results.json
data/06-carry-discrepancy-verification_log.txt
figures/06-carry-discrepancy-bound_comparisons.pdf
figures/06-carry-discrepancy-bound_comparisons.png
```

**Source 07, prefix `07-transport-rigidity-`** (6 files). At the root, its
formalization plan (`FORMALIZATION.md`: proposed Lean obligations, not completed
code; pinned to `ae0e89574`). `code/`: the exact-arithmetic checks (standard
library, fixed seed 20261006) and the delivered Makefile. `data/`: the build
status, the source manifest with blob ids, and the recorded verification output.

```
07-transport-rigidity-FORMALIZATION.md
code/07-transport-rigidity-Makefile
code/07-transport-rigidity-checks.py
data/07-transport-rigidity-BUILD_STATUS.txt
data/07-transport-rigidity-source_manifest.json
data/07-transport-rigidity-verification.json
```

**Source 08, prefix `08-cube-fourth-order-`** (5 files). `code/`: the
exact-arithmetic verifier (673,227 four-sets in dimensions 2–6, the three-cube
classification, the counterexample polynomial by two independent enumerations)
and the delivered build script. `data/`: the recorded output, the source
provenance (blob ids, no commit) and a page-layout validation record.

```
code/08-cube-fourth-order-build.sh
code/08-cube-fourth-order-verify_cube_refinements.py
data/08-cube-fourth-order-layout_validation.json
data/08-cube-fourth-order-source_provenance.json
data/08-cube-fourth-order-verification_results.json
```

**Source 09, prefix `09-cubical-expansions-`** (7 files). At the root, its pinned
source audit. `code/`: the direct cube-average checks (standard library) and the
lattice census with Smith normal forms (SymPy), and the delivered build script.
`data/`: their two recorded outputs and the optional requirement (`sympy==1.14.0`).

```
09-cubical-expansions-SOURCE_AUDIT.md
code/09-cubical-expansions-build.sh
code/09-cubical-expansions-verify_expansion.py
code/09-cubical-expansions-verify_lattices.py
data/09-cubical-expansions-lattice_results.json
data/09-cubical-expansions-requirements-optional.txt
data/09-cubical-expansions-results.json
```

**Source 10, prefix `10-torsion-energy-`** (12 files; delivered under
`verification/`, `figures/` and the package root). `code/`: the runner and its four
diagnostics (density and phase, structural, torsion, polynomial colouring), and
the figure script. `data/`: the recorded results with script hashes, the formula
examples, the source manifest with blob ids, and the requirements (`numpy`,
`matplotlib`). `figures/`: the frontier figure of Section I.24.

```
code/10-torsion-energy-make_figure.py
code/10-torsion-energy-run_all.py
code/10-torsion-energy-verify_density_phase.py
code/10-torsion-energy-verify_polynomial.py
code/10-torsion-energy-verify_structural.py
code/10-torsion-energy-verify_torsion.py
data/10-torsion-energy-formula_examples.json
data/10-torsion-energy-requirements.txt
data/10-torsion-energy-source_manifest.json
data/10-torsion-energy-verification_results.json
figures/10-torsion-energy-phase_frontier.pdf
figures/10-torsion-energy-phase_frontier.png
```

**Source 11, prefix `11-affine-rigidity-`** (7 files). At the root, its
formalization plan (`formalization_plan.md`: proposed Lean layers, not compiled
code; pinned to `40f885098`) and its delivery-validation note (`validation.md`).
`code/`: the exact verifier (standard library, integer arithmetic) and the
delivered build script. `data/`: the pinned source record (`sources.json`, blob ids)
and the recorded verification output and log.

```
11-affine-rigidity-formalization_plan.md
11-affine-rigidity-validation.md
code/11-affine-rigidity-build.sh
code/11-affine-rigidity-verify.py
data/11-affine-rigidity-sources.json
data/11-affine-rigidity-verification_log.txt
data/11-affine-rigidity-verification_results.json
```

**Source 12, prefix `12-bohr-extension-`** (8 files). `code/`: the exact
extension checks (standard library), the Bohr and Fourier checks (NumPy) and the
figure script (Matplotlib). `data/`: their recorded outputs, the parameter ledger
and the build report (generator records that no shipped script produces).
`figures/`: the extension frontier of Section II.35.

```
code/12-bohr-extension-make_figure.py
code/12-bohr-extension-verify_bohr_fourier.py
code/12-bohr-extension-verify_extension.py
data/12-bohr-extension-build_report.json
data/12-bohr-extension-extension_validation.json
data/12-bohr-extension-parameter_ledger.json
data/12-bohr-extension-verification_bohr_fourier.json
figures/12-bohr-extension-extension_frontier.pdf
```

**Source 13, prefix `13-simultaneous-recurrence-`** (14 files; delivered under
`verification/` and `figures/`). `code/`: the four verifiers (partitions and
density: standard library; cubes and Fourier/counting: NumPy) and the figure
script. `data/`: their four recorded summaries and `provenance.json` (SHA-256 of
16 delivered files, all verified at intake, including the unshipped PDF, README and
manuscript). `figures/`: the density frontier (Section I.28) and the partition
frontier (Section V.53).

```
code/13-simultaneous-recurrence-make_figures.py
code/13-simultaneous-recurrence-verify_cubes.py
code/13-simultaneous-recurrence-verify_density.py
code/13-simultaneous-recurrence-verify_fourier_counting.py
code/13-simultaneous-recurrence-verify_partitions.py
data/13-simultaneous-recurrence-cube_verification_summary.json
data/13-simultaneous-recurrence-density_summary.json
data/13-simultaneous-recurrence-fourier_counting_summary.json
data/13-simultaneous-recurrence-partition_verification.json
data/13-simultaneous-recurrence-provenance.json
figures/13-simultaneous-recurrence-density_frontier.pdf
figures/13-simultaneous-recurrence-density_frontier.png
figures/13-simultaneous-recurrence-partition_frontier.pdf
figures/13-simultaneous-recurrence-partition_frontier.png
```

**Source 14, prefix `14-sharp-extremals-`** (10 files). `code/`: the exact
certificate checker (standard library), the diagnostics (NumPy, `decimal`) and the
figure script (Matplotlib). `data/`: the certificate and diagnostic results, the
tested environment, the delivered quality record and the source manifest (11 blob
ids; links on the moving branch `main`). `figures/`: the convergence figure of
Section III.37.

```
code/14-sharp-extremals-make_figures.py
code/14-sharp-extremals-verify_certificates.py
code/14-sharp-extremals-verify_results.py
data/14-sharp-extremals-certificate_results.json
data/14-sharp-extremals-environment.json
data/14-sharp-extremals-quality_checks.json
data/14-sharp-extremals-source_manifest.json
data/14-sharp-extremals-verification_results.json
figures/14-sharp-extremals-cube_convergence.pdf
figures/14-sharp-extremals-cube_convergence.png
```

**Sources 15–17, placed by `eed2ab863`, write pending** (21 files; not used in the
article):

```
15-collision-amplification-integration.md
code/15-collision-amplification-build.sh
code/15-collision-amplification-verify.py
code/16-phase-localization-make_figures.py
code/16-phase-localization-verify_cube_coefficients.py
code/16-phase-localization-verify_localization.py
code/16-phase-localization-verify_partitions.py
code/17-polynomial-restriction-build.sh
code/17-polynomial-restriction-verify.py
data/15-collision-amplification-provenance.json
data/15-collision-amplification-verification.txt
data/15-collision-amplification-verification_results.json
data/16-phase-localization-cube_results.txt
data/16-phase-localization-localization_constants.csv
data/16-phase-localization-localization_results.json
data/16-phase-localization-partition_results.json
data/16-phase-localization-pdf_review.txt
data/17-polynomial-restriction-source_manifest.json
data/17-polynomial-restriction-verification_results.json
figures/16-phase-localization-localization_constants.pdf
figures/16-phase-localization-localization_constants.png
```

**Sources 18–20, placed by `58aa0c493`, write pending** (21 files; not used in the
article):

```
code/18-arrangement-degeneracy-make_partition_figure.py
code/18-arrangement-degeneracy-verify_refinements.py
code/19-shared-interpolation-make_figures.py
code/19-shared-interpolation-verify_polynomial.py
code/19-shared-interpolation-verify_sampling.py
code/20-quadratic-counting-Makefile
code/20-quadratic-counting-verify.py
data/18-arrangement-degeneracy-provenance.json
data/18-arrangement-degeneracy-verification_results.json
data/19-shared-interpolation-poisson_constants.json
data/19-shared-interpolation-polynomial_results.json
data/19-shared-interpolation-sampling_results.json
data/19-shared-interpolation-source-audit.json
data/20-quadratic-counting-BUILD_REPORT.txt
data/20-quadratic-counting-source_manifest.json
data/20-quadratic-counting-validation_summary.json
data/20-quadratic-counting-verification_report.json
figures/18-arrangement-degeneracy-partition_exponents.pdf
figures/18-arrangement-degeneracy-partition_exponents.png
figures/19-shared-interpolation-sampling_extrema.pdf
figures/19-shared-interpolation-sampling_extrema.png
```

**Sources 21–23, placed by `a902613c9`, write pending** (38 files; not used in the
article):

```
code/21-characteristic-five-Makefile
code/21-characteristic-five-make_figures.py
code/21-characteristic-five-verify_order5.py
code/21-characteristic-five-verify_profiles.py
code/22-degree-filtrations-Makefile
code/22-degree-filtrations-verify_certificates.py
code/22-degree-filtrations-verify_norm_obstruction.py
code/22-degree-filtrations-verify_polynomial_patterns.py
code/22-degree-filtrations-verify_two_cubes.py
code/23-sharp-thresholds-Makefile
code/23-sharp-thresholds-check_fifth.py
code/23-sharp-thresholds-make_figure.py
code/23-sharp-thresholds-verify_prescribed_partitions.py
code/23-sharp-thresholds-verify_section16_gluing.py
data/21-characteristic-five-coefficient_convergence.csv
data/21-characteristic-five-mathematical_review.txt
data/21-characteristic-five-order5_cube_fourier_certificate.csv
data/21-characteristic-five-order5_verification.txt
data/21-characteristic-five-package_validation.json
data/21-characteristic-five-profile_validation_results.json
data/21-characteristic-five-profile_verification.txt
data/21-characteristic-five-source_manifest.json
data/22-degree-filtrations-SOURCE_LEDGER.json
data/22-degree-filtrations-certificate_verification.json
data/22-degree-filtrations-norm_obstruction_verification.json
data/22-degree-filtrations-polynomial_pattern_verification.json
data/22-degree-filtrations-two_cube_verification.json
data/23-sharp-thresholds-build_validation.json
data/23-sharp-thresholds-fifth_checks.txt
data/23-sharp-thresholds-gluing_checks.json
data/23-sharp-thresholds-partition_checks.json
data/23-sharp-thresholds-source_manifest.json
figures/21-characteristic-five-coefficient_convergence.pdf
figures/21-characteristic-five-coefficient_convergence.png
figures/21-characteristic-five-phase_envelope.pdf
figures/21-characteristic-five-phase_envelope.png
figures/23-sharp-thresholds-phase_thresholds.pdf
figures/23-sharp-thresholds-phase_thresholds.png
```

**Not shipped**, all retrievable from the arrival commits (`66f24b0d0` for 01–05,
`62e21161f` for 06–10, `08ab4187e` for 11–13, `d179062cc` for 14):
- the fourteen PDFs;
- the manuscripts of sources 01, 02, 03, 05 and 06–14, which are printed in the
  article;
- the delivery READMEs of 01, 02, 03, 05 and 06–14 (their limitations are carried
  below);
- the checksum manifests of 04 (`SHA256SUMS.txt`, 13/13), 12 (`SHA256SUMS.txt`,
  11/11) and 14 (`SHA256SUMS`, 13/13), all verified at intake (repository policy
  drops checksum manifests).

**Delivery names.** A shipped file is its delivered path, flattened, behind its
prefix:
- code (`.py`, `.sh`, `Makefile`) goes to `code/`;
- outputs, certificates, manifests and requirements go to `data/`;
- figures go to `figures/`;
- audit and provenance notes go to the root.

For example, source 01's `certificates/carry.json` is
`data/01-carry-transfer-carry.json`; source 06's
`verification/carry_certificates.json` is
`data/06-carry-discrepancy-carry_certificates.json`; source 10's
`verification/run_all.py` is `code/10-torsion-energy-run_all.py`.

## Labels and numbering

Label prefix **`gsr:`** (none at HEAD before this report). A label has the form
`gsr:<part>:<source>:<delivered label>`, with Part codes `dt` (I), `en` (II), `cc`
(III), `fp` (IV), `fz` (V) and `fm` (front matter). For example, source 02's
`thm:tail` is `gsr:dt:02:thm:tail`. The delivered labels collide across sources
(`thm:tail` in 01 and 02, `sec:lean` in 05, 06, 08 and 09, `lem:rounding` and
`eq:false-lower` in 08 and 09, …); under the prefixes they are distinct.

The first write added a label on every delivered section of 01–05,
`…:sec:d<k>` (67), two remark labels of source 03, the five Part labels, the
front matter's five section labels, and Part V's `gsr:fz:sec:crosswalk` and
`gsr:fz:sec:further` with 32 item labels: 538 labels (all 425 delivered labels of
01–05 among them: 01: 115, 02: 62, 03: 100, 04: 78, 05: 70). The second write added the
408 delivered labels of 06–10 (06: 85, 07: 75, 08: 93, 09: 89, 10: 66), a label on
each of their 69 delivered sections, the guide `gsr:en:sec:transport`, the remark
`gsr:cc:rem:falselower` (Remark W1) and 28 item labels in Part V: **1,045 labels**,
all distinct. No existing label was renamed or removed, and a comparison of the
`.aux` with a build of the first write's text found every one of its 538 labels
with the same printed number. A comparison with separate builds of the five new
delivered `.tex` files found all 408 of their labels present. The third write
added the 305 delivered labels of 11–14 (11: 70, 12: 69, 13: 86, 14: 80), a label
on each of their 51 delivered sections, the two chapter guides
(`gsr:en:sec:affine`, `gsr:en:sec:bohr`), the three write remarks W2–W4
(`gsr:en:11:rem:cutoff`, `gsr:en:14:rem:composition`, `gsr:cc:14:rem:q1`) and 17
item labels in Part V: **1,423 labels**, all distinct. A comparison of the `.aux`
with a build of `9f83dbe0f` found every one of its 1,045 labels with the same
printed number.

**Numbering.** Sections restart in each Part and carry its numeral (I.9; F.1–F.19
in the front matter). Statements and equations are numbered within sections. A
delivered statement or equation `k.j` keeps its index `j`; the exceptions are the
equations of sources 02, 03, 06, 11, 12 and 13, which numbered them through the whole
manuscript, and the appendices, which now carry Part numbers. Tables and figures
of sources 06–10 are numbered within their sections (Figure IV.9.1), so that the
global table and figure numbers of 01–05 do not move; the write's remark on the
false quartic bound is Remark W1; the third write's remarks have their own counter and
are W2–W4. Source 04's tags (M1)–(M7), (R1)–(R32),
(A1)–(A14), (Q1), (Q2) and (∗) are kept. **Bare numbers such as "Lemma 5.15"
refer to Gowers's paper**, as in the sources; this report's own numbers always
carry a Part numeral or an F. Section F.1 holds the full concordance of delivered
sections with sections here.

## Notation

No delivered symbol was renamed; one macro was (06's `\snapshot`, its own pin, is
`\snapshotsix`), and 09's `question` environment is set as this report's
"Research question". Section F.3 lists every letter whose meaning changes across
sources, with the tempting false readings, and each Part opens with
reading-conventions tables (one for 01–05, one for 06–10). The main collisions:
- **ℰ/E**: 02's `ℰ(w)` (N⁻³-normalized energy on `G × Ĝ`), 04's `ℰ_j` (unnormalized
  transform), 03's `ℰ(f) = ‖f‖⁴_{U²}` and `ℰ₍₂₎`, 05's captured energy `E`; 08's
  `E₄(f)` and `E_⟨2⟩(f)` and 09's `𝖤₄`, `𝖳₂` are 03's `ℰ(f)` and `ℰ₍₂₎(f)`; 06's
  `ℰ_d(g)` is an unnormalized cube energy.
- **Cube counts**: 03's and 04's `Q_d` are 08's `𝒞_d` and 09's `𝒞_d`; 08's
  `Q_d(f)` (quartic coefficient) and 09's `Q_d` (star count) are not cube counts.
- **R, P, T, F, A, K**: 03's `R_d` (parallelograms) = 04's `P_d` = 08's `R_d` =
  09's `P_d`; 08's `F_d` = 09's `A_d` = 03's `K_d`; 08's `K_d` is a binomial sum;
  04's `R_d` is a remainder; 04's `R_d(H)` is 01's `R(H, d)` and 06's `ℛ_d(H)`.
- **B_k, c_k**: 01's and 04's translation budgets differ; 06's `K_k` is 01's
  `B_k`; 06's `B_k(δ)` is a polynomial; 06's `c_k` is not 04's `c_k`.
- **δ, κ, h_k**: 07's `δ` is a failure probability; 07's `κ` a fibre ratio, 10's
  `κ_G(c)` a kernel size; 10's `h_k` is a fibre size, 06's `h_k` = `H_k`.
- **Q, T, ρ, s, L, M, m, q, η, γ**: several meanings each.
- **α**: a norm power in Gowers's α-uniformity; a correlation elsewhere.
- **Arcs**: 01's `r` and 05's `ε` are widths in turns; 02's `ρ = sin θ`, which is
  01's `s`.
- **Sources 11–14**: 11's `κ ∈ {0,1}` (involution in the target), 12's `κ` a
  translation-loss bound, 14's `κ = 2^{5/4}/12`; 11's `ℰ(f)` is the graph energy
  and its `E(S)` is 14's `E(A)`; 12's `χ(η)` is a majority function, not a
  character, and 14's `τ(ε) = χ(2ε)`; 13's `ρ` is `‖f‖_{U²}` but 14's `ρ, b` are
  Fourier moduli, **half of 04's `a, b`**; 14's `M_δ(u)` ranges over all groups of
  order coprime to 6 and norms at most `u`, 04's over primes above 16 and norm
  exactly `u`. 11's and 13's `question` environments are this report's
  "Research question"; 12's `\snapshot` is `\snapshottwelve`.

## What the report claims

Section F.2 of the article is the full status table. In short:

**Part I.**
- The sharp one-sided bound with extremizers (02, 03, 06, 10; case `a = δ`: 01, 05).
- 01's short-arc density tail with phase parameter `s`, occupied-mass exceptions,
  the optimal forced maximum and its trade-off. These are sharp in the finite
  weighted model, not claimed for arithmetic characters.
- The envelope `C² ≤ (1−ρ²)F² + ρ²L²` for real `f` (01, 02); 02's complex
  counterexample shows that real values are needed.
- The Lemma 5.15 replacement (02, 03). It needs `α > 0` and nonempty cells. 06's
  exact fixed-`M` optimum `min{P₊/(b(M−1)), S/(M−2)}` with extremizers, its
  Lemma 5.15 corollary, the simultaneous threshold `τ(α) = α/4 + 3α²/32 + O(α³)`,
  and exceptional-set and signed-drift versions.
- 10's optimal cap `M ≥ δ + δS/(2δ−S)`, the variance cap `M ≥ δ + V/δ`, the tail,
  and correlation transfer with an exceptional set.
- Lemma 2.3 with `√(rs/(9M))`, and `1/3` optimal, also under the exact Lean
  hypotheses (05).
- Corollary 2.4 with `36π`, `3α/4` and the same upper length (05).
- Fourier increments:
  - 01: `δ + 3δbκ/(4−(4−3δ)κ) ≥ δ + 3η/8` at length
    `⌊√((N/2π) arcsin(η/4δb))⌋`, for a real frequency, bounded weights and any `N`;
  - 05: `δ + δα/(4δ−α)` at length `≥ √(αN/(16πδ(1−δ)))`, with an exact integer
    length and a popularity bound;
  - 03: an adjustable version;
  - 10: the frontier `D_γ = δγη/(2δ−γη)` at length `⌊√(N arcsin((1−γ)η/2v)/2π)⌋`;
    at `γ = 1/2` this is 05's increment at 01's length.
- Simultaneous partitions (01, 05), the optimal exponent `1/(m+1)` (05), and the
  one-phase barrier `ℓ ≤ 1+√(3r(N−1))` (01).
- Spectral extraction with a Gram correction and width allocation (05).
- The phase-to-density transfer and refinement theorem, *conditional on*
  `PP(K,R₀)` (02).

**Part II.**
- 02's `𝒯_w(f,g)⁴ ≤ min{m(f)⁴𝒰(g), m(g)⁴𝒰(f)}ℰ(w)` on every finite abelian
  group, with coefficient 1 optimal, plus its deficits, alignment and rigidity.
- 03's cubic DRC certificate and its optimal scalar tangent `κ* = 0.95378…`.
- 03's elementary BSG bound `(c/8, 2¹⁹c⁻⁹)` and 10's `(c/4, 2¹⁰c⁻⁵)`, both far
  weaker than Reiher–Schoen.
- 04's exact interpolation (M1)–(M7); its restriction theorem with
  `κ_d = 1/(2(400d)^d)`, `Λ_d = 2(1+C(2d,2))(400d)^d`, over prime fields only; its
  arrangement interpolation.
- 07: the coupled-path rigidity theorem with transport profiles; Freiman order `k`
  when `2[1+(k−1)κ]δ < 1`; the sharp threshold `1/(2k)` for constant fibres; at
  Lemma 10.9, order five and (with the ambient package) order nine, allowances
  `120⁻⁵` and `75⁻⁵`; the root-law linear program, collision-to-mode, weighted and
  nonabelian versions.
- 10: Lemma 7.5 with `|B|/(k(h_k−1)+1)`, Corollary 7.6 with `2⁻²⁰⁹γ¹⁰³`, and a
  torsion budget for general finite codomains.

**Part III.**
- The exact quartic term `δ^{m−4}(R_d ℰ(f) + T_d ℰ₍₂₎(f))` (03, 08, 09). `K_d` is
  optimal over all groups, the power 4 is optimal for sets, and the fifth-order
  remainder is necessary.
- 09's complete four- and five-vertex classifications on every finite abelian
  group, the exact fifth order `δ^{m−5}(Q_d 𝖬₅ + S_d 𝖳₃,₅)`, sharpness through
  order six, the determinant-5 configuration and the all-prime family.
- 08's complete odd-order three-cube polynomial (support counts 12, 8, 28, 8, 1),
  Fourier lower bound `(δ⁴+E₄)^{p/4}`, inhomogeneous weights and the
  character-kernel survival criterion.
- **Refuted, on record:** `Q₃(F) ≥ δ⁸ + 12δ⁴‖F−δ‖⁴_{U²}` (Remark W1).
- 04's norm gap with equality and stability; the three-cube bound with leading
  `6√2 δ⁴u⁴`; the `u^{16/3}` correction with optimal exponent for
  `gcd(|G|, 6) = 1`; sharpness for sets.
- Generalized von Neumann and the telescoping error `(k−2)α` in place of `2^k α`
  (03, 04, 06, 10); 06's two-target bound and quadratic discrepancy
  `√δ B_k(δ) ε²` (sharp three-term variance factor); 10's mixed-`L^p` bound with
  kernel factors, sharp on `(ℤ/2ℤ)ⁿ`, and error `δ S_k(δ) η`.
- 10's exact dimension threshold `d ≤ Σ ⌈D_ℓ/2⌉²` for polynomial colourings
  (`D_ℓ ≤ k < p`).
- The lifting lemma (04 Lemma III.4.5; 03's remark).

**Part IV.**
- `|F(r)| = (∏ 2rᵢ) C_k` (01); integer intervals and the modular count (04); every
  finite `V ⊂ ℤ^k_{≥0}` containing 0 and the unit vectors (06).
- `C_k ≤ R(H_k, k)` (01, 04, 06).
- `C_k ≥ 2^{⌊k²/4⌋}` (01) and `C_k ≥ 2^{k(k−1)/2}` (04).
- `log₂ C_k ~ k²` and `log₂ A_k ~ k²`, using the classical threshold-function
  count (Zuev; Kahn–Komlós–Szemerédi as recorded by Baldi–Vershynin); an external
  input, not reproved; uniformly modulo `M` and for translation classes (06).
- The polynomial floor entropy (lower half external: Baldi–Vershynin).
- The certified counts (01, 04, 06).
- The local phase-extraction coefficients of 04 and 06.

**Part V.** Iteration bookkeeping: 03's density and length recurrence, 06's
discrete potential with optimal leading cost, 10's `321(δ₀⁻¹ − 1)` steps and exact
length propagation.

**Sources 11–14 (third write).**
- 11: `ε(f) ≥ Ψ_κ(t)` for `t < 1/7` (odd targets) or `t < 1/3` (involutions), with
  equality exactly for one value on a coset; correction for `ε < 1/9`; the inverse
  series `1/4, 5/32, 11/64, …`; the largest non-affine energy for `|G| ≥ 34`, and for
  all `𝔽_p^n → 𝔽_p^m`; partial domains; a refinement of Proposition 6.1 for
  `α⁴ > 8/9` (stated for odd prime `N`; the write notes it holds for every `N`).
- 12: sharp extension `3ε + 2κ < 1` and its boundary; global extension above `2/3`;
  the sharp mode bound `1 − χ(η)`; radius selection `ρ/(8d)`; smoothing
  `2⁻⁷⁴α⁹/π`; Theorem 10.13 with radius `α¹⁹/(3π2¹⁴⁹)` and `α⁵|X|/20000` — the
  `α⁵` fraction is already established inside the formal proof (`5α⁵/98304`, before
  it exports `α⁶/20000`); all densities via Gowers's printed schedule.
- 13: the partitions, obstruction and frontiers of Part I; the cube orbit
  identity over `𝔽_p^n` (= 08's on odd-order groups) with orbit-moment bounds; the
  interval constant `D_N(M) ≤ 2√2 b^{1/4}`; the telescope (as 03, 04).
- 14: `Q₃(δ+f) ≤ δ⁸ + 6√2δ⁴u⁴ + (9/4)^{1/3}δ^{8/3}u^{16/3} + O(δ^{7/3}u^{17/3})`
  uniformly over groups of order coprime to 6, with matching models, two-harmonic
  rigidity in `U²` (not `L²`) and indicator sharpness; exponent 6 on exponent-five
  groups (lower model `2^{3/4}/3`, not claimed optimal); coset stability and
  arrangement equality; exact polynomial-colouring supersaturation.

**Proved in the first write** (dated notes, each with its proof; listed in F.1):
1. **01's increment is at least 3/2 times 05's** (and 03's at `λ = 1/2`) at the
   stated parameters. With `κ = η/(2δb)`, the ratio is
   `3/2 + (3/2)(2−δ)κ/(4−(4−3δ)κ)`. The lengths are of the same order.
   Caveat, also proved there: 03's `λ → 0` and 05's `ε → 0` buy larger increments
   at shorter lengths (for small κ, 05 matches 01's increment at about 0.71 of
   01's length and 03 at about 0.50); at finite N, 05's exact length can exceed
   01's by one (corrected after the independent check; the first wording said
   "much shorter lengths").
2. **The four forms of the one-sided bound coincide** (`T = D/2`, `a = δ`,
   `b = 1−δ`).
3. **`c₃^odd = 2^{−1/2}`**, attained exactly by real parts of characters. It
   follows from 04's norm gap and answers 03's Research question for `d = 3`; the
   best odd-order leading constant is `R₃ c₃^odd = 6√2`.
4. **04's lower bound `2^{k(k−1)/2}` beats 01's `2^{⌊k²/4⌋}` for every `k ≥ 3`**,
   and equals it at `k = 1, 2`.

**Proved in the second write** (dated notes, each with its proof; listed in F.1):
5. **01 against 10's frontier.** With `κ = η/(2δb)`: 01's increment is at least
   10's `D_γ` iff `γ(4−κ) ≤ 3`, and at least `(3/2)D_γ` iff `γ(4−(2−δ)κ) ≤ 2`; so
   the 3/2 domination holds for every `γ ≤ 1/2` (where 10's length is at least
   01's), not along the whole frontier.
6. **06's fixed-`M` bound against the `M−1` corollary of 02/03**: at least as
   large, strictly for `α < 1`, equal at `α = 1` (the intake said "strictly").
7. **Iteration**: the leading coefficients of `δ₀^{1−p}` in the step counts of 06,
   10 and 03 satisfy `1/(cq) ≤ 1/(1−(1+c)^{−q}) ≤ (1+c)^p/(cq)`, `q = p−1`.
8. **Progression criteria**: in the paper's `α`, the powers of `δ` are
   `k2^{k−1}` (04), `(k−1)2^{k−1}` (10), `(k−½)2^{k−2}` (06) and `k2^k` (Lean
   `corollary_3_6`); 06's is the smallest for every `k ≥ 3`.
9. **10 implies the formal Lemma 7.5 and Corollary 7.6 conclusions**
   (`γ ≤ 1` is forced; `C ≥ 1`); not formalized.

**Proved in the third write** (each with its proof):
10. **Remark W2**: 11's formula fails for `ℤ/12 → ℤ/2` (`f = 1_{0,1}(x mod 4)`,
    energy `27 · 48 = 1296 > 1288`), so the cutoff 34 cannot simply be dropped;
    exhaustive search also gives `ℤ/4 → ℤ/2` (48 vs 40), `ℤ/5, ℤ/7 → ℤ/2`,
    `ℤ/6, ℤ/9 → ℤ/3`, while `ℤ/10, 14, 15, 16 → ℤ/2` obey the formula.
11. **Remark W3**: 11's Corollary 6.1 + 14's Theorem 4.2: for
    `θ = η/(6t³) ≤ 1/100` (odd targets) the error support is within `τ(θ)s` of a
    unique coset and has one value off a fraction `η/(2t²(1−7t))` — 11's Question 3
    in substance (the intake found the composition).
12. **Remark W4**: 14's Theorem 2.1 gives the limit in 04's display (Q1) in 04's
    own normalization (primes above 16, norm exactly `u`); the normalizations agree
    (`ρ = a/2`, `b₁₄ = b₀₄/2`, `β* = c/2`).
13. **13's Fourier increment against 01's**: same length; 01's increment is larger
    by the factor `1 + 2(1−κ)/(4−(4−3δ)κ) ∈ [1, 3/2]`.
14. Checked: 11's Corollary 11.2 needs no primality (the formal
    `proposition_6_1` has none); the hypotheses `C = −C`, `0 ∈ C` of 12's
    Theorem 3.2 are unused; the sets `H \ K` attain 14's coset envelope.

Recomputed independently at the second write: the `ℤ/11` counterexample (exact
enumeration of all `11⁴` frequency choices, and direct summation over all cubes);
09's determinant-5 configuration (`det B = −5`, `M_S r = (10,5,5,5,5,5)`, Smith form
`1,1,1,1,1,5`, moment 4 on `ℤ/5`); 10's `2⁻²⁰⁹γ¹⁰³`; 06's and 04's coefficients at
`k = 8` (`2⁻²¹²·⁷⁰` and `2⁻¹²¹·⁶⁶`); 07's endpoint `331257600001/335923200000 < 1`;
08's and 09's order-two closed forms (identical); 09's Stirling coefficients
against 08's and 03's counts (`d = 2, …, 7`). Script and output:
not shipped (the write's scratch record).

## What the report does not claim

No source claims a new bound for `r_k(N)`. All cite Leng–Sah–Sawhney's
`r_k(N) ≪ N exp(−(log log N)^{c_k})`, `k ≥ 5`, as the benchmark (10 also
Raghavan's 2026 `r₃` bound and Green–Tao's `r₄`). No source claims literature
priority or an exhaustive priority search, Lean compilation, or kernel
verification. Further limitations, kept in place and collected in Section V.2:
- sharpness in the weighted model, not for arithmetic characters (01);
- `36π` and `3/4` not claimed optimal, and sharpness only for linear phases,
  uniform arcs and symmetric widths (05);
- the coefficient 6 of the `u^{16/3}` term not claimed optimal, nor the
  higher-dimensional `P_d/√2` (04);
- the restriction theorem is prime-only and does not prove the Lean
  Lemma 9.3/Corollary 9.4 (04);
- `PP(K,R₀)` is imported (02);
- `R_d` is not claimed optimal on odd-order groups (03, 08; for `d = 3` it is not);
- orders five and nine are guaranteed orders, not maximal ones; the sharpness is
  for the directional defect `δ`, not `η`; the factors 243 and 2548.04 are not
  improvements of a global bound (07);
- 57 is a convenient constant; the sets in 08's sharpness theorem have densities
  tending to `δ` (08);
- 09's sixth-order certificates are not inverse theorems; no originality claim (09);
- the colouring theorem concerns declared polynomial coordinates only; no novelty
  claim for the polynomial method (Führer–Taranchuk credited); the
  Reiher–Schoen variant uses a published input (10);
- 06's leading entropy rests on Zuev's count;
- 11: radii `1/7`, `1/3` and the cutoff 34 are sufficient, not optimal; its
  Proposition 6.1 corollary needs `α⁴ > 8/9`; majority decoding (Blum–Luby–
  Rubinfeld) and the derivative identities are prior art;
- 12: sharpness is universal, not for prime cyclic groups with the same target;
  the component lemmas are borrowed; `3ε + rκ` and the factor 3 are not claimed
  optimal; `Y` is not claimed to contain a progression;
- 13: only the flexible-length frontier is claimed optimal; quartic sharpness is
  for weights; no rectification to integers;
- 14: the truncated expansion is not a finite-parameter bound; no `L²` rigidity;
  `2^{3/4}/3` is a lower bound only; the colouring condition is not Corollary 8.3;
  no peer review; the constants `c, C` of its Theorem 2.1 are not explicit;
- finite and numerical checks prove nothing general (all).

From the delivery READMEs:
- 05's spectral diagnostics test only the cyclic-character specialization, not the
  Gram corollary, and its exact constructions are not fast algorithms for very
  large `N`.
- 01's finite certificates are proof evidence for the finite counts only, and its
  verifier is ordinary Python.
- 06, 07, 08, 09, 10: the delivery READMEs repeat that the finite checks are
  supplementary, that no Lean build was run, and that nothing global is claimed.

## Further questions, and the standing rule

Section V.2 applies Vladimir's standing rule of 4 October 2026. The first write
grouped the 46 questions of 01–05 (01: 10, 02: 7, 03: 9, 04: 12, 05: 8) into 32
items. The second write added the 50 questions of 06–10 (06: 11, 07: 8, 08: 10,
09: 10, 10: 11; the intake dossier said 10 for source 10) and two question
paragraphs of 10, as 28 new items or dated sentences in existing items. The third
write adds the 45 questions of 11–14 (11: 9, 12: 12, 13: 12, 14: 12) as 17 new items
or dated sentences — 141 questions in all:
- **I**, density transfer: 13 items, 24 questions;
- **II**, the inverse step: 31 items, 40 questions and one paragraph, plus one
  marked question of the intake (below);
- **III**, cubes and progressions: 24 items, 44 questions and one paragraph;
- **IV**, floor patterns: 6 items, 13 questions;
- **V**, integration and formalization: 3 items, 20 questions.

- **Answered or advanced in the third write** (dated notes at the questions):
  - **04's Question 1 is settled by 14**: the secondary coefficient exists and is
    `(9/4)^{1/3}` (Remark W4); 04's Question 2 is answered in `U²`, not `L²`;
    04's Question 7 is advanced by 14's arrangement equality.
  - 11's Question 3 is answered in substance (Remark W3).
  - 13's Question 5 is solved by 06 in the weighted model with `M` fixed.
  - 05's anisotropic question is advanced by 13's obstruction with independent
    tolerances.
- **Marked question (the intake's derivation, in neither source):** with 12's sharp
  majority lemma in 11's correction step the radius `1/7` is reached at `ε = 6/49`,
  and since `Ψ₀(1/30) = 551/4500 < 6/49 < Ψ₀(1/29)` the cutoff of 11's theorem
  would become 30; not proved, recorded in item II.smallgroups.
- **Answered or advanced inside the report** (first and second writes):
  - 04's Question 8 is answered by 01 and, independently, by 06: the leading
    constant is 1 (classical threshold count); `C₄ = 154` is certified twice.
  - 03's question on `c_d^odd` is settled for `d = 3` by 04; 08's question
    "`κ₃^odd = 1/√2`?" is the same and is answered yes.
  - 03's question on the fifth and sixth coefficients: the fifth is answered by
    09; the sixth stays open (09 shows order-five torsion enters there).
  - 02's finite-cell extremal problem is solved by 06 in the weighted model; integer
    cardinalities and prescribed sizes stay open.
  - 06's Question 7 and 04's Question 10 are advanced by 10's torsion factors.
- **Not certified**, item IV.2: `C₅ = 8410` and `A₄ = 770` (intake recount,
  floating-point infeasibility side). 06 does not compute them either.
- **Refuted and kept on record:** the quartic lower bound with coefficient 12
  (posed and refuted by 08 and 09, also refuted by 03; not a claim of any source),
  Remark W1 with the counterexample. No claim of the ten manuscripts was found
  false, and none asserts an unproved theorem as proved.
- **Intake statements corrected at the second write:** 06's improvement over the
  `M−1` corollary is strict only for `α < 1`; 01 dominates 10's increment by 3/2
  only for `γ ≤ 1/2`; 10 asks 11 questions, not 10; 09's date for version 2 of
  Shi–Dong (24 August 2026) is wrong — arXiv lists 28 July 2026 (bibliography
  note).
- **Third write:** no claim of 11–14 was found wrong or unproved. Framing
  corrected in dated notes: 13 presents its Fourier increment as a gain without
  noting 01's larger one; 12's abstract says its radius selection "replaces"
  Corollary 10.11 (the ambient radius is selected); 12's list of open obligations
  (Sections 13, 16, 18) is incomplete; 14 places `HasMonochromaticAP` in
  `Sections08_09.lean` (it is in `Definitions.lean`, line 113). Kept as numerical
  evidence: 14's `2^{3/4}/3` on exponent-five groups.
- **Moved to further questions:** no unproved claim needed moving. External inputs
  (threshold counts, `PP(K,R₀)`, Plünnecke–Ruzsa, Reiher–Schoen for 10's labelled
  variant) are listed with their status.

## What was checked, and what was not

**At intake** (dossier of batch 115, 6 October 2026), all ten manuscripts were
read, every headline re-derived and the computable ones checked; all delivered
suites were rerun on copies and reproduced their recorded outputs (except
last-ulp floating-point diagnostics and 10's timestamps). For 06–10 the checks
included 06's fixed-`M` extremizers and `τ(α)`, 06's quadratic discrepancy on
random sets, 07's order five at the literal Lean hypotheses and its exact
endpoints, 08's counterexample and `R_d, T_d, F_d` to `d = 6`, 09's Stirling
multiplicities and determinant-5 certificate, 10's torsion sharpness, weighted
BSG and `2⁻²⁰⁹γ¹⁰³`, and the online existence of the cited 2026 preprints.

**At the first write:** every comparison of 01–05 with the formal project was
checked against the ledger and the Lean declarations at `25df8755d`; the four
statements above were proved; the short suites of 01–05 were rerun on copies.

**At the second write:** every comparison of 06–10 with the formal project was
checked at HEAD `764740f07` (Section V.1, second table, with files and lines);
statements 5–9 were proved and the recomputations above made; the short suites of
06–10 were rerun on copies by the routes below (Windows, Python 3.14.4), and all
outputs matched the shipped ones after removing carriage returns (10: script
hashes and printed outputs identical; its JSON carries a timestamp).

**At the third write:** every comparison of 11–14 with the formal project was
checked at HEAD `e1db00e99` (Section V.1, third table); the statements above were
proved and the checks listed there made (`ℤ/12` and the small-group table by
exhaustive search; 14's model identity by a direct cube sum on `ℤ/17`; 13's
increment identity on 200,000 exact rational draws); the suites of 11–14 were
rerun on copies by the routes below (Windows, Python 3.14.4, NumPy and Matplotlib
through `uv`): 11, 12, 14 and 13's partition and density outputs reproduce the
shipped files (after removing carriage returns, and 12's timing fields); 13's cube
and Fourier summaries differ only in last-ulp floating-point error fields
(`maximum_Fourier_error`, `flat_spectrum_equality_error`, around `10⁻¹⁸` and
`10⁻¹³`) and the NumPy version; 14's `make_figures.py` regenerated its figure on a
copy (bytes differ, as expected; the shipped figure is unchanged).

**Independent check of the write for sources 01–05 (6 October 2026).** An
adversarial check made by the intake after the first write (`18507e2b2`) rebuilt
that text (167 pages, byte-identical to its PDF), re-derived the four statements
proved there, re-checked all 56 Lean citations (correct, and unchanged at
`9f83dbe0f`), the ledger counts, the corrected-statement comparisons, merge fidelity
(all 67 delivered sections token-identical apart from declared interventions; all
**425** delivered labels — the first write's README said 424) and the question
counts, and refuted no write claim. Four wording defects were corrected in the
third write, with the first wording kept in dated notes: "Theorem 01 is therefore
the strongest" (false for lengths at finite `N`: 05's exact length can exceed 01's
by one, e.g. `N = 50`), "much shorter progressions" (a constant factor: about 0.71
and 0.50 of 01's length for small κ), the crosswalk row "Lemma 3.8" (it listed
Lemma 3.9's tool and now names `lemma_3_9_holds`, `Proofs03Minkowski:173`), and the
stronger Corollary 2.5 pair, which exists only *inside the proof* of
`cor25_large_scale`. Optional precisions were applied too.

**Independent check of the write for sources 06–10 (6 October 2026).** An
adversarial check after the second write (`9f83dbe0f`) rebuilt it (321 pages, no
warnings), recomputed Remark W1, re-checked 07's orders five and nine against the
Lean statements, the five proofs of that write, merge fidelity (408 labels, 50
questions) and the certificates, and found no mathematical error. Five wording
defects were corrected in the third write with dated notes: 07's chapter summary
named one of three order-nine requirements; V.2 said 01 dominates 10's increment by
3/2 "only for γ ≤ 1/2", which is false as worded (the bound holds exactly when
`γ(4−(2−δ)κ) ≤ 2`); a progression-threshold note cited 06's homogeneous corollary
for its existence corollary; the implication to `lemma_7_5` needs `B ≠ ∅` (the
empty case is trivial); and V.2 over-read the finite-cell item. (The check's
further point that V.2 omits 04's Q10 does not apply: that note already records
it.) The second write's commit message repeats "only for γ ≤ 1/2"; this README
(item 5 above) was already right.

**Not verified:** the external threshold-count theorems and the published
literature the sources compare with; the long proofs beyond the intake's
re-derivations.

## Relation to the formal project

The ledger (`gowers-proof-status.json`) moves while the Lean development is being
extended by another session. At the pins of 01–05 it recorded 88 exact companions
and 32 open statements; at `7d99e5dee` and `ae0e89574` (pins of 06, 09, 10 and
of 07) 95 and 25; at `40f885098` and `9ea383e9b` (pins of 11 and of 12–14) 97 and
23. At the first write (`25df8755d`) it recorded 98 and 22; at the second write
(HEAD `764740f07`) 99 and 21, and `FORMALIZATION_STATUS.txt` reported 196 modules
and 1,805 audited public theorems (06 quotes 140 and 1,365 from its pin); at the
third write (HEAD `e1db00e99`) 100 and 20 (`lemma_13_8` closed), 206 modules and
1,879 theorems (12 quotes 154 and 1,508 from its pin). Each source's comparison
with a corrected statement is accurate at HEAD except stale claims, which the
article corrects in dated notes:
- source 02 calls its partition input `PP(K,R₀)`, i.e. Corollary 5.6, "not … Lean-verified". It is now
  `corollary_5_6_holds` (`Proofs05FullPartition.lean`), with identical constants.
  The affine pullback of polynomials is formal (`polynomialOn_affine_pullback`),
  but 02's refinement theorem itself is not.
- source 03 (and implicitly 01) quotes the ledger as 88/32; sources 06 and 10 quote
  95/25, and 06 quotes 140 modules and 1,365 theorems; sources 12 and 13 quote
  97/23 (13 also in its `provenance.json`), and 12 quotes 154 modules and 1,508
  theorems.
- source 12 lists open obligations only in Sections 13, 16 and 18; the ledger also
  has open statements in Sections 1, 5, 7 and 8.

**Formalized:** exactly one statement of the ten sources, 04's Lemma III.4.5
(lifting a modular progression from a short interval) with 03's rectification
remark. They are `hasNatAP_of_short_modular_sequence` and
`hasNatAP_of_hasModAP_image` (`Proofs18IntervalTransfer.lean`, lines 22, 92),
added in `327773149`, which is 04's own pin, before arrival. Some baselines that
the sources improve are already proof-level facts of the development:
- Corollary 2.5's stronger pair, in `cor25_large_scale`;
- Lemma 9.2's exact Parseval, inside `lemma_9_2_holds`.

**Lemma 10.9 (source 07).** `lemma_10_9` (`Section10.lean`, line 335; companion
`lemma_10_9_holds`, `Proofs10Shift.lean`, line 717) concludes `FreimanHom 2 B' psi`.
07's order five has exactly its hypotheses (nonempty `W`,
`IsSection10ShiftRegular`, `IsSection10LocalDifferenceModel` with
`θ = 10η^{1/5}`, `6√θ < 1`) and does not use `(1−θ)|B| ≤ |B'|`. 07's order nine
also needs the fibre lower bound `α²M/16`, ambient invariance
`DomainInvariant D B (σM)` and `ρ ≤ α²/32`, `σ ≤ ηρα²/16` — hypotheses of
`lemma_10_6` and the Section 10 set-up, not of `lemma_10_9`; a formal order-nine
theorem needs a new statement. Neither order is formalized. Likewise 10's
Lemma 7.5 and Corollary 7.6 replacements imply the conclusions of `lemma_7_5` and
`corollary_7_6`, but that implication is not formalized.

**Sources 11–14.** No statement of theirs is formalized. The formal pieces they
rely on, by declaration: 12's component input is the output of `lemma_10_3_holds`
… `lemma_10_9_holds`, its Appendix A matches `lemma_10_6_holds` (with
`extractionMode`), and its scalar linearity follows from `corollary_10_14_holds`;
13's rectification remark is `hasNatAP_of_short_modular_sequence`; 11's corollary
consumes `proposition_6_1`. One more baseline is proof-level: the proof of
`theorem_10_13_holds` (`Proofs10Main.lean`) establishes `|W| ≥ ϱ²α²LN/16` with
`ϱ = α²/32` (line 1398), i.e. a retained fraction `5α⁵/98304`, and only then
spends `α ≤ 1/6` (line 1407) to export `α⁶/20000`.

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
  - 01's Makefile, 02's, 08's and 09's `build.sh` and 07's Makefile name the
    delivered files.
  - 02's `verify.py` overwrites `verification_results.json` beside itself; 06's and
    09's checkers write their JSON beside themselves (`verification/` in the
    delivery); 07's and 08's checkers write to `--output` (default in the current
    directory).
  - 05's `verify.py` does `from phase_partitions import …`; 10's `run_all.py` runs
    its four siblings by their delivered names and writes
    `../verification_results.json`; 10's `make_figure.py` writes `figures/` and
    `formula_examples.json` one level up; 06's `bound_comparisons.py` writes its
    JSON beside itself and its figure under `../figures/`, and needs Matplotlib.
  - 03's `make_figure.py` and 04's `make_figures.py` write into `./figures/`
    beside themselves.
  - 11's `build.sh` runs `checks/verify.py` and tees `checks/verification_log.txt`;
    `verify.py --output` defaults to the current directory, not `checks/`.
  - 12's two verifiers and figure script, 13's four verifiers and 14's two
    verifiers write their (unprefixed) outputs beside themselves; 13's
    `make_figures.py` writes `figures/` beside itself.
  - **14's `make_figures.py` reads `verification_results.json` beside itself**, so
    under the shipped names it fails; it runs on a copy with the delivered layout.

  Rerun on copies (below).
- **Source defects**, disclosed and not fixed in the delivered files:
  - 04's `.tex` wrote `_{epsilon\in\Omega_k}` twice, without the backslash; it is
    corrected in the article, with a dated note.
  - 10's `.tex` has `M_{\rm rest}` mangled three times into `M_{` + line break +
    `m rest}` (its PDF prints "M_{m rest}"); restored in the article, with a dated
    note.
  - 09's bibliography dates version 2 of Shi–Dong (arXiv:2607.20752) "24 August
    2026"; arXiv lists 22 July (v1) and 28 July 2026 (v2), checked at the second
    write. Corrected in a dated bibliography note.
  - 05's `SOURCE_AUDIT.md` says its pinned read of `Proofs02Partition.lean`
    "included lines 580–780". That file has 702 lines; its blob `291b149` and the
    construction described are correct.
  - 02, 05 and 08 link some repository files through the moving branch `main`;
    their blob ids are correct. 08 records no commit.
  - 02 records no pin in its README; its Appendix A gives the observed branch
    ref `66c02f8a1`.
  - 01's bibliography gives the public Gowers PDF under `users/gasarch`, the
    others under `~gasarch` (07, 08 and 09 also under `users/gasarch`).
  - 11's Appendix A shows two pdflatex passes, its `build.sh` three; its README
    (not shipped) says `python`, `build.sh` calls `python3`. 13's Lean-map row for
    Lemma 5.14 names `Proofs05Downstream.lean`; the companion is
    `Proofs05FullPartition.lean`, line 103 (via `Proofs05Lemma14.lean`, line 231).
  - 14 places `HasMonochromaticAP` in `Sections08_09.lean`; it is in
    `Definitions.lean`, line 113 (dated note in the article).
  - 10's `.tex` keeps two fragment-assembly comments ("Integration requirements:
    … No custom macros or citations"); they are invisible and kept.
- **Delivery names inside shipped text.**
  - 04's and 07's and 10's `source_manifest.json`, 03's `SOURCE_NOTES.txt`, 06's
    `provenance.json` and `README_VERIFICATION.txt`, 08's `source_provenance.json`,
    07's `FORMALIZATION.md` and `BUILD_STATUS.txt` and 09's `SOURCE_AUDIT.md`
    name delivered files.
  - 04's manuscript comment ("See README.txt") is quoted in F.9.
  - 01's `environment.json` records a generic Linux sandbox and no user paths.
  - 11's `formalization_plan.md`, `validation.md` and `sources.json`, 12's
    `build_report.json` and `parameter_ledger.json`, 13's `provenance.json` and 14's
    `source_manifest.json` and `quality_checks.json` name delivered files
    (`checks/verify.py`, `gowers_bohr_extension.tex`, …).
- **Edits of delivered text in the article**, listed in F.1:
  - prefixed labels and unified citation keys;
  - source tags on headings;
  - 02's plain "Section 3" made a live reference;
  - four figure paths;
  - two bookmark strings;
  - the missing backslash (04) and the damaged `\rm` (10) restored;
  - 06's `\snapshot` macro renamed, 09's question environment mapped;
  - 07's Appendix A placed first in its chapter;
  - third write: 11's and 13's `question` environments set as "Research question";
    12's `\snapshot` renamed `\snapshottwelve`; 12's ragged-right `tabularx`
    columns set inside its tables; 12's and 13's `\cref`/`\Cref` written out with
    the names cleveref prints (the installed cleveref cannot name theorems sharing
    a counter); four figure paths; 13's and 14's title-page statements printed as
    quotations.

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

Sources 06–10 (added in the second write; same variables):

```sh
mkdir -p "$T/r06/verification"
for f in verify_carry_certificates uniformity_checks density_checks; do
  cp "$R/code/06-carry-discrepancy-$f.py" "$T/r06/verification/$f.py"; done
cp "$R/data/06-carry-discrepancy-carry_certificates.json" "$T/r06/verification/carry_certificates.json"
(cd "$T/r06/verification" && $PY verify_carry_certificates.py &&
  $PY uniformity_checks.py > /dev/null && same uniformity_results.json "$OLDPWD/$R/data/06-carry-discrepancy-uniformity_results.json" &&
  $PY density_checks.py > /dev/null && same density_results.json "$OLDPWD/$R/data/06-carry-discrepancy-density_results.json")
mkdir -p "$T/r07" && cp "$R/code/07-transport-rigidity-checks.py" "$T/r07/checks.py"
(cd "$T/r07" && $PY checks.py --output verification.json > /dev/null &&
  same verification.json "$OLDPWD/$R/data/07-transport-rigidity-verification.json")
mkdir -p "$T/r08" && cp "$R/code/08-cube-fourth-order-verify_cube_refinements.py" "$T/r08/verify_cube_refinements.py"
(cd "$T/r08" && $PY verify_cube_refinements.py --output verification_results.json > /dev/null &&
  same verification_results.json "$OLDPWD/$R/data/08-cube-fourth-order-verification_results.json")
mkdir -p "$T/r09/verification"
for f in verify_expansion verify_lattices; do cp "$R/code/09-cubical-expansions-$f.py" "$T/r09/verification/$f.py"; done
(cd "$T/r09/verification" && $PY verify_expansion.py > /dev/null && same results.json "$OLDPWD/$R/data/09-cubical-expansions-results.json" &&
  $PY verify_lattices.py > /dev/null && same lattice_results.json "$OLDPWD/$R/data/09-cubical-expansions-lattice_results.json")
mkdir -p "$T/r10/verification"
for f in run_all verify_density_phase verify_structural verify_torsion verify_polynomial; do
  cp "$R/code/10-torsion-energy-$f.py" "$T/r10/verification/$f.py"; done
(cd "$T/r10/verification" && $PY run_all.py)   # writes $T/r10/verification_results.json
```

Sources 11–14 (added in the third write; same variables):

```sh
mkdir -p "$T/r11/checks" && cp "$R/code/11-affine-rigidity-verify.py" "$T/r11/checks/verify.py"
(cd "$T/r11" && $PY checks/verify.py --output checks/verification_results.json > checks/verification_log.txt &&
  same checks/verification_results.json "$OLDPWD/$R/data/11-affine-rigidity-verification_results.json" &&
  same checks/verification_log.txt "$OLDPWD/$R/data/11-affine-rigidity-verification_log.txt")
mkdir -p "$T/r12" && for f in verify_extension verify_bohr_fourier; do
  cp "$R/code/12-bohr-extension-$f.py" "$T/r12/$f.py"; done
(cd "$T/r12" && $PY verify_extension.py --output extension_validation.json > /dev/null &&
  $PY verify_bohr_fourier.py --output verification_bohr_fourier.json > /dev/null)
  # compare with data/12-bohr-extension-*.json except the elapsed/timing fields
mkdir -p "$T/r13/verification" && for f in verify_partitions verify_density verify_cubes verify_fourier_counting; do
  cp "$R/code/13-simultaneous-recurrence-$f.py" "$T/r13/verification/$f.py"; done
(cd "$T/r13/verification" && $PY verify_partitions.py > /dev/null && $PY verify_density.py > /dev/null &&
  $PY verify_cubes.py > /dev/null && $PY verify_fourier_counting.py > /dev/null &&
  same partition_verification.json "$OLDPWD/$R/data/13-simultaneous-recurrence-partition_verification.json" &&
  same density_summary.json "$OLDPWD/$R/data/13-simultaneous-recurrence-density_summary.json")
mkdir -p "$T/r14" && for f in verify_certificates verify_results make_figures; do
  cp "$R/code/14-sharp-extremals-$f.py" "$T/r14/$f.py"; done
(cd "$T/r14" && $PY verify_certificates.py > /dev/null &&
  same certificate_results.json "$OLDPWD/$R/data/14-sharp-extremals-certificate_results.json" &&
  $PY verify_results.py > /dev/null &&
  same verification_results.json "$OLDPWD/$R/data/14-sharp-extremals-verification_results.json" &&
  $PY make_figures.py)   # writes $T/r14/figures/cube_convergence.{pdf,png}
```

Requirements and run times:
- 02 and 10 need NumPy; 05's `verify.py` needs mpmath (even for `--part exact`);
  09's `verify_lattices.py` needs SymPy (1.14.0 was used); 12's
  `verify_bohr_fourier.py`, 13's `verify_cubes.py` and `verify_fourier_counting.py`
  and 14's `verify_results.py` need NumPy; the figure scripts of 12, 13 and 14 need
  Matplotlib.
- 13's cube and Fourier summaries record floating-point error magnitudes and the
  NumPy version; compare them field by field, not byte by byte.
- Do not run Python with `-O`: the 02, 05 and 06 checkers rely on assertions (06's
  verifier refuses to run under `-O`).
- Everything else uses the standard library.
- Each command runs in under a minute (05 exact: about 40 s; 07: about 40 s; 10:
  about 35 s; 14's `verify_results.py`: about 45 s; 14's figure: about 30 s).
- 10's `verification_results.json` records a timestamp and the Python version;
  compare its `stdout` and `sha256` fields with the shipped file instead of the
  bytes.

At the first write the 01–05 block, at the second write the 06–10 block, and at
the third write the 11–14 block (with NumPy and Matplotlib through `uv`) run
verbatim from the repository root (Git Bash on Windows, `PY=py`; 09 and 10 through
`uv run --no-project --with sympy==1.14.0` and `--with numpy`), completed all
comparisons. The longer checks also run on these copies:
- 01: `check_refinements.py` (NumPy, SymPy);
- 03: `verify_estimates.py`, compared with `verification_estimates.txt`;
- 04: `-S verify_refinements.py --output out.json` (two float diagnostics differ
  in the last digit);
- 05: `verify.py --part fourier` (mpmath, 80 digits).

The intake ran all of these. Regenerating certificates needs SciPy (01, 06);
regenerating figures needs Matplotlib (03, 04, 06, 10).

## Building the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Use pdfLaTeX (MiKTeX or TeX Live), in a scratch copy that contains `figures/`.
The build gives 452 pages, with no LaTeX warnings, no undefined references, no
duplicate destinations and no overfull boxes. Packages: amsmath, amssymb, amsthm,
mathtools, lmodern, geometry, microtype, graphicx, booktabs, longtable, tabularx,
array, enumitem, needspace, placeins, xcolor, hyperref, xurl, bookmark, tikz
(source 07's diagram), listings (source 08's certificate code) and tcolorbox
(source 12's result box). Only
`article.pdf` is committed.

## Licences

Repository text is MIT-0. The sources quote short passages of the cited
literature with attribution. No third-party paper, repository copy or font is
redistributed.
