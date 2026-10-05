# Airy Asymptotics for Tree-Child Networks

**Fixed combining degree, and the binary total count, deficit law and inverse (A213863)**

This research report, dated 2 October 2026, was built from four manuscripts: two of batch 77 and
two bundle reports of batch 102. No manuscript names a person as author; all four are AI-assisted
research reports.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 16 (base) | batch 77, manuscript 16 | `d-combining-asymptotics-reproducibility.zip` (main file `d-combining-asymptotics.tex`, 406 lines, 10-page PDF) | none | `34f1acd4b` | Part I, Sections 2–13 |
| 69 | batch 77, manuscript 69 | `tree-child-asymptotics-reproducibility.zip` (main file `article/tree-child-asymptotics.tex`, 1,233 lines, 23-page PDF) | none | `34f1acd4b` | Part II, Sections 14–20 |
| 104 | batch 102, bundle Report 104 | `Fixed_Degree_Tree_Child_Networks_All_Orders_Source.zip` (main file `general_tree_child_amplitudes.tex`, 926 lines, 22-page PDF) | none | `6ab1f1979` | Part III, Sections 21–32 |
| 102 | batch 102, bundle Report 102 | `A213863_Tableaux_and_Tree_Child_Networks_Source.zip` (main file `tree_child_amplitude_sources/tree_child_amplitude.tex`, 903 lines, 21-page PDF) | none | `6ab1f1979` | Part IV, Sections 33–41 |

The batch-77 archives arrived in commit `096ee7b87`. They were placed in this directory by `34f1acd4b`
(batch 77P3) and written into this report in batch 77P3, step 3 of 7. The bundle reports 104 and 102
arrived in `60f54ea06`, were placed by `6ab1f1979` (batch 102) with the file prefixes `104-fixdeg-` and
`102-tableaux-`, and were written in as Parts III and IV on 5 October 2026. No manuscript names a
repository commit, so none has a pin.

**Credit order.** The archives of sources 102 and 104 were closed on 1 October 2026 (22:36 and 23:18
Pacific time), before the batch-77 archives arrived (`096ee7b87`, 2 October, 11:05 Pacific). Both prove
the main theorem independently of Parts I–II and cite neither; source 102 does not cite source 104
(same delivery series, closed 42 minutes later). The theorem was printed here first, from sources 16
and 69; sources 104 and 102 are credited as independent further routes, not as derivatives.

**Authorship metadata.** Source 104's author line is "Research prepared for Vladimir / Report 104".
Source 102's title page and PDF metadata say "Research prepared for private review"; disclosed here, as
in the placement commit.

**Status.** AI-assisted research report, unrefereed and not formalized. No statement of this report has a
Lean or Rocq declaration. Each source's audits are independent research review by its producer, not
external peer review, publication, a proof-assistant check or numerical certification. No source
was published or submitted anywhere.

## What the report proves, and what it does not

**Claimed (Part I, source 16).** Fix d ≥ 2. Let a_n be the maximal-word diagonal of d-combining
tree-child networks, so that T^(d)_{n,n−1} = n!·a_{n−1}. Then
a_n = γ_d (n!)^(d−1) Γ^n exp(B n^(1/3)) n^ρ (1 + Σ C_{d,r} n^(−r/3)), to every finite order
(Theorem 2.1). Here Λ = (d+1)^(d−1)/(d−1)!, Γ = 4Λ, B = 3z((d−1)/(d+1))^(2/3) with z the largest zero of Ai,
ρ = −η − 1/2, η = (d−1)²/(2(d+1)), and C_{d,r} ∈ ℚ[B]. The amplitude γ_d > 0 is defined by convergent
limits. The same holds for T^(d)_{n,n−1}. For d ≥ 3 the total count gets only its leading equivalent.
*[5 October 2026, batch 102: at d = 3 Part III adds the first total-count correction, conditional on
source 104's reading of a published proof; see below.]*
Part I also gives the ternary logarithmic coefficients and a Lambert-W inverse with integer brackets.
At d = 2 the diagonal is A213863.

**Claimed (Part II, source 69, d = 2).** Theorem 14.1 is Theorem 2.1 at d = 2, with the explicit coefficients
c₁ = B²/18, c₂ = B⁴/648 and c₃ = B⁶/34992 − 1/9 (B = 3^(1/3) z), and four logarithmic coefficients. It has
its own complete proof in Section 15, printed as a second route. Theorem 16.2 transfers every finite order
to the total number TC_n of binary tree-child networks, with no new constant:
TC_n = (√e γ/12)(n!)² 12^n e^(B n^(1/3)) n^(−5/3) exp{B²/18 n^(−1/3) − 23B/72 n^(−2/3) + 161/288 n^(−1) + …}.
It rests on the Pons–Batle identity, proved by Lin–Liu–Liu–Liu–Xin (arXiv:2601.09551v3), together with
Chang et al. 2024. Theorem 18.1 expands the reticulation-deficit law around Poisson(1/2) with weights
e^(θm). Theorem 18.2 proves the exact eventual identity d_TV = (3/2)(1/ℛ_n − e^(−1/2)), where
ℛ_n = T_{n+1}/((n+1)! a_n), with
d_TV = |B|/(48√e) n^(−2/3) − 1/(192√e) n^(−1) + 167B²/(34560√e) n^(−4/3) + O(n^(−5/3)). Part II also gives
PGF and moment corrections and explicit inverses with integer brackets (Section 17).

**Claimed (Part III, source 104, every fixed d).** Theorem 22.1 proves Theorem 2.1 again for the word
counts, by two-step elimination in an exact gamma-product gauge G(p) = Λ^p ∏(1+i/(d+1))_p with a Gram
factor (a third route), with a new convergent amplitude formula (eq. 124). New for every d:
- C_{d,1} = B²(8(d+1)² − 27(d−1)²)/(810(d−1)²), negative exactly for d ≥ 4 (eq. 87);
- L_{d,2} = (B/3)(1/(d+1) − (d+1)²/(27(d−1)²)) and C_{d,2} = C_{d,1}²/2 + L_{d,2} (eqs. 146–147); the
  maximal-count second coefficient is C_{d,2} − B/3;
- the scalars σ₄, σ₅, h₁ of its gauge, and (computed in writing) h₂.

At d = 3 it re-derives Part I's ternary coefficients with identical values and adds
C_{3,3} = B⁶/25509168 + 43B³/52488 − 3/16. Proposition 28.1 gives T^(3)_n/T^(3)_{n,n−1} = 1 + O(n^(−1/2)) and
hence the first total-count correction T^(3)_n = (γ₃/32)(n!)³ 32^n e^(B n^(1/3)) n^(−3)(1 + B²/162 n^(−1/3) +
O(n^(−1/2))) (eq. 90). **This rests on source 104's reading of the proofs of Chang et al. 2024, Lemma 3.24
and Theorem 1.9(ii), which is not shipped and was not checked in writing** (Remark 28.2). Section 30 adds
the d = 4 diagonal 1, 1, 91, 51821, the d = 3 and d = 4 maximal prefixes, and the trap that A213864
(1, 1, 19, 1075, …) is not the d = 3 sequence. Section 29 gives amplitude-free rounding inverses, an
explicit Newton count and exact one-comparison threshold rules.

**Claimed (Part IV, source 102, d = 2).** Theorems 34.1, 37.1 and 38.1 prove Theorem 14.1 again in the
factorial gauge 3^p p! (a fourth route), with the amplitude formula γ₂ = √(2/27) p_∞ C_λ (eq. 205). New:
- L₅ = B(108 − B³)/8748 and L₆ = 2B³/2187 − 1/162 (eq. 217); Part II's own generator, rerun at order 9
  on a copy in writing, gives exactly these values (Remark 39.1);
- the ratio a_n/(12n a_{n−1}) through n^(−3) (eq. 220);
- Proposition 34.3: TC_n/TC_{n,n−1} = √e(1 + O(n^(−2/3))) and a total-variation distance O(n^(−2/3)) from
  Poisson(1/2), from Chang et al. Lemmas 3.17–3.20 alone, without the Pons–Batle identity used in
  Part II. It is weaker than Theorems 16.2 and 18.2 (Remark 34.4) and kept as a second route.

Its question on the n^(−2/3) total-count coefficient is answered by Part II's Theorem 16.2 (−23B/72 in
logarithmic form); see Section 41.

**Not claimed by any source:**
- uniformity as d → ∞;
- convergence of any infinite series;
- exponentially small or transseries corrections;
- higher-order total-count corrections for d ≥ 3 (at d = 3 Part III has the first correction only, and
  conditionally; at d ≥ 4 only the leading equivalent);
- a d ≥ 3 OEIS accession;
- a closed form, certified digits or an effective error constant for any amplitude;
- a certified threshold algorithm or an unconditional ceiling rule;
- novelty beyond a bounded literature search.

The uncertified diagnostics γ₂ ≈ 2.02264201 (Section 19) and 2.0226420146 (Section 39.3) are not claimed
values. Nor are the intake's fits γ₃ ≈ 3.784368, γ₄ ≈ 3.478351, γ₅ ≈ 2.384755 (Section 31): uncertified,
computed in writing with C_{d,1} fixed, script not shipped.

The Lambert-W inversions are instances of the repository volume *Transseries and inversion*
(`Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`, theorems
`p0:thm:lambert-core`, `p0:thm:perturbed-inversion`, `p0:thm:staircase`; Remark 11.1). No novelty is
claimed for them.

## How the sources are merged

Parts I–II (batch 77):

- **Base.** Source 16 (general d) is Part I, printed in full. Source 69 (d = 2) is Part II, printed in full,
  in its own order. Each Part opens with its source's abstract.
- **No result is dropped.** Source 69's Sections 2–8 prove Theorem 2.1 at d = 2, step by step. They are
  printed as Section 15, a detailed second route, because they hold binary-only explicit material: the
  quasimode φ₂, φ₃, the eigenvalue through ε⁵, s₂…s₇, h₁…h₃, the endpoint expansion and the N^(−4/3)
  coefficient. Four displays are literally identical in both sources and are printed once, in Part I:
  the polynomial–Airy identity, the triangular equation, the convolution estimate and the Catalan smoothing
  bound. Part II points to them.
- **Source 16's red flags** (batch-77 dossier R16.1–R16.3):
  - Its bibliography entry `Binary` had no locator. It is replaced by references to Part II
    (Section 10; bibliography note).
  - Its one-paragraph compactness step is spelled out in Remark 5.1, assembled from its shipped
    `16-dcomb-expanded-proof.md` and source 69's Section 3. The remark adds no new idea.
  - Its hash receipts name `/workspace/shared/…` paths; see the disclosures below.
- **Source 69's red flags** (R69.1–R69.2):
  - Its Sections 9 and 11 were converted Markdown. Their bold "Theorem"/"Proof" paragraphs are now
    environments (Theorems 16.2, 18.1, 18.2), and the inline `\href` citations are bibliography citations.
    The equation tags T1–T24 and D1–D14 are kept, and each now has a label. Source 69 has no tag D12.
  - Its sentence on an "extended-precision run" is qualified in Section 19. NumPy's `longdouble` is the
    80-bit format on x86-64 Linux, and the recorded run shows nonzero differences up to 2.0e−14. On Windows
    a rerun compares double with double and is vacuous.
- **Re-scoped question.** Source 16's open question 1 (all-order total counts) is settled at d = 2 by
  Part II and stays open for d ≥ 3 (Section 12).
- **Notation.** Each Part keeps its source's notation except for the renamings in the table of
  Section 1.4, which also prints the tempting false readings. The main renamings:
  - source 69's d_N(j), a_{N,j} → D_N(j), p_N(j) (Part I's, identical at d = 2);
  - its deficit ratio b_n(m) → β_n(m), and q_{n,m}, Q_m(t), G(t) → ω_{n,m}, Ω_m(t), 𝒢(t);
  - its R_n, r_s, M_n, π(m), p_n(m), ℓ_n(m) → ℛ_n, τ_s, X_n, π_{1/2}(m), π_n(m), lr_n(m);
  - its gap constant c₁ → a₂ (c₁ is also B²/18);
  - α_N → ξ_N in both sources (α is the network exponent);
  - the Duhamel window L → Δ in both;
  - source 16's inversion letters p, r, K, L_j, a, A → 𝗉, 𝗋, 𝖪, 𝖫_j, 𝖺, γ⋆;
  - source 69's generic-inverse letters → sans-serif (Section 17);
  - its target logarithm T → y, and its threshold ρ, η, r, N(Y) → σ, δ_Y, x_Y, 𝒩(Y).

  The renaming in Section 17 was re-verified symbolically: every displayed coefficient of h(x+δ) − y
  vanishes through ϑ³.
- **Bibliographies merged.** Source 16's `Chang` and `Thesis` are source 69's `Chang2024` and
  `ChangThesis`. Source 69's `OEIS` entry, uncited in its own text, is now cited.

Parts III–IV (batch 102, written 5 October 2026):
- **Order.** Source 104 (every d) is the more general new source and is Part III, printed in full.
  Source 102 (d = 2, the same architecture in another gauge) is Part IV. Its binary-specific material is
  printed in full; where its displays are literally Part III's at d = 2 (the formal system and
  algorithm, the uniform residual estimate, the forced-product proof) Part IV points to Part III and
  keeps source 102's extra remarks. This mirrors the order of Parts I–II. Each Part opens with its
  source's abstract and a section on provenance, credit, a map onto Parts I–II and its own notation table,
  and closes with "Further questions and research".
- **Union.** Every result, proof, remark, non-claim and question of both sources is printed. Results
  already in Parts I–II are marked as second routes with the Part I/II label named; nothing is presented
  as new to the repository that Parts I–II already had.
- **Notation** (Sections 21.3 and 33.3). Both sources call the Airy zero α, which is the network exponent
  here: α → z. Source 104's r, a, ℓ, g, ρ, θ, μ, χ, κ, η, b_A, c_j(d), b_j(d), c_d(n) → d−1, d+1, Λ, Γ, B/3,
  ρ, α, c, ℓ, η_f, c_A, C_{d,j}, L_{d,j}, a_n; source 102's ρ, γ_w, K_T, b_j → B/3, γ₂, γ_T, L_j. Their
  proof apparatus (two-step matrix, symmetrizer, Gram factor, inter-time ratio, Perron vector, products)
  is renamed to sans-serif or host-role letters (𝖬_n, Σ_n, 𝖪_n, 𝖱_n, ψ_n, P_n, u_n, 𝖳_n); targets and
  thresholds y, Y are swapped to agree with Sections 11 and 17. Every displayed conversion to the host's B
  was checked symbolically.
- **Dated notes** in Parts I–II (abstract, Sections 1.1–1.5, 2, 9, 10, 12, 14, 18, 19, 20) record where the
  new Parts answer, sharpen or bear on them; question 1 of Section 12 is re-scoped, questions 2–4 stay open.
- **Stale text corrected.** The sources' literature-priority sentences ("located no prior
  positive-amplitude equivalent", "the result here supplies the amplitude input", "the additional
  assertions proved here") are true of the literature they inspected and are qualified in place: the
  repository already held the theorem (Parts I–II).
- **Standing rule** (Vladimir, 4 October 2026). No claim of either source was found wrong. Moved to
  "Further questions and research": source 104's d = 3 ratio (its reading of Chang et al., Lemma 3.24, not
  shipped, unchecked), a second ternary total coefficient, any d ≥ 4 total correction, certified
  amplitudes, uniformity in d, exponentially small terms, an OEIS accession; source 102's certified
  amplitude, beyond-all-orders and sparse-regime questions. Source 102's question on the n^(−2/3)
  total-count coefficient is marked answered by Theorem 16.2. New write-phase questions: an identity-free
  all-order transfer, closed forms beyond two coefficients, L₇–L₉.
- **Bibliography.** Nine entries added from the two sources (AofA 2026 Pons–Batle framework, four 2026
  arXiv preprints, Elvey Price–Fang–Louf–Wallner, A213864, A213275, A167484); the others coincide with
  existing entries.

## Files

```
article.tex                                   the merged report (standalone LaTeX, internal bibliography)
article.pdf                                   the compiled report, 92 pages (contents on pages 1–4)
README.md                                     this guide
16-dcomb-expanded-proof.md                    source 16's expanded derivation notes, as delivered
16-dcomb-mathematical-audit.md                source 16's independent mathematical audit (of its draft)
16-dcomb-integrated-report-audit.md           source 16's audit of its integrated TeX
69-binary-mathematical-verification.md        source 69's verification scope record
69-binary-coef-certificate.md                 source 69's coefficient certificate
69-binary-coef-numerical-and-field-check.md   source 69's forward-numerics and Q[B] field check
69-binary-sources-source-status.md            source 69's literature and version receipts
104-fixdeg-SOURCES.md                         source 104's provenance, attribution and OEIS cautions
104-fixdeg-checks-README.md                   source 104's check-package guide (delivered names)
104-fixdeg-checks-RESULTS.md                  source 104's recorded suite result
104-fixdeg-qa-REVIEW.md                       source 104's document review of its 22-page PDF
102-tableaux-SOURCES.md                       source 102's primary-source provenance
102-tableaux-checks-README.md                 source 102's check-package guide (delivered names)
102-tableaux-checks-RESULTS.md                source 102's recorded suite result
102-tableaux-diag-README.md                   source 102's guide to its optional numerical diagnostics
102-tableaux-qa-REVIEW.md                     source 102's document review of its 21-page PDF
code/16-dcomb-verify_reduction.py             exact source-array vs shifted-array checks (d = 2..8)
code/16-dcomb-independent_checks.py           independent normalized-recurrence checks (N <= 20, d = 2..12)
code/16-dcomb-derive_coefficients.py          polynomial-Airy recursion for fixed d (COMBINING_D=2 or 3)
code/16-dcomb-numerical_diagnostic.py         uncertified floating diagnostics
code/16-dcomb-replay.sh                       source 16's replay driver (delivered layout)
code/16-dcomb-build_pdf.sh                    source 16's PDF build script (delivered; see below)
code/69-binary-check_exact_cocycle.py         exact gauge and recurrence checks
code/69-binary-verify_total_transfer.py       deficit polynomials and finite counting identities
code/69-binary-check_inverse.py               generic inverse cancellations
code/69-binary-reproduce.py                   source 69's replay driver (delivered layout)
code/69-binary-coef-derive_coefficients.py    polynomial-Airy recursion, d = 2, order 7
code/69-binary-coef-check_natural_field.py    Q[B] coordinate check
code/69-binary-coef-check_forward_numerical.py   uncertified forward diagnostics to n = 50000
code/69-binary-coef-check_frozen_numerical.py    uncertified tridiagonal eigenvalue check
code/69-binary-verif-check_independent.py          independent coefficient solves
code/69-binary-verif-check_independent_order7.py   the same through order 7
code/69-binary-verif-check_total_transfer.py       independent transfer algebra
code/69-binary-verif-check_total_transfer_order6.py   the same through degree 6
code/69-binary-verif-check_inverse_independent.py  independent inverse expansion
code/69-binary-verif-check_distribution.py         distribution normalization and moments
code/104-fixdeg-verify_exact.py               source 104's fail-closed exact verifier (checks/verify_exact.py)
code/104-fixdeg-run_checks.py                 its normal/-O and corruption harness (checks/run_checks.py)
code/104-fixdeg-build.sh                      its PDF build script (builds the unshipped manuscript)
code/102-tableaux-verify_exact.py             source 102's fail-closed exact verifier (checks/verify_exact.py)
code/102-tableaux-run_checks.py               its normal/-O and corruption harness (checks/run_checks.py)
code/102-tableaux-inputs-derive_tree.py       reference derivation snapshot (checks/inputs/), manifest-listed
code/102-tableaux-inputs-endpoint_tree.py     reference endpoint snapshot (checks/inputs/), manifest-listed
code/102-tableaux-inputs-verify_tree_formal.py   reference formal check snapshot (checks/inputs/), manifest-listed
code/102-tableaux-diag-reproduce_dp.py        optional exact DP and mpmath diagnostic (diagnostics/)
code/102-tableaux-build.sh                    its PDF build script (builds the unshipped manuscript)
data/16-dcomb-*.json, *.log                   source 16's recorded outputs (14 files) and its requirements
data/69-binary-*.json, *.log                  source 69's recorded outputs (26 files) and its requirements
data/104-fixdeg-*                             source 104's inputs, manifest, results and provenance (13 files)
data/102-tableaux-*                           source 102's inputs, manifest, results, diagnostics and provenance (16 files)
```

The `data/` directory holds exactly these 71 files:
- **Source 16 (15):** `clean-replay-summary.json`, `coefficients-d2.{json,log}`, `coefficients-d3.{json,log}`,
  `exact-replay.log`, `hash-receipt.json`, `independent-replay.log`, `independent_checks.json`,
  `integrated-hash-receipt.json`, `numerical-diagnostics.{json,log}`, `quality-checks.json`,
  `reduction-checks.json`, `requirements.txt`.
- **Source 69 (27):** `clean-replay-summary.json`, `coef-coefficients.json`, `coef-forward-numerical.json`,
  `coef-frozen-numerical.json`, `coef-natural-field.json`, `exact-cocycle-checks.json`, `inverse-check.json`,
  `logs-02-derive_coefficients.log`, `logs-03-check_natural_field.log`, `logs-06-check_independent.log`,
  `logs-07-check_independent_order7.log`, `logs-08-check_total_transfer.log`,
  `logs-09-check_total_transfer_order6.log`, `logs-12-check_forward_numerical.log`,
  `logs-13-check_frozen_numerical.log`, `quality-checks.json`, `reproduction-results.json`,
  `requirements.txt`, `sources-source-status.json`, `total-transfer-checks.json`,
  `verif-distribution-checks.json`, `verif-independent-checks.json`, `verif-independent-inverse-checks.json`,
  `verif-independent-order7-checks.json`, `verif-total-transfer-checks.json`,
  `verif-total-transfer-order6-checks.json`, `visual-quality.json`.
- **Source 104 (13):** `input_manifest.json` (checks/), `checks-provenance.json` (checks/provenance.json),
  `inputs-formal_coefficients.json`, `inputs-reference_sequences.json`, `inputs-ternary_degree6.json`
  (checks/inputs/), `results-normal.{json,log}`, `results-optimized.{json,log}`, `results-replay.log`,
  `results-suite.json` (checks/results/), `provenance-sources.json` (provenance/sources.json),
  `qa-release_replay.json` (qa/).
- **Source 102 (16):** `input_manifest.json`, `checks-provenance.json`, `inputs-endpoint_9.json`,
  `inputs-formal_9.json`, `results-normal.{json,log}`, `results-optimized.{json,log}`,
  `results-suite.{json,log}` (all under checks/), `diag-replay_100.{json,log}`,
  `diag-replay_100_optimized.{json,log}`, `diag-saved_dp_3000.json` (diagnostics/),
  `provenance-sources.json` (provenance/sources.json).

Every file other than `article.tex`, `article.pdf` and this README is byte-identical to the delivery.
Shipped names are the delivered names with the prefix `16-dcomb-`, `69-binary-`, `104-fixdeg-` or
`102-tableaux-`. Delivered subdirectories are folded into the name: `reproducibility/` is dropped for
source 16, and source 69's `coefficients/`, `verification/`, `logs/` and `sources/` become `coef-`,
`verif-`, `logs-` and `sources-`. For sources 104 and 102 (whose files lie under
`tree_child_amplitude_sources/` in source 102's archive) `checks/` is dropped for the scripts and the
manifest, and `checks/inputs/`, `checks/results/`, `checks/provenance.json`, `checks/README.md`,
`checks/RESULTS.md`, `diagnostics/`, `qa/` and `provenance/` become `inputs-`, `results-`,
`checks-provenance`, `checks-README`, `checks-RESULTS`, `diag-`, `qa-` and `provenance-`. Scripts go to
`code/`, recorded outputs to `data/`, and audit Markdown to the root.

**Not shipped (all retrievable with `git show 096ee7b87:docs/incoming/<archive>.zip`):**
- both manuscripts' PDFs, source 69's manuscript TeX and README, and its `article/build_pdf.sh`;
- the checksum ledgers, all verified at placement and retired: source 16's `SHA256SUMS` (29/29) and
  `manifest.json` (29/29), and source 69's `SHA256SUMS` (55/55);
- source 16's HTML renderings of its two audits;
- source 69's `coefficients/coefficients-order7.json`, byte-identical to the shipped
  `data/69-binary-coef-coefficients.json`;
- source 69's `logs/01`, `04`, `05`, `10` and `11`, byte-identical to the shipped JSON receipts
  `exact-cocycle-checks.json`, `total-transfer-checks.json`, `inverse-check.json`,
  `verif-independent-inverse-checks.json` and `verif-distribution-checks.json`.

**Not shipped from sources 104 and 102 (retrievable with `git show 60f54ea06:docs/incoming/<archive>.zip`):**
- both manuscripts (TeX and PDF) and their delivery READMEs; they are printed as Parts III and IV;
- both `MANIFEST.json` release inventories, verified at placement (25/25 and 34/34);
- both `verify_release.py` release verifiers, which only check the unshipped inventory and PDF (source
  104's fails on Windows; see below);
- both `checks/requirements.txt` (`sympy==1.14.0`), byte copies of a generic repository blob;
- source 102's `diagnostics/endpoint_9.json`, byte-identical to the shipped
  `data/102-tableaux-inputs-endpoint_9.json`.

Source 16's delivered README was staged as this file by the placement commit and is replaced here; it
survives as `git show 34f1acd4b:<this directory>/README.md`. Its scope statement is in Section 1.3 of the
article. No file of any archive was excluded as heavy regenerable data.

OEIS terms embedded in the shipped checkers and data (A213863 in source 102's checks; A213863 and computed
recurrence values in `data/104-fixdeg-inputs-reference_sequences.json`) come from the OEIS, whose content
is licensed CC BY-SA 4.0.

## Label prefix

Every label in `article.tex` carries the prefix `tcn:`: `tcn:sec:` and `tcn:part:` for the provenance
section and the Parts, `tcn:d:` for Part I (source 16), `tcn:b:` for Part II (source 69), `tcn:f:` for
Part III (source 104) and `tcn:w:` for Part IV (source 102). Source 16's 39 labels are kept with the prefix
`tcn:d:`. The article has **367** labels (170 before batch 102: 106 `tcn:f:`, 89 `tcn:w:` and 2
`tcn:part:` were added; none was renamed, removed or renumbered); the file staged at placement had 39.
No `tcn:` label has a Lean mapping.

## Delivered text that uses delivery names or names unshipped files

- `16-dcomb-mathematical-audit.md`:
  - It reviews an unshipped draft, `maximal-proof.md`, whose verdict names d ≥ 3. The integrated
    audit and the article claim d ≥ 2.
  - It compares against `oeis-a213863-research/release/tree-child-asymptotics.tex`, which is source 69's
    manuscript (same SHA-256, `86217958…`). That manuscript is not shipped; it is printed as Part II.
  - It mentions an audit directory with replay copies that is not shipped.
- `16-dcomb-integrated-report-audit.md` and `data/16-dcomb-integrated-hash-receipt.json` pin
  `/workspace/shared/d-combining-extension/release/d-combining-asymptotics.tex` (SHA-256 `70a1aab9…`). That
  is the delivered manuscript, i.e. the `article.tex` of the placement commit. The merged `article.tex`
  differs from it. `data/16-dcomb-hash-receipt.json` hashes `/workspace/shared/…` paths, including
  `maximal-proof.md` and source 69's manuscript.
- `16-dcomb-expanded-proof.md` calls source 69 "the frozen A213863 release".
- `data/16-dcomb-quality-checks.json` names `reproducibility/integrated-report-audit.md` and describes the
  delivered 10-page PDF.
- `data/69-binary-quality-checks.json` and `data/69-binary-visual-quality.json` describe source 69's
  delivered 23-page PDF, which is not shipped.
- `69-binary-coef-certificate.md` names `coefficients-order7.json` (see above) and gives commands in the
  delivered layout.
- `69-binary-coef-numerical-and-field-check.md` names `forward-numerical.out` and `natural-field.out`,
  which were never delivered. Its "main proof §7" is Section 15.6 here.
- `data/69-binary-reproduction-results.json` and `data/69-binary-clean-replay-summary.json` use delivered
  paths (`logs/…`, `coefficients/…`, `verification/…`), and the latter counts 53 manifest entries.
- `69-binary-sources-source-status.md` names `source-status.json`, shipped as
  `data/69-binary-sources-source-status.json`.
- `code/16-dcomb-build_pdf.sh` builds the unshipped `d-combining-asymptotics.tex`, so it cannot build this
  report. Use the command below.
- `code/104-fixdeg-build.sh` and `code/102-tableaux-build.sh` build the unshipped
  `general_tree_child_amplitudes.tex` and `tree_child_amplitude.tex`; they cannot build this report.
- `104-fixdeg-checks-README.md` and `102-tableaux-checks-README.md` give commands and file names in the
  delivered `checks/` layout (`run_checks.py`, `verify_exact.py`, `inputs/…`, `results/…`,
  `input_manifest.json`, `provenance.json`) and name the unshipped `requirements.txt`; source 102's also
  names `results/suite.log` as the output of its own command. `104-fixdeg-checks-RESULTS.md` and
  `102-tableaux-checks-RESULTS.md` name `results/…` files, shipped as `data/…-results-…`.
- `102-tableaux-diag-README.md` names `diagnostics/reproduce_dp.py`, `saved_dp_3000.json` and an
  `endpoint_9.json` copy in `diagnostics/`, which is not shipped (the `checks/inputs/` copy is).
- `104-fixdeg-SOURCES.md` names `provenance/sources.json`, shipped as `data/104-fixdeg-provenance-sources.json`.
- `104-fixdeg-qa-REVIEW.md`, `102-tableaux-qa-REVIEW.md` and `data/104-fixdeg-qa-release_replay.json`
  describe the delivered 22- and 21-page PDFs and the release replay, which are not shipped.
- The suite result files of both sources record the delivered names and SHA-256 values of the verifier,
  harness and input manifest; the shipped files are byte-identical, so the hashes still match (checked for
  source 102 in writing).

## Relation to other reports and to formal work

- `../a082161-airy-amplitudes` (relaxed and compacted trees and automata, written in the same batch)
  proves its amplitudes with the same family of lemmas. Its relaxed-binary identity
  (P″+4(x+a)Q′+2Q)F+(2P′+Q″)F′ is this report's polynomial–Airy identity at c = 2, ℓ = 2a. Neither report
  cites the other, and they stay separate (Section 1.5). Sources 104 and 102 belong to the same bundle
  delivery series as Reports 100, 101 and 103, which the batch-102 placement (`6ab1f1979`) filed as Part V
  of that report; they share its lemma family (positive Jacobi products, the killed half-line kernel, the
  forced-product bootstrap). Source 102's "companion relaxed-tree article" is presumably Report 100.
- `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/` supplies the inversion
  machinery cited above.
- No other repository report treats tree-child networks, A213863 or d-combining networks.
- **Formal status.** Placement in the repository confers no formal status. No Lean or Rocq declaration
  states any result of this report. The only related declaration is the real-number bracket lemma
  `staircase_separation` in `Analysis/FabiusFunction/Lean/FabiusFunction/StaircaseInversion.lean`, which
  formalizes the separation condition of `p0:thm:staircase` behind the integer brackets. It says nothing
  about these counts.

## Building the PDF

From a scratch copy of `article.tex` (pdfLaTeX, MiKTeX or TeX Live):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has 0 errors, 0 undefined references or citations, 0 multiply defined labels, 0 duplicate
destinations, and no overfull or underfull boxes. It yields 92 pages. Copy back only `article.pdf`.

## Rerunning the programs

The scripts use delivery-relative paths and write their outputs next to themselves, overwriting
same-named files. On Windows they write CRLF line endings. Never run them in this directory. Copy them
into the delivered layout in a scratch directory instead. Python 3 with the pins in
`data/16-dcomb-requirements.txt` and `data/69-binary-requirements.txt` (sympy 1.14.0, numpy 2.3.5,
scipy 1.17.0, mpmath 1.3.0); on Windows use `py` for `python`.

```sh
R=<repository>/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a213863-tree-child-networks
W=$(mktemp -d)

# Source 16 (delivered root: the archive root, scripts under reproducibility/)
mkdir -p "$W/16/reproducibility"
for f in verify_reduction independent_checks derive_coefficients numerical_diagnostic; do
  cp "$R/code/16-dcomb-$f.py" "$W/16/reproducibility/$f.py"; done
cp "$R/code/16-dcomb-replay.sh" "$W/16/reproducibility/replay.sh"
(cd "$W/16" && bash reproducibility/replay.sh)    # calls `python`; on Windows run its five lines with `py`

# Source 69 (delivered root tree-child-asymptotics/, with coefficients/ and verification/)
mkdir -p "$W/69/coefficients" "$W/69/verification"
for f in check_exact_cocycle check_inverse verify_total_transfer reproduce; do
  cp "$R/code/69-binary-$f.py" "$W/69/$f.py"; done
for f in derive_coefficients check_natural_field check_forward_numerical check_frozen_numerical; do
  cp "$R/code/69-binary-coef-$f.py" "$W/69/coefficients/$f.py"; done
for f in check_independent check_independent_order7 check_total_transfer check_total_transfer_order6 \
         check_inverse_independent check_distribution; do
  cp "$R/code/69-binary-verif-$f.py" "$W/69/verification/$f.py"; done
cp "$R/data/69-binary-coef-coefficients.json" "$W/69/coefficients/coefficients-order7.json"  # read by check_natural_field.py
(cd "$W/69" && python reproduce.py)               # add --numerical for the uncertified diagnostics
```

Compare the outputs with the shipped `data/` files using `diff --strip-trailing-cr` or by parsed JSON.
Source 16's driver writes `*.log` and `*.json` into `reproducibility/`. Source 69's driver writes `logs/`,
`reproduction-results.json` and the JSON receipts in place.

The batch-77 intake ran every piece on such copies, on a heavily loaded laptop:
- Source 16: `verify_reduction` 2 s, `independent_checks` 2 s, `derive_coefficients` 162 s at d = 2 and
  23 s at d = 3, `numerical_diagnostic` 57 s.
- Source 69: all 13 commands, 4–122 s each.

All passed. The exact outputs equal the shipped ones apart from CRLF, and the numerical outputs differ
only in the last floating digits. The intake also found that every entry of source 16's d = 2 coefficient
file agrees with source 69's order-7 file, which runs one order further. On Windows,
`check_forward_numerical.py --extended-check` compares double with double; see Section 19.

**Sources 104 and 102.** Both verifiers read `input_manifest.json` and refuse any input whose SHA-256
differs or any unexpected file, so the copies must reproduce the delivered `checks/` layout exactly.
Python 3.10+ with sympy 1.14.0; source 102's diagnostic also needs mpmath 1.3.0.

```sh
# Source 104 (delivered root: the archive root, checks under checks/)
mkdir -p "$W/104/checks/inputs" "$W/104/checks/results"
cp "$R/code/104-fixdeg-verify_exact.py" "$W/104/checks/verify_exact.py"
cp "$R/code/104-fixdeg-run_checks.py"   "$W/104/checks/run_checks.py"
cp "$R/data/104-fixdeg-input_manifest.json"  "$W/104/checks/input_manifest.json"
cp "$R/data/104-fixdeg-checks-provenance.json" "$W/104/checks/provenance.json"
for f in formal_coefficients reference_sequences ternary_degree6; do
  cp "$R/data/104-fixdeg-inputs-$f.json" "$W/104/checks/inputs/$f.json"; done
(cd "$W/104/checks" && python verify_exact.py --section all --output results/manual.json)
(cd "$W/104/checks" && python run_checks.py)     # full suite: normal, -O, 50 corruptions

# Source 102 (delivered root: tree_child_amplitude_sources/)
mkdir -p "$W/102/checks/inputs" "$W/102/checks/results" "$W/102/diagnostics"
cp "$R/code/102-tableaux-verify_exact.py" "$W/102/checks/verify_exact.py"
cp "$R/code/102-tableaux-run_checks.py"   "$W/102/checks/run_checks.py"
cp "$R/data/102-tableaux-input_manifest.json"  "$W/102/checks/input_manifest.json"
cp "$R/data/102-tableaux-checks-provenance.json" "$W/102/checks/provenance.json"
for f in derive_tree endpoint_tree verify_tree_formal; do
  cp "$R/code/102-tableaux-inputs-$f.py" "$W/102/checks/inputs/$f.py"; done
for f in endpoint_9 formal_9; do
  cp "$R/data/102-tableaux-inputs-$f.json" "$W/102/checks/inputs/$f.json"; done
cp "$R/code/102-tableaux-diag-reproduce_dp.py" "$W/102/diagnostics/reproduce_dp.py"
(cd "$W/102/checks" && python verify_exact.py --output results/manual.json)
(cd "$W/102/checks" && python run_checks.py > results/suite.log 2>&1)   # full suite: normal, -O, 44 corruptions
(cd "$W/102/diagnostics" && python reproduce_dp.py 100 replayed_dp_100.json)   # optional, uncertified

# Optional: L5 and L6 from source 69's generator (writes coefficients.json next to itself)
mkdir -p "$W/69g" && cp "$R/code/69-binary-coef-derive_coefficients.py" "$W/69g/derive_coefficients.py"
(cd "$W/69g" && python derive_coefficients.py --order 9)
```

`run_checks.py` rewrites `results/` in its copy; compare with the shipped `data/…-results-…` files by parsed
JSON, ignoring timestamps, durations and the Python version. The release verifiers are not shipped; source
104's `verify_release.py` fails on Windows in any case ("Unsafe inventory path": it requires
`str(Path(name)) == name`, which backslash paths break), a portability defect, not an integrity failure.

The batch-102 intake (5 October 2026) ran both suites on copies of the delivered archives, on a laptop
shared by several sessions. Source 104: a first run failed after 34 of 50 rejections during a machine-wide
resource shortage ("verifier did not produce result JSON"; that case rejects correctly in isolation); a
rerun passed (5,655 gates per baseline, 50/50 rejections, 475 s). Source 102: the harness kills each run
after 300 s, so a first run failed by timeout (302 s) under load; a rerun with the machine quieter passed
(4,999 gates per baseline, 44/44 rejections, 690 s; the delivered record took 136 s); direct verifier
runs passed in both modes (114 s each); `reproduce_dp.py 100` reproduced the delivered replay; source
102's `verify_release.py` passed. Regenerated results equal the delivered ones apart from timestamps,
durations and the Python version (3.14.4 here, 3.12.14 delivered). Source 69's generator at `--order 9`
took 392 s and printed `logforward_n` ending in exactly L₅ and L₆. In writing, the `finite` sections of
both verifiers were rerun from the shipped files in the layout above and passed (5,519 and 4,737 gates).
