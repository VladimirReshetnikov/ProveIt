# Local Quantitative Refinements of Gowers's Proof of Szemerédi's Theorem

**Density transfer and phase-flat partitions; energies, restriction and dependent random choice; cube and progression counts; floor patterns and the Proposition 17.7 phase extraction**

This is a research report built on 6 October 2026 from thirty-three research
manuscripts, all dated 6 October 2026. Sources 01–05 were merged in the first write
(batch 115, `18507e2b2`); sources 06–10 were added in a second write the same day
(`9f83dbe0f`), sources 11–14 (batch 116) in a third (`b16ce380d`), sources 15–20
(batches 117–118) in a fourth (`eae64ceca`), sources 21–27 (batches 119–120) in a
fifth (`4b7266a65`), and sources 28–33 (batch 121) in a sixth, each time as dated
additions that renumber and relabel nothing printed before. Each source
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

- **Part I — density transfer and phase-flat partitions** (sources 01, 02, 03, 05; 06, 10; 13; 16, 18, 19; 23, 26; 32).
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
  - 16: exact partitions whose own steps control affine frequencies (the Lemma 13.5
    interface): every balanced exponent below `1/((q+1)(42q+1))`, conditional on
    Lau's preprint, and an obstruction at `1/(3q+1)`.
  - 18, 19 (two independent proofs): simultaneous polynomial partitions with
    exponents polynomial in the number of phases — `1/(126q²+129q+2)` for
    quadratics, `1/(99q+98)` for a shared leading coefficient (18), degree profiles
    (19) — conditional on Maynard's published theorem; this **answers 13's
    Question 3**. Volume obstructions `(qk(k+1)/2+1)a + kqb ≤ 1` and
    `(S+1)a + Db ≤ 1`.
  - 23: prescribed-length simultaneous linear partitions are governed by the
    conductor of the semigroup of allowed lengths; for lengths `L, L+1` the
    threshold is `L^{q+2}/∏εᵢ (1+o(1))` (leading constant one), and a mixed-radix
    obstruction, valid even with cell-dependent steps, shows that the frontier
    `(q+2)a + qb = 1` is optimal — this **answers 13's Question 1** (13's exponent
    `1/(3q+2)` is optimal). Exact packing and almost-partitions.
  - **The chapter "Corollary 5.8 without a scale threshold" (I.40; source 26):** at
    degree one, gain `α/3` at length `(N/M)^{1/3}/8` on every cyclic group, against
    `α/16` and `(N/M)^{1/16}/8` in the open formal `corollary_5_8`; it implies that
    statement's degree-one instance, which holds trivially (a singleton) whenever
    `N/M ≤ 2^48` (proved at the write). Its degree-two sibling, source 32, is placed
    and belongs in this chapter.
  - **Source 32 in the same chapter (I.45–I.48):** at degree two, gain `α/3` at length
    `max{1, (N/M)^{1/39}/17}` on every cyclic group with no scale threshold, through an
    explicit recurrence `p ≤ 2¹⁰R⁵` and lossless quadratic partitions above
    `2¹¹⁶L³⁸`; it implies the degree-two instance of `corollary_5_8`, so with 26 the
    instances `k ≤ 2` have written proofs (not formalized; the ledger is unchanged).
- **Part II — the inverse step** (02, 03, 04; 07, 10; 11, 12, 14; 15, 17, 18, 19; 22–25, 27; 28–31, 33).
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
  - **Source 15's chapter (Lemmas 14.6–14.8):** the collision count kept through
    the product-property step and the interpolation: `β^{22·4^k}γ^{44k4^k+56·2^k}`
    for eight-arrangements, against `β^{28·4^k}γ^{84k4^k}` in the formal
    `lemma_14_8` (new); its interpolation, cubic cap, Cartesian equality, stability
    and joint normal form repeat 04 and 14, its stability constants are weaker.
  - **Source 17's chapter (Section 9):** one Fejér filter gives retention
    `α^mη^{m−1}/(2(m+2)^m)` above an explicit polynomial threshold; at order eight
    `α^{16}η^{15}/(2·18^{16})` in place of `(αη/4)^{2^{19}}`, which **proves the
    prime-modulus case of the formal `lemma_9_3`** with an explicit `N₀`; against
    04's restriction theorem, a better constant for `d ≤ 97`, a worse threshold.
  - **Sources 18 and 19 (Sections 15–16):** the degenerate-arrangement density
    `(k+C_d)/p + O(p⁻²)`, `C₈ = 2,585,444`, and Lemma 15.5 with
    `λp ≥ k + 2,585,445` (18); common sampling with `⌈qd/σ⌉ − 1` anchors, an exact
    minimax, the sharp constant `φ³e^{−φ} = 0.83996…`, shared-slice interpolation
    and a local replacement in Lemma 16.10, which itself stays unproved (19).
  - **Source 24's chapter (Section 7):** mostly second routes to 03 and 10 (the cubic
    certificate and scalar optimum of 03; 10's fibre extraction and modern-input
    corollary), with weaker constants where they differ (`2⁻²⁹⁵γ¹⁰³` against 10's
    `2⁻²⁰⁹γ¹⁰³`); new: an extraction for codomains `𝔽_p^d` independent of `d`, which
    beats 10's torsion budget there when `Q_k ≤ p^{d−1}`, `k ≥ 2` (proved at the
    write), and a parameterized selector. Proposition 7.3 "in every abelian group"
    is already formal (`proposition_7_3_group_holds`).
  - **Sources 22, 25, 27 on Lemma 15.4 and 23 on Lemma 16.10 (guide II.81):** 18's
    leading coefficient `k + C_d` re-derived independently by 25 (with the
    codimension-one classification over prime-power fields and a selection theorem
    for every `d`) and 27 (every characteristic, core directions, a cubic
    remainder); 22's degree-stratified finite bound and **`d = 1`: `(k²+3k)/p`**;
    **27's second coefficient `(k²+21k−6)/2` for `d = 2`**, answering 18's first
    question, and an exact count `5/q + 8/q² + 40/q³ − 367/q⁴ + 563/q⁵ − 248/q⁶` for
    `k = 1`, `d = 2`; 22's thresholds gain nothing over 18's at Lemma 15.5 at
    leading order. 23: a common base partition with width `(m/3)^A` and exact
    transport, without an inherited-coordinate hypothesis (a formalization
    candidate).
  - **Sources 31 and 29 at the Proposition 6.1 endpoint (guide II.104):** the exact
    optimal near-extremal `U³` profile `1 − F ≤ (1 − √((1+√(1−4δ))/2))/2` for
    `δ = 1 − κ < 1/120` on every finite abelian group, equality on `ℤ/2`; selected
    graphs with errors `≤ ε` and infidelity `≤ (1−√(1−2ε))/2`, separately sharp (31);
    29's `20ε`, `22ε` (superseded), soft and mixed selectors.
  - **Source 31 on Section 7 (guide II.114):** 10's fibre restriction with weights (10's
    progression is never shorter; `2⁻³⁶³c¹⁷¹` against 10's `2⁻²⁰⁹γ¹⁰³`); the selected
    derivative correlation kept through an exact restriction on `𝔽_p`, which answers
    02's Subsection 11.1 in that form.
  - **Source 29 at Lemma 9.3 (guide II.119):** over a fixed `𝔽_q`, threshold
    `8qS/(αη)`, then none, with every degenerate tuple kept (04's Question 4 and 17's
    Question 2 for fixed fields; not the all-moduli `lemma_9_3`).
  - **Sources 28 and 30 at Section 10 (guide II.121):** logarithmic selection retaining
    `αp(α)/20` with `O(α⁻³)` original-domain frequencies and radius `Ω(α⁵)` (28); a
    fixed-radius escape inequality `2m·b_B(d) ≤ |B(3ρ/2)| − |B| ≤ (3^r−1)|B|`, both
    parts sharp, and a proof that exponential dependence on the rank is necessary
    (30, whose extension and compatibility steps are 12's, uncited).
  - **Source 33 at Lemma 12.3 (guide II.136):** `max{θ⁷, 4θ−3}N³²` respected
    eight-arrangements, and full-product repair `δ ≤ ε_s/s + 2(s−1)ε_s²/s² + O(ε_s³)`
    with both coefficients sharp.
- **Part III — cube and progression counts** (03, 04; 06, 08, 09, 10; 13, 14; 16, 18, 20; 21, 22, 23; 28, 29).
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
  - The expansion through order five twice more (16, 18: independent derivations
    of 09's theorem; 18 shows by Smith forms that only 2 and 3 enter).
  - **Source 20's chapter (Section 3):** two marked functions with an `L²` gain for
    surjective homomorphisms, the sharp directional-to-global constant, and
    `|Λ_k(1_A) − δ^k| ≤ B_k(δ)u²` with a coefficient **strictly below 06's**
    (proved at the write); the exponent 2 is sharp for indicator sets of density
    near 1/2 on `𝔽₂₉^{2m}` (new).
  - **Source 21's chapter (exponent five), with 23's second route:** on every group
    of exponent five `Q₃(δ+f) ≤ δ⁸ + 6√2δ⁴u⁴ + (2^{3/4}/3)δ²u⁶ + Cu⁸` for `u ≤ cδ`,
    absolute constants, sharp — this **answers 14's Question 1**; the phase
    envelope, rigidity, the next coefficient **20/9 on ℤ/5ℤ**, indicator sharpness.
  - **Source 22's chapter (polynomial colourings):** the exact pointwise pattern
    minimum `q^{max(n−B,0)}` for every pattern and degree; the quintic budget eight
    is sharp at a prescribed centre; no independent additive extension of the norm
    colouring.
  - **Sources 29 and 28 on `c_d^odd` (guide III.66):** `‖f‖^{16}_{U⁴} ≥ (35/8)‖f‖^{16}_{U²}`
    for real centered `f` on odd-order groups, `c_d^odd ≤ B_d ↓ 1/2`, `c_d^odd ≥ 1/3`
    (29); `c₄^odd ≥ 0.5587294` and no single-cosine extremizer for `d ≥ 4` (28); with
    the intake's exact `ℤ/7` certificate, **`0.5587725 ≤ c₄^odd ≤ 0.6914416`** among
    sources 01–33 (34, 35 and 45, placed, record better upper bounds).
- **Part IV — floor patterns** (01, 04; 06; 16).
  - `|F(r)| = (∏ 2rᵢ) C_k`, with `2^{k(k−1)/2} ≤ C_k ≤ R(H_k, k)`; general
    coefficient families and modular counts (06).
  - `log₂ C_k ~ k²`, using the classical threshold-function count (01, 06; 06
    also uniformly modulo every `M ≥ 2`).
  - Certified `C₁..C₄ = 1, 2, 10, 154` (twice: 01 and 06) and
    `A₁..A₃ = 2, 6, 38` (04; 06's `D_k`).
  - Local coefficients at Proposition 17.7: `2^{−k²−k log₂ k−O(k)}` (04) and
    `2^{−2k²−O(k log k)}` (06).
  - **Source 16's chapter: Proposition 17.7 without carry patterns**, retention
    `(4/(3(k+2)))^{k+2}` — a drop-in strengthening of the formal
    `proposition_17_7`. In one normalization (cells `l` or `l+1`, normalized by
    `(l+1)^{k+2}`) the bits lost at `k = 8` are 29.07 (16), **91.07 (04, re-derived
    at the write; its own normalization gives the 121.66 quoted earlier)**, 212.70
    (06) and 1,458 (formal).
- **Part V — formal interface, ledger crosswalk, research questions.** The
  writes' crosswalk to the ledger, the deduplicated list of the sources'
  358 questions, iteration bookkeeping (03, 06, 10), and each source's
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
| 15 | *Collision-Sensitive Amplification of Respected Arrangements: sharp refinements of Gowers's Lemma 14.7, coupled product-property bounds, and Cartesian stability* | `collision_sensitive_arrangements.zip` (487,136 B, 9) | `collision_sensitive_arrangements.tex`, 1,752 lines, 27 pp. | `9ea383e9b` | `eed2ab863` | F.20; II.45 (guide), II.46–II.56; V.59–V.63 |
| 16 | *Local Phase Removal Without Carry Patterns, and further quantitative refinements of Gowers' proof of Szemerédi's theorem* | `Gowers_Localization_and_Quantitative_Refinements.zip` (669,627 B, 15) | `Gowers_Localization_and_Quantitative_Refinements.tex`, 2,127 lines, 30 pp. | `dca9f0638` | `eed2ab863` | F.21; I.30–I.31; III.39; IV.10 (guide), IV.11–IV.14; V.64–V.68 |
| 17 | *Polynomial-loss restriction in Gowers's Szemerédi argument: Fejér filters, density-sensitive moments, and finite-field systems* | `Gowers_Polynomial_Restriction_Research.zip` (427,352 B, 7) | `article.tex`, 1,327 lines, 21 pp. | `dca9f0638` | `eed2ab863` | F.22; II.57 (guide), II.58–II.64; V.69–V.74 |
| 18 | *Higher-Order Cube Expansions and Sharp Degeneracy Bounds in Gowers' Szemerédi Framework: simultaneous polynomial partitions, exact constants, and quantitative obstructions* | `gowers_cubes_degeneracy_partitions.zip` (685,030 B, 10) | `gowers_cubes_degeneracy_partitions.tex`, 2,672 lines, 35 pp. | `dca9f0638` | `58aa0c493` | F.23; I.32–I.33; II.65 (guide, with 19), II.66; III.40; V.75–V.79 |
| 19 | *Efficient Interpolation in Gowers' Szemerédi Framework: exact sampling losses, shared refinements, and simultaneous polynomial recurrence* | `gowers_interpolation_article.zip` (752,841 B, 13) | `gowers_interpolation.tex`, 2,505 lines, 32 pp. | `dca9f0638` | `58aa0c493` | F.24; I.34; II.67–II.71; V.80–V.82 |
| 20 | *Quadratic Counting Errors and Sharp Directional Bounds in Gowers's Szemerédi Argument: two-function uniformity, torsion-sensitive constants, and a sharp three-term obstruction* | `gowers_quadratic_counting.zip` (483,898 B, 10) | `article.tex`, 1,535 lines, 21 pp. | none (observed checkpoint `1bd57e91c`) | `58aa0c493` | F.25; III.41 (guide), III.42–III.48; V.83–V.86 |
| 21 | *Sharp Characteristic-Five Cube Bounds in Gowers's Framework: optimal sixth-order correction, phase rigidity, and an eighth-order extremal term* | `gowers_characteristic_five.zip` (815,428 B, 19) | `gowers_characteristic_five.tex`, 1,775 lines, 24 pp. | `43306653a` | `a902613c9` | F.26; III.49 (guide), III.50–III.57; V.87–V.90 |
| 22 | *Degree Filtrations in Gowers' Ramsey Framework: sharper degeneracy bounds, exact polynomial pattern thresholds, and obstructions to extending norm constructions* | `gowers_degree_stratification.zip` (391,101 B, 14) | `gowers_degree_stratification.tex`, 2,071 lines, 30 pp. | `43306653a` | `a902613c9` | F.27; II.82–II.85; III.60 (guide), III.61–III.65; V.91–V.92 |
| 23 | *Sharp Thresholds and Extremal Constants in Gowers's Szemerédi Framework: numerical semigroups, characteristic-five cube asymptotics, and common partitions for affine fibres* | `gowers_sharp_thresholds.zip` (832,508 B, 17) | `gowers_sharp_thresholds.tex`, 2,320 lines, 33 pp. | `65f4e039f` | `a902613c9` | F.28; I.35–I.39; II.103; III.58–III.59; V.93–V.95 |
| 24 | *Sharper local structure in Gowers's Szemerédi argument: moment-sensitive dependent random choice, small difference sets, and vertical-fibre compression* | `gowers_section7_refinements.zip` (484,922 B, 7) | `gowers_section7_refinements.tex`, 1,711 lines, 22 pp. | `2e0553b0c` | `79d9075b9` | F.29; II.72 (guide), II.73–II.80; V.96–V.101 |
| 25 | *The Codimension-One Degeneracies of Gowers Arrangements: an asymptotically sharp replacement for Lemma 15.4 and explicit random-selection thresholds* | `gowers_arrangement_degeneracy.zip` (444,249 B, 10) | `arrangement_degeneracy.tex`, 1,207 lines, 17 pp. | `568d1802e` | `79d9075b9` | F.30; II.81 (guide, with 22, 27, 23), II.86–II.92; V.102–V.104 |
| 26 | *Threshold free affine density increments on cyclic groups* (Report275) | `Report275_Threshold_Free_Affine_Density_Increments.zip` (405,485 B, 9) | `article.tex`, 494 lines, 12 pp. | `c94998a5d` | `79d9075b9` | F.31; I.40 (guide), I.41–I.44; V.105–V.106 |
| 27 | *Sharp Degeneracy Bounds for Gowers Arrangements: hyperplane obstructions, second-order structure, and an exact finite-field count* | `gowers_arrangement_degeneracy (2).zip` (518,856 B, 9) | `article.tex`, 1,824 lines, 28 pp. | none (blob ids only) | `79d9075b9` | F.32; II.93–II.102; V.107–V.110 |
| 28 | *Logarithmic Selection, Local Freiman Models, and Higher Uniformity* | `gowers_logarithmic_selection.zip` (650,769 B, 14) | `gowers_logarithmic_selection.tex`, 2,594 lines, 36 pp. | `e3125e698` | `c5513046e` | F.33; II.121 (guide, with 30), II.122–II.127; III.66 (guide, with 29), III.70; V.111–V.114 |
| 29 | *Further Quantitative Refinements of Gowers's Szemerédi Argument: higher norm comparisons, joint quadratic rigidity, and restriction by affine rank* | `gowers_moments_stability_restriction.zip` (725,320 B, 19) | `gowers_moments_stability_restriction.tex`, 2,256 lines, 30 pp. | `e3125e698` | `c5513046e` | F.34; II.110–II.113 (in II.104's chapter); II.119 (guide), II.120; III.66 (guide), III.67–III.69; V.115–V.117 |
| 30 | *Fixed-radius Bohr invariance in Gowers's Szemerédi argument: escape-tube bounds, larger Freiman-extension neighborhoods, and exponential-rank obstructions* | `Gowers_Fixed_Radius_Bohr_Invariance.zip` (414,517 B, 10) | `article.tex`, 1,278 lines, 19 pp. | `8d65d3c9f` | `c5513046e` | F.35; II.128–II.135 (in II.121's chapter); V.118–V.121 |
| 31 | *Weighted Derivative Spectra and Sharp Local Rigidity: explicit Freiman restriction, an optimal near-extremal U³ profile, and the limits of stability for correlation weights* | `gowers_weighted_spectrum_rigidity.zip` (371,304 B, 14) | `gowers_weighted_spectrum_rigidity.tex`, 1,745 lines, 25 pp. | `e3125e698` | `c5513046e` | F.36; II.104 (guide), II.105–II.109; II.114 (guide), II.115–II.118; V.122–V.124 |
| 32 | *Threshold free quadratic density increments on cyclic groups* (Report276) | `Report276_Threshold_Free_Quadratic_Density_Increments.zip` (410,590 B, 9) | `article.tex`, 533 lines, 12 pp. | `c94998a5d` | `c5513046e` | F.37; I.45–I.48 (in I.40's chapter); V.125–V.126 |
| 33 | *Sharp High-Agreement Stability for Gowers's Respected Arrangements: full-product decoding, optimal error terms, and erasures* | `Gowers_Respected_Arrangement_Stability.zip` (481,838 B, 19) | `article.tex`, 1,623 lines, 24 pp. | `9f83dbe0f` | `c5513046e` | F.38; II.136 (guide), II.137–II.143; V.127–V.129 |

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
text); every overlap involving 11–14 is below 1 %. Sources 15–20 arrived in
`212999d4b` (15), `82bc38a30` (18, 19), `99f28708e` (16), `060528502` (17) and
`83f3171c1` (20); `eed2ab863` ("Place batch 117") staged 15–17 and `58aa0c493`
("Place batch 118") 18–20 and retired their archives (`git show <arrival>:docs/incoming/<archive>`);
intake records `dossier117_GOWERS` and `dossier118_GOWERS`. The numbering follows the
two batches, so 18 and 19 arrived between 15 and 16. Source 15's pin predates every
placement here; the pins of 16–19 and 20's checkpoint contain source 04's
manuscript as `article.tex` (placed sources 01–10) but not the first write. Every
overlap involving 15–20 is at most 1.06 %; 18 and 19 prove the same partition
theorem independently. Sources 21–23 arrived in `26908b3b6` (the merge
`f7efeb4f5` dropped them; `e3125e698` restored byte-identical copies), 24 in
`e2bf630b0`, 25 in `d7c4aa399`, 26 in `7e827c6f3` and 27 in `6078f6e16`;
`a902613c9` ("Place batch 119") staged 21–23 and `79d9075b9` ("Place batch 120")
24–27 and retired their archives; intake records `dossier119_GOWERS` and
`dossier120_GOWERS`. 21–23 are numbered in ASCII order of archive name, 24–27 by
arrival. Archive 27, `gowers_arrangement_degeneracy (2).zip`, is an independent
manuscript, not an edition of 25 (0.57 % shared text). 24's pin predates every
placement here; 21–23, 25 and 26 saw the first write; 27 records blob ids only. No
two of 21–27 share more than 1.53 % (21 and 23, which prove the same theorem
independently); 25 and 27 re-derive 18's leading coefficient without having seen
18. Sources 28 and 29 arrived in `624d7a42a`, 30 and 31 in `12da35673`, 32 in
`6c2e2172b` and 33 in `17dd7886c`; `c5513046e` ("Place batch 121") staged them and
retired their archives; intake record `dossier121_GOWERS`. They are numbered by
arrival and then in ASCII order of archive name. 32 shares 4.70 % of its text with
its sibling 26, 33 1.11 % with 11; every other overlap involving 28–33 is at most
0.93 %. 28, 29 and 31 share a pin and overlap pairwise without citing each other (28
and 29 on `c_d^odd`, 29 and 31 on the Proposition 6.1 endpoint); 30 repeats parts of
12 and 31 parts of 10 without citing them.

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
- Sources 15, 16, 18 and 20 are "prepared for Vladimir Reshetnikov" (15 a "Research
  manuscript", 16 and 18 a "Research report"); source 17 is a "Research note
  prepared for the ProveIt project". None of the five contains an AI statement,
  and none is invented here.
- **Source 19's PDF author field reads "ChatGPT, research report prepared for
  Vladimir Reshetnikov"** (its title page: "Prepared for Vladimir Reshetnikov");
  its source audit records the retrieval method "GitHub plugin read tools".
- No source names a human author.
- Source 03 mentions "independent mathematical reviews", source 10 an
  "independent review", source 14 an internal review "within the preparation
  process", source 18 that its core derivations "were cross-reviewed independently
  within this task" and source 19 a written-proof review independent of the
  initial derivation, none of which is part of their deliveries or recorded in the
  repository. Nothing in the report rests on them.
- Source 14 cites sources 04 and 10 of this report as "earlier unpublished
  project reports" (its Companion2026 and CompanionColoring2026).
- **Sources 21, 22, 24 and 25 credit ChatGPT**: 21's title page reads
  "Mathematical research report prepared by ChatGPT" (PDF author field "ChatGPT;
  prepared for Vladimir Reshetnikov"), and its shipped
  `mathematical_review.txt` records an "AI-assisted" review, not peer review;
  22 is a "Research report developed with ChatGPT"; 24 a "Research draft prepared
  with ChatGPT"; 25 has "Mathematical development and computational checks with
  ChatGPT".
- **Source 27 is "An AI-assisted research draft"** (title page and PDF author
  field), naming no system.
- Source 23 ("Research article prepared for integration into the ProveIt
  repository") and source 26 ("Research report prepared for Vladimir") contain no AI
  statement; none is invented here.
- Sources 21, 22 and 23 cite manuscripts of sources 14, 18 and 13 as earlier
  project reports, by their file names.
- **Sources 28, 29, 30, 31 and 33 credit ChatGPT**: 28 and 33 "Mathematical
  development and computational checks with ChatGPT" (33: "exact computational
  checks"; its title page adds that no human authorship or independent referee review
  is implied), 29 and 31 "Mathematical development and verification with ChatGPT", 30
  "Mathematical development and exact checks with ChatGPT"; 28 says it was
  "separately checked by other reasoning agents", 31's `VALIDATION.json` records
  "internal AI-assisted reviews" and no independent human peer review.
- Source 32 ("Research report prepared for Vladimir") contains no AI statement; none
  is invented here.

Every result, proof, example, remark, question and limitation of the thirty-three
manuscripts is printed. No proof was replaced by a pointer.

**Further sources, not yet written in.** Sources 34–39 (`bf2fe146d`) and 40–46
(`2dfe46f44`) are in this directory as
prefixed files (listed under Files). The article does not use them yet; later writes
will add them as dated additions without renumbering anything here. Their placements
record findings that bear on this text: 34, 35 and 45 record upper coefficients
`81/16`, `5` and `4795/832` for `c₄^odd` (better than 29's `35/8`); 34 answers 07's Question 1 and 09's question on
the prime-onset function; 35 answers 23's question on polynomial phases; 38 reduces
the exponent-five problem to `ℤ/5ℤ` at small `u/δ`, answering three of 21's
questions; 39 re-derives 19's sampling minimax; 40 replaces the repeated Riesz
products of Lemma 15.5 by one Fejér kernel; 41 (Report277) proves the whole of
Corollary 5.8 in every degree with no scale premise, extending 32, and 42 (Report278)
replaces 26's cube-root length cap by a square root, both for 26's chapter; 43 and 46
continue 36 in characteristic two; 44 computes the second Whitney coefficient of the
cross-section arrangement in every dimension, answering two of 27's questions; 45
improves the upper bound for `c_4^odd` and extends 14's coset envelope. V.2 still
states those questions as open.

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
with its carry counts, and 09's Section 13 in Part III. The fourth write adds five
chapter guides: 15 (II.45) and 17 (II.57), which logically follow 04's Sections II.10
and II.8–II.9; 18 and 19 on Sections 15–16 (II.65); 20 (III.41), beside 06's
Section III.5; and 16 (IV.10), the strongest of the four Proposition 17.7
coefficients in Part IV. Source 16 is split over four Parts; 18's Section 6
(quantitative consequences) is in Part V, like 04's Section 9; 19's Section 8 (worked
comparisons) stays with its Section 16 chapter. The fifth write adds five
guides: the Part I chapter on Corollary 5.8 without a scale threshold (I.40, 26;
planned for 26, its degree-two sibling 32, and 41 and 42); 24's Section 7 chapter (II.72), which
logically follows 03's Sections II.5–II.6 and 10's II.20–II.21; a guide to 22, 25 and
27 on Lemma 15.4 and 23 on Lemma 16.10 (II.81), continuing 18's II.66 and 19's
chapter; 21's exponent-five chapter (III.49), with 23's Section 7 and Appendix A as a
credited second route, after 14's III.35; and 22's colouring chapter (III.60), after
10's III.30 and 14's III.36. 23's partition sections (I.35–I.39) logically follow
13's I.26. The sixth write adds six guides: the Proposition 6.1 endpoint (II.104; 31,
then 29 as a second route), after 02's II.4 and 11's chapter; weights in the Section 7
restriction (II.114; 31), after 10's II.20–II.21; restriction over a fixed field (II.119;
29), after 17's II.63; Section 10 by logarithmic selection and at a fixed radius
(II.121; 28 and 30), continuing 12's and 07's chapters; repair of respected arrangements
(II.136; 33), after 14's II.44 and 15's chapter; and the odd-order constants (III.66; 29,
then 28), after 04's III.3. Source 32's Sections 2–5 follow 26's Appendix A in
26's chapter (no new guide). Source 28 divides itself into three `\part`s; their
headings are printed, unnumbered, at the head of the sections they introduce.

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
  colouring threshold (10, reproved by 14), collision-to-mode (07, 11, 12);
- added in the fourth write: the arrangement interpolation and cubic cap (04, 14,
  15), Cartesian equality, stability and the joint normal form (14, 15; 15's
  constants weaker), moments without density loss (04, 17), the cube expansion
  through order five (09, 16, 18) and set sharpness (03, 04, 09, 16, 18), the
  active-pattern bound at Proposition 17.7 (04, 16), two-function counting (06,
  20), polynomial partitions (18, 19) and their obstructions (13, 05, 18, 19).
- added in the fifth write: the exponent-five coefficient (21, 23; 23 is the second
  route), the leading degeneracy coefficient and the single-certificate bound (18
  first; 22 with credit; 25 and 27 independently), the case `k = d = 1` (22, 27),
  the prescribed-length upper threshold (13, generalized by 23), the cubic DRC
  certificate and the scalar optimum (03, 24), the fibre extraction and the
  modern-input corollary (10, 24), sampling with an add-one argument (19, 23).
- added in the sixth write: bounds for `c_d^odd` (28, 29, independently; 29 the
  spine) and the count 222 (both); the Proposition 6.1 endpoint (31 sharp, 29 a second
  route); the vertical-fibre restriction and the Reiher–Schoen alternative (10; 31
  with weights); the tree budget and the compatibility inequality (12; 30 again); the
  variance step over every cyclic modulus (26, 32).

## Files

The directory holds 418 files: 41 at the root, 158 in `code/`, 187 in `data/`, 32 in
`figures/`. Of these, 38 were placed with sources 01–05 (besides the base's
`article.tex` and `README.md`, which the first write replaced), 46 with sources
06–10, 39 with sources 11–14, 42 with sources 15–20, 60 with sources 21–27, 61 with
sources 28–33, and 129 with later sources not yet written in (below); `article.pdf`
was added by the first write and rebuilt by the second to sixth.

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

**Source 15, prefix `15-collision-amplification-`** (6 files). At the root, its Lean
integration plan (`integration.md`: proposed interfaces, not compiled code; pinned to
`9ea383e9b`). `code/`: the exact verifier (standard library, fixed seed 20261006) and
the delivered build script. `data/`: the recorded results and log, and
`provenance.json` (pin, five blob ids, literature, a `source_correction` block).

```
15-collision-amplification-integration.md
code/15-collision-amplification-build.sh
code/15-collision-amplification-verify.py
data/15-collision-amplification-provenance.json
data/15-collision-amplification-verification.txt
data/15-collision-amplification-verification_results.json
```

**Source 16, prefix `16-phase-localization-`** (11 files; delivered under `code/`,
`data/`, `figures/`). `code/`: the localization check (NumPy), the partition
certificates and the cube coefficients (standard library), and the figure script
(Matplotlib). `data/`: their recorded outputs, the formula table of the figure
(`localization_constants.csv`, delivered with CRLF and kept byte-for-byte by a
`-text` line in the root `.gitattributes`) and `pdf_review.txt`, a build record
with the SHA-256 of the unshipped PDF. `figures/`: the figure of Section IV.13.

```
code/16-phase-localization-make_figures.py
code/16-phase-localization-verify_cube_coefficients.py
code/16-phase-localization-verify_localization.py
code/16-phase-localization-verify_partitions.py
data/16-phase-localization-cube_results.txt
data/16-phase-localization-localization_constants.csv
data/16-phase-localization-localization_results.json
data/16-phase-localization-partition_results.json
data/16-phase-localization-pdf_review.txt
figures/16-phase-localization-localization_constants.pdf
figures/16-phase-localization-localization_constants.png
```

**Source 17, prefix `17-polynomial-restriction-`** (4 files). `code/`: the audit script
(exact arithmetic, NumPy optional) and the delivered build script. `data/`: the
recorded results and `source_manifest.json` (pin, paths, verification-status flags).

```
code/17-polynomial-restriction-build.sh
code/17-polynomial-restriction-verify.py
data/17-polynomial-restriction-source_manifest.json
data/17-polynomial-restriction-verification_results.json
```

**Source 18, prefix `18-arrangement-degeneracy-`** (6 files). `code/`: the exact
verifier (standard library) and the figure script (Matplotlib). `data/`: the
recorded results and `provenance.json` (pinned blob ids). `figures/`: the
partition-exponent figure of Section V.75.

```
code/18-arrangement-degeneracy-make_partition_figure.py
code/18-arrangement-degeneracy-verify_refinements.py
data/18-arrangement-degeneracy-provenance.json
data/18-arrangement-degeneracy-verification_results.json
figures/18-arrangement-degeneracy-partition_exponents.pdf
figures/18-arrangement-degeneracy-partition_exponents.png
```

**Source 19, prefix `19-shared-interpolation-`** (9 files; delivered under
`verification/`, `provenance/`, `figures/`). `code/`: the sampling and polynomial
verifiers (standard library) and the figure script (Matplotlib, high-precision
decimals). `data/`: their recorded outputs, the 60-digit Poisson constants and the
source audit (`source-audit.json`: blob ids, the ledger counts 98/22 of its pin, the
retrieval method). `figures/`: the sampling figure of Section II.69.

```
code/19-shared-interpolation-make_figures.py
code/19-shared-interpolation-verify_polynomial.py
code/19-shared-interpolation-verify_sampling.py
data/19-shared-interpolation-poisson_constants.json
data/19-shared-interpolation-polynomial_results.json
data/19-shared-interpolation-sampling_results.json
data/19-shared-interpolation-source-audit.json
figures/19-shared-interpolation-sampling_extrema.pdf
figures/19-shared-interpolation-sampling_extrema.png
```

**Source 20, prefix `20-quadratic-counting-`** (6 files). `code/`: the verifier (exact
arithmetic; NumPy for `--gauss`) and the delivered Makefile. `data/`: the recorded
report, a validation summary, the build report (a TeX Live log summary, no paths)
and `source_manifest.json` (blob ids; links on the moving branch `main`).

```
code/20-quadratic-counting-Makefile
code/20-quadratic-counting-verify.py
data/20-quadratic-counting-BUILD_REPORT.txt
data/20-quadratic-counting-source_manifest.json
data/20-quadratic-counting-validation_summary.json
data/20-quadratic-counting-verification_report.json
```

**Source 21, prefix `21-characteristic-five-`** (16 files). `code/`: the order-five
certificate verifier and the profile verifier (standard library), the figure script
(Matplotlib, `decimal`), the delivered Makefile. `data/`: the 34-monomial Fourier
certificate (CSV, CRLF line ends kept by `.gitattributes`), the two verification
logs and the profile results, the coefficient-convergence data, the AI-assisted
review record, `package_validation.json` (SHA-256 of the unshipped `.tex` and PDF)
and `source_manifest.json` (pin and blob ids). `figures/`: the phase-envelope and
convergence figures of Sections III.53 and III.55.

```
code/21-characteristic-five-Makefile
code/21-characteristic-five-make_figures.py
code/21-characteristic-five-verify_order5.py
code/21-characteristic-five-verify_profiles.py
data/21-characteristic-five-coefficient_convergence.csv
data/21-characteristic-five-mathematical_review.txt
data/21-characteristic-five-order5_cube_fourier_certificate.csv
data/21-characteristic-five-order5_verification.txt
data/21-characteristic-five-package_validation.json
data/21-characteristic-five-profile_validation_results.json
data/21-characteristic-five-profile_verification.txt
data/21-characteristic-five-source_manifest.json
figures/21-characteristic-five-coefficient_convergence.pdf
figures/21-characteristic-five-coefficient_convergence.png
figures/21-characteristic-five-phase_envelope.pdf
figures/21-characteristic-five-phase_envelope.png
```

**Source 22, prefix `22-degree-filtrations-`** (10 files). `code/`: four exact
verifiers (standard library) and the delivered Makefile. `data/`: their four
recorded outputs and `SOURCE_LEDGER.json` (pin, paths and SHA-256 of the inspected
files, each of the pinned content plus one appended newline, and claim-status lists).

```
code/22-degree-filtrations-Makefile
code/22-degree-filtrations-verify_certificates.py
code/22-degree-filtrations-verify_norm_obstruction.py
code/22-degree-filtrations-verify_polynomial_patterns.py
code/22-degree-filtrations-verify_two_cubes.py
data/22-degree-filtrations-SOURCE_LEDGER.json
data/22-degree-filtrations-certificate_verification.json
data/22-degree-filtrations-norm_obstruction_verification.json
data/22-degree-filtrations-polynomial_pattern_verification.json
data/22-degree-filtrations-two_cube_verification.json
```

**Source 23, prefix `23-sharp-thresholds-`** (12 files). `code/`: the partition,
fifth-order and Section 16 verifiers (standard library), the figure script (NumPy,
Matplotlib), the delivered Makefile. `data/`: the three recorded outputs,
`source_manifest.json` (pin, blob ids) and `build_validation.json`. `figures/`: the
threshold figure of Section I.38. Its `data/latex_build.log` (a TeX Live log) is
not shipped.

```
code/23-sharp-thresholds-Makefile
code/23-sharp-thresholds-check_fifth.py
code/23-sharp-thresholds-make_figure.py
code/23-sharp-thresholds-verify_prescribed_partitions.py
code/23-sharp-thresholds-verify_section16_gluing.py
data/23-sharp-thresholds-build_validation.json
data/23-sharp-thresholds-fifth_checks.txt
data/23-sharp-thresholds-gluing_checks.json
data/23-sharp-thresholds-partition_checks.json
data/23-sharp-thresholds-source_manifest.json
figures/23-sharp-thresholds-phase_thresholds.pdf
figures/23-sharp-thresholds-phase_thresholds.png
```

**Source 24, prefix `24-section7-compression-`** (4 files). At the root, the
provenance note (pin, blob ids). `code/`: the exact verifier (standard library) and
the delivered build script. `data/`: the recorded results.

```
24-section7-compression-PROVENANCE.md
code/24-section7-compression-build.sh
code/24-section7-compression-verify.py
data/24-section7-compression-verification_results.json
```

**Source 25, prefix `25-codimension-one-`** (7 files). At the root, the source
audit. `code/`: the verifier, the cutoff comparison (standard library) and the
delivered Makefile. `data/`: their recorded outputs and `build_summary.json` (SHA-256
of the unshipped PDF).

```
25-codimension-one-SOURCE_AUDIT.md
code/25-codimension-one-Makefile
code/25-codimension-one-compare_cutoffs.py
code/25-codimension-one-verify.py
data/25-codimension-one-build_summary.json
data/25-codimension-one-cutoff_comparison.json
data/25-codimension-one-verification.json
```

**Source 26, prefix `26-threshold-free-affine-`** (5 files; delivered as
`build.py`, `companion/exact_checks.py`, `tests/…`). At the root, `SOURCES.md` (the
pinned interface and four SHA-256 fingerprints, each of the pinned file plus one
appended newline). `code/`: the exact companion, its regression tests, and the
Linux-only builder with its tests. No recorded output is delivered.

```
26-threshold-free-affine-SOURCES.md
code/26-threshold-free-affine-build.py
code/26-threshold-free-affine-exact_checks.py
code/26-threshold-free-affine-test_build.py
code/26-threshold-free-affine-test_companion.py
```

**Source 27, prefix `27-degeneracy-second-order-`** (6 files). At the root, the
formalization plan and the source audit (blob ids). `code/`: the verifier (standard
library; NumPy for `--subset`) and the delivered Makefile. `data/`: the exact
rational certificate (delivered as `code/exact_certificate.json`) and the
verification report (delivered at the package root).

```
27-degeneracy-second-order-FORMALIZATION.md
27-degeneracy-second-order-SOURCE_AUDIT.md
code/27-degeneracy-second-order-Makefile
code/27-degeneracy-second-order-verify.py
data/27-degeneracy-second-order-exact_certificate.json
data/27-degeneracy-second-order-verification.json
```

**Source 28, prefix `28-log-selection-`** (11 files). `code/`: the selection and
`U⁴` verifiers (standard library), the figure script (Matplotlib) and the delivered
Makefile. `data/`: their recorded outputs, `verification_scope.txt`,
`source_provenance.json` (pin and blob ids; its pin of source 07 has 39 hexadecimal
digits, a `6` missing — dated note in the article) and `build_summary.txt` (SHA-256
of the unshipped `.tex` and PDF). `figures/`: the bound comparison of II.127 and the
two-harmonic ratio of III.70.

```
code/28-log-selection-Makefile
code/28-log-selection-make_figures.py
code/28-log-selection-verify_selection.py
code/28-log-selection-verify_u4.py
data/28-log-selection-build_summary.txt
data/28-log-selection-selection_checks.json
data/28-log-selection-source_provenance.json
data/28-log-selection-u4_exact_results.json
data/28-log-selection-verification_scope.txt
figures/28-log-selection-local_bounds.pdf
figures/28-log-selection-two_harmonic_ratio.pdf
```

**Source 29, prefix `29-moment-stability-`** (15 files). `code/`: four verifiers
(the joint-rigidity one needs NumPy), the figure script (NumPy, Matplotlib) and the
delivered Makefile. `data/`: their four recorded outputs, the requirements,
`build_validation.json` (SHA-256 of the unshipped `.tex` and PDF) and
`source_audit.json` (SHA-256, bytes and blobs of the eighteen archives 06–23 it read).
`figures/`: the norm-bound figure of III.69 (PDF and PNG).

```
code/29-moment-stability-Makefile
code/29-moment-stability-make_figures.py
code/29-moment-stability-verify_coefficients.py
code/29-moment-stability-verify_joint_rigidity.py
code/29-moment-stability-verify_moments.py
code/29-moment-stability-verify_rank_restriction.py
data/29-moment-stability-build_validation.json
data/29-moment-stability-coefficients.json
data/29-moment-stability-joint_verification.json
data/29-moment-stability-moment_verification.json
data/29-moment-stability-rank_verification.json
data/29-moment-stability-requirements.txt
data/29-moment-stability-source_audit.json
figures/29-moment-stability-norm_bounds.pdf
figures/29-moment-stability-norm_bounds.png
```

**Source 30, prefix `30-fixed-radius-bohr-`** (7 files). At the root, its
formalization plan and source audit (blob ids; it records a moving-branch read of a
README). `code/`: the exact verifier (standard library) and the delivered Makefile.
`data/`: the recorded results, delivered under `results/` (`verification.json`, the
verifier's stdout `check_stdout.txt`, `build_validation.json` with a generic sandbox
path).

```
30-fixed-radius-bohr-FORMALIZATION.md
30-fixed-radius-bohr-SOURCE_AUDIT.md
code/30-fixed-radius-bohr-Makefile
code/30-fixed-radius-bohr-verify.py
data/30-fixed-radius-bohr-build_validation.json
data/30-fixed-radius-bohr-check_stdout.txt
data/30-fixed-radius-bohr-verification.json
```

**Source 31, prefix `31-weighted-spectra-`** (10 files). `code/`: three verifiers
(the spectral one needs NumPy) and the delivered Makefile. `data/`: their recorded
outputs, the requirements, `SOURCE_LEDGER.json` (pin, blobs, SHA-256 of its four
inputs) and `VALIDATION.json` (both delivered at the package root).

```
code/31-weighted-spectra-Makefile
code/31-weighted-spectra-verify_spectral_rigidity.py
code/31-weighted-spectra-verify_weight_defects.py
code/31-weighted-spectra-verify_weighted_extraction.py
data/31-weighted-spectra-SOURCE_LEDGER.json
data/31-weighted-spectra-VALIDATION.json
data/31-weighted-spectra-requirements.txt
data/31-weighted-spectra-spectral_rigidity_checks.json
data/31-weighted-spectra-weight_defect_verification.json
data/31-weighted-spectra-weighted_extraction_results.json
```

**Source 32, prefix `32-quadratic-increments-`** (5 files; delivered as
`build.py`, `companion/exact_checks.py`, `tests/…`). At the root, `SOURCES.md` (the
pinned interface and SHA-256 fingerprints, each of the pinned file plus one appended
newline, as for 26). `code/`: the exact companion, its tests, and the Linux-only
builder with its test. No recorded output is delivered.

```
32-quadratic-increments-SOURCES.md
code/32-quadratic-increments-build.py
code/32-quadratic-increments-exact_checks.py
code/32-quadratic-increments-test_build.py
code/32-quadratic-increments-test_companion.py
```

**Source 33, prefix `33-arrangement-stability-`** (13 files). At the root, its
formalization plan and source audit (pin, blobs). `code/`: the verifier, the erasure
verifier, their two modules (standard library) and the delivered Makefile. `data/`:
the recorded verification and erasure outputs, the example input and its result,
the requirements and `build_validation.json`.

```
33-arrangement-stability-FORMALIZATION.md
33-arrangement-stability-SOURCE_AUDIT.md
code/33-arrangement-stability-Makefile
code/33-arrangement-stability-arrangements.py
code/33-arrangement-stability-polynomial_checks.py
code/33-arrangement-stability-verify.py
code/33-arrangement-stability-verify_erasures.py
data/33-arrangement-stability-build_validation.json
data/33-arrangement-stability-erasure_verification.json
data/33-arrangement-stability-example.json
data/33-arrangement-stability-example_result.json
data/33-arrangement-stability-requirements.txt
data/33-arrangement-stability-verification.json
```

**Sources 34–39, placed by `bf2fe146d`, write pending** (77 files; not used in the
article):

```
35-graded-selection-SOURCE_AUDIT.txt
36-symmetry-certification-FORMALIZATION_PLAN.md
36-symmetry-certification-SOURCE_AUDIT.md
37-missing-intervals-INTEGRATION.md
37-missing-intervals-SOURCE_AUDIT.md
39-shared-anchor-FORMALIZATION_PLAN.md
39-shared-anchor-SOURCE_AUDIT.md
code/34-torsion-gaps-Makefile
code/34-torsion-gaps-verify_determinant_gadgets.py
code/34-torsion-gaps-verify_odd_fourth_gap.py
code/34-torsion-gaps-verify_torsion.py
code/35-graded-selection-Makefile
code/35-graded-selection-verify_all.py
code/35-graded-selection-verify_graded_selection.py
code/35-graded-selection-verify_norm_gap.py
code/35-graded-selection-verify_polynomial_obstruction.py
code/36-symmetry-certification-Makefile
code/36-symmetry-certification-verify.py
code/37-missing-intervals-Makefile
code/37-missing-intervals-verify.py
code/38-quotients-Makefile
code/38-quotients-make_figures.py
code/38-quotients-run_checks.py
code/38-quotients-verify_odd_cube_expansion.py
code/38-quotients-verify_odd_rigidity.py
code/38-quotients-verify_quotient.py
code/38-quotients-verify_six_ap_defect.py
code/38-quotients-verify_twelfth_order.py
code/39-shared-anchor-Makefile
code/39-shared-anchor-anchor_selection.py
code/39-shared-anchor-poisson_constants.py
code/39-shared-anchor-verify.py
code/39-shared-anchor-verify_balanced.py
data/34-torsion-gaps-build_verification.json
data/34-torsion-gaps-determinant_gadget_verification.json
data/34-torsion-gaps-no_seven_vertex_torsion_mod_11.json
data/34-torsion-gaps-no_seven_vertex_torsion_mod_13.json
data/34-torsion-gaps-odd_fourth_gap_certificates.json
data/34-torsion-gaps-requirements.txt
data/34-torsion-gaps-small_prime_matrices.json
data/34-torsion-gaps-source_ledger.json
data/34-torsion-gaps-torsion_verification.json
data/35-graded-selection-README.txt
data/35-graded-selection-graded_selection_checks.json
data/35-graded-selection-norm_gap_checks.json
data/35-graded-selection-polynomial_obstruction_results.json
data/36-symmetry-certification-claims.json
data/36-symmetry-certification-requirements.txt
data/36-symmetry-certification-results.json
data/37-missing-intervals-requirements.txt
data/37-missing-intervals-verification_results.json
data/37-missing-intervals-verification_run.txt
data/38-quotients-SOURCE_LEDGER.json
data/38-quotients-VALIDATION.json
data/38-quotients-environment.json
data/38-quotients-figure_numerics.json
data/38-quotients-five_point_coefficient_convergence.csv
data/38-quotients-odd_cube_expansion_checks.json
data/38-quotients-odd_rigidity_checks.json
data/38-quotients-quotient_checks.json
data/38-quotients-qutrit_coefficient_convergence.csv
data/38-quotients-requirements.txt
data/38-quotients-six_ap_defect_checks.json
data/38-quotients-twelfth_order_checks.json
data/38-quotients-verification_run.json
data/38-quotients-verify_odd_cube_expansion_run.txt
data/38-quotients-verify_odd_rigidity_run.txt
data/38-quotients-verify_quotient_run.txt
data/38-quotients-verify_six_ap_defect_run.txt
data/38-quotients-verify_twelfth_order_run.txt
data/39-shared-anchor-balanced_verification.json
data/39-shared-anchor-build_validation.json
data/39-shared-anchor-exact_profiles.csv
data/39-shared-anchor-poisson_constants.csv
data/39-shared-anchor-verification.json
figures/38-quotients-asymptotic_coefficients.pdf
figures/38-quotients-asymptotic_coefficients.png
```

**Sources 40–46, placed by `2dfe46f44`, write pending** (52 files; not used in the
article):

```
40-fejer-selection-PROOF_AUDIT.md
41-all-degree-increments-SOURCES.md
42-quadratic-scale-SOURCES.md
43-boolean-phase-FORMALIZATION.md
44-grid-core-FORMALIZATION.md
44-grid-core-SOURCE_AUDIT.md
45-rigidity-gaps-review_applications.md
45-rigidity-gaps-review_cosets.md
45-rigidity-gaps-review_energy.md
45-rigidity-gaps-review_integration.md
45-rigidity-gaps-review_research.md
45-rigidity-gaps-review_u4.md
46-polarization-barriers-FORMALIZATION.md
46-polarization-barriers-SOURCE_AUDIT.md
code/40-fejer-selection-Makefile
code/40-fejer-selection-verify_fejer_selection.py
code/41-all-degree-increments-build.py
code/41-all-degree-increments-exact_checks.py
code/41-all-degree-increments-test_build.py
code/41-all-degree-increments-test_companion.py
code/42-quadratic-scale-build.py
code/42-quadratic-scale-exact_checks.py
code/42-quadratic-scale-test_build.py
code/42-quadratic-scale-test_companion.py
code/43-boolean-phase-Makefile
code/43-boolean-phase-verify.py
code/44-grid-core-Makefile
code/44-grid-core-verify.py
code/45-rigidity-gaps-Makefile
code/45-rigidity-gaps-verify_all.py
code/45-rigidity-gaps-verify_cosets.py
code/45-rigidity-gaps-verify_energy.py
code/45-rigidity-gaps-verify_u4.py
code/46-polarization-barriers-Makefile
code/46-polarization-barriers-verify.py
data/40-fejer-selection-verification-results.json
data/43-boolean-phase-build_report.json
data/43-boolean-phase-source_audit.json
data/43-boolean-phase-verification.json
data/44-grid-core-grid_certificate.json
data/44-grid-core-normals_d2.json
data/44-grid-core-normals_d3.json
data/44-grid-core-normals_d4.json
data/44-grid-core-run_output.txt
data/44-grid-core-verification.json
data/45-rigidity-gaps-build_report.json
data/45-rigidity-gaps-coset_checks.json
data/45-rigidity-gaps-energy_checks.json
data/45-rigidity-gaps-source_manifest.json
data/45-rigidity-gaps-u4_certificate.json
data/45-rigidity-gaps-verification_run.txt
data/46-polarization-barriers-validation.json
```

**Not shipped**, all retrievable from the arrival commits (`66f24b0d0` for 01–05,
`62e21161f` for 06–10, `08ab4187e` for 11–13, `d179062cc` for 14, and those named
above for 15–33):
- the thirty-three PDFs;
- the manuscripts of sources 01, 02, 03, 05 and 06–33, which are printed in the
  article;
- the delivery READMEs of 01, 02, 03, 05 and 06–33 (their limitations are carried
  below);
- 23's `data/latex_build.log` (a TeX Live build log);
- 33's `data/verification.log` (its verifier's stdout, ending with a sandbox path) and
  `data/erasure_verification.log` (a byte copy of its erasure JSON), both matched by
  the repository's ignore rules;
- the checksum manifests of 04 (`SHA256SUMS.txt`, 13/13), 12 (`SHA256SUMS.txt`,
  11/11), 14 (`SHA256SUMS`, 13/13), 16 (`SHA256SUMS.txt`, 14/14), 18 (9/9), 19
  (12/12), 20 (9/9), 22 (`SHA256SUMS`, 13/13), 23 (`SHA256SUMS`, 16/16), 26
  (`MANIFEST.sha256`, 8/8), 29 (`SHA256SUMS.txt`, 18/18), 31 (`SHA256SUMS`, 13/13), 32
  (`MANIFEST.sha256`, 8/8) and 33 (`manifest.json`, a pure hash list, 18/18), all
  verified at intake (repository policy drops checksum manifests).

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
printed number. The fourth write added the 540 delivered labels of 15–20 (15: 93, 16:
107, 17: 71, 18: 92, 19: 97, 20: 80), a label on each of their 76 delivered sections,
the five chapter guides (`gsr:en:sec:collision`, `gsr:en:sec:restriction`,
`gsr:en:sec:sections1516`, `gsr:cc:sec:quadratic`, `gsr:fp:sec:windows`) and 17 item
labels in Part V: **2,061 labels**, all distinct. A comparison of the `.aux` with a
build of `b16ce380d` found every one of its 1,423 labels with the same printed
number. Source 15 uses the sub-prefixes `gsr:en:15:` and `gsr:fz:15:`; 16 uses
`gsr:dt:16:`, `gsr:cc:16:`, `gsr:fp:16:` and `gsr:fz:16:`, so its `cub:` labels do not
meet 04's. The fifth write added the 511 delivered labels of 21–27 (21: 68, 22:
63, 23: 72, 24: 83, 25: 67, 26: 42, 27: 116), a label on each of their 85 delivered
sections, the five chapter guides (`gsr:dt:sec:cor58`, `gsr:en:sec:section7`,
`gsr:en:sec:degeneracy`, `gsr:cc:sec:charfive`, `gsr:cc:sec:colourings`), four labels
on statements delivered without one (`gsr:en:22:thm:twocube`,
`gsr:en:22:cor:secondupper`, `gsr:en:22:cor:sharpscale`, `gsr:cc:23:prop:indicator`)
and 8 item labels in Part V: **2,674 labels**, all distinct. A comparison of the
`.aux` with a build of `eae64ceca` found every one of its 2,061 labels with the same
printed number, and a comparison with separate builds of the seven delivered `.tex`
files found every statement and equation index of 21–27 unchanged. 27's label
`sec:d2` (its Section 7) has the form of this report's section labels and is
`gsr:en:27:sec:dtwo`. 22 uses `gsr:en:22:` and `gsr:cc:22:`; 23 uses `gsr:dt:23:`,
`gsr:cc:23:` and `gsr:en:23:`. The sixth write added the 442 delivered labels of
28–33 (28: 100, 29: 67, 30: 57, 31: 80, 32: 45, 33: 93), a label on each of their 68
delivered sections, the six chapter guides (`gsr:en:sec:endpoint`,
`gsr:en:sec:weighted7`, `gsr:en:sec:fixedfield`, `gsr:en:sec:section10`,
`gsr:en:sec:arrangements`, `gsr:cc:sec:oddconstant`) and 4 item labels in Part V:
**3,194 labels**, all distinct. A comparison of the `.aux` with a build of
`4b7266a65` found every one of its 2,674 labels with the same printed number, and a
comparison with separate builds of the six delivered `.tex` files found every
statement and equation index of 28–33 unchanged (the consecutively numbered
equations of 30 and 32 apart). 28 uses `gsr:en:28:`, `gsr:cc:28:` and `gsr:fz:28:`;
29 uses `gsr:cc:29:` and `gsr:en:29:`.

**Numbering.** Sections restart in each Part and carry its numeral (I.9; F.1–F.38
in the front matter). Statements and equations are numbered within sections. A
delivered statement or equation `k.j` keeps its index `j`; the exceptions are the
equations of sources 02, 03, 06, 11, 12, 13, 26 (omitted from this list at the fifth
write), 30 and 32, which numbered them through the whole manuscript, and the appendices, which now carry Part numbers. Tables and figures
of sources 06–10 are numbered within their sections (Figure IV.9.1), so that the
global table and figure numbers of 01–05 do not move; the write's remark on the
false quartic bound is Remark W1; the third write's remarks have their own counter and
are W2–W4 (the fourth, fifth and sixth writes needed none). Source 16 numbers its equations by
explicit tags `(k.j)`, kept as delivered; source 20's Questions, numbered on their
own counter there, are numbered within their section here and keep their indices. So are 25's Questions 1–8; 22's and 23's explicit equation tags ((D1.1)–(D1.7), (F1)–(F13)) are kept. So are 28's Research questions 1–15, 30's Questions 1–12 and 33's Research questions 1–12. Source 04's tags (M1)–(M7), (R1)–(R32),
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
- **Sources 15–20**: 15's `C = R₁` is a collision count, not 14's coset, and its `χ`
  a normalized collision count, not a character; 18's `C_d` (degeneracy), 19's `C_d`
  (Poisson constant) and 01's and 06's `C_k` (carry counts) differ; 16's `ℬ_k` is a
  partition quotient, 20's `B_k(δ)` is at most `√δ` times 06's `B_k(δ)`; 17's `T₁₆`
  is 04's `T₈`; 18's `Q_d` counts five-circuits (= 09's `Q_d`); 16's `q` counts affine
  frequencies, not 04's `⌈h/k⌉`; 17's "L-degenerate" tuples are not 18's degenerate
  arrangements. Six macros renamed (16's `\conj`, `\BB`; 17's `\code`; 18's `\T`;
  19's `\commit`; 20's `\U`), printing as delivered; 19's `question` is "Research
  question", 20's "Question".
- **Sources 21–27**: one number under four names — 18's `C_d`, 22's `C_d`, 25's
  `H_d`, 27's `L_d` (`C₈ = 2,585,444`; 27's `R_{2,2} = 2,585,419` is a different
  number); 21's and 23's `C₅ = 2^{3/4}/3` (14's), 21's `C₆, C₇` (vertex sums) and
  23's `C₆` (one of three forms) differ; 23's `κ = 2^{1/4}/6` is 21's `β₅`; 22's `𝖩`
  (balanced classes) is not 18's `J_{k,d}`; 24's `Q_k` is 10's `h_k`, its `κ` is 10's
  `γ`; 25's `n = 2d2^k` is 27's `m`; 22's `q` is `2d` in Sections 2–5 and the field
  size in 6–10. Three macros renamed (23's `\snapshot`, 24's `\code`, 25's `\card`),
  printing as delivered; 22's and 27's `question` is "Research question", 21's, 24's
  and 25's "Question"; 27's `\cref` written out as its own `\crefname` settings print
  them.
- **Sources 28–33**: 28's and 29's `c_d^odd` are 03's (= 08's `κ_d^odd`); 29's `C_m`
  (a moment coefficient) and `B_d` (an upper bound for `c_d^odd`) are not 18's `C_d`,
  `B_d`; 31's `κ = ‖f‖⁸_{U³}/‖f‖⁸₂` and `δ = 1 − κ`, 30's `κ` (12's translation loss)
  and 33's `δ` (a distance) differ; 29's and 31's `T_φ` are one score (31 divides by
  `m²`); 30's `b_B(d)` counts points where 12's is a fraction; 33's `s` is twice
  Gowers's arrangement order (`s = 16`). Eight macros renamed (28's `\T` as `\Tcirc`,
  the `\pin` of 28, 30, 33, 29's `\code`, 30's `\defect`, 31's `\Energy` and `\ip`,
  33's `\V`), printing as delivered; 28's, 31's and 33's `question` is "Research
  question", 29's and 30's "Question"; 28's `\cref` written out as `cleveref` prints
  it there (lowercase names).

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

**Sources 15–20 (fourth write).**
- 15: `R₂^{d−1} ≤ C^{d−2}R_d` and the cubic cap (as 04, 14); the collision-
  parametrized product step `a₂ ≥ γ^{8·2^k}χ⁴` and the coupled
  `a_d ≥ γ^{8(d−1)2^k}χ^{3d−2}` (new); Cartesian equality and labels (as 14),
  stability with `18ε` and spectral stability (weaker than 14), band, profile,
  joint normal form (as 14), dichotomy, vertex weights.
- 16: Proposition 17.7 with `(4/(3(k+2)))^{k+2}` under exactly its hypotheses, cells
  between `m/(3k)` and `3km`; width limit `(2/(k+2))^{k+2}`; local-scale ceiling
  `2^{k+1}/(k+2)!`; polarization, the factorial criterion and the `𝔽_p` test; the
  short-cell variant (as 04); own-step partitions conditional on Lau, obstruction
  `γ ≤ 1/(3q+1)`; the cube expansion (as 09), `2^{−1/2}` without three-torsion.
- 17: restriction over `𝔽_p` with `α^mη^{m−1}/(2(m+2)^m)` above
  `N ≥ 2L^m(2L−1)^{m−1}β^{−(m−1)}`, weights and vector-valued maps; moments
  `γ^{r−1}` (as 04); the scalar-certificate optimum; fixed characteristic with a
  rank gap.
- 18: degenerate density `(k+C_d)/p + O(p⁻²)` for `d ≥ 2`, `p > 2d`, sharp first
  order; Lemma 15.5 with `λp ≥ k + 2,585,445`; the expansion through order five on
  every group (as 09, 16); polynomial partitions `1/(126q²+129q+2)`, `1/(99q+98)`;
  the volume obstruction.
- 19: common sampling with lost mass `≤ qd/(r+1)`; exact minimax; `C₂ = φ³e^{−φ}`;
  shared-slice lifting with `Σ e_j(M₁,…,M_r)` candidates; a local replacement in
  Lemma 16.10 under an inherited-coordinate hypothesis; degree-profile partitions
  and the obstruction `(S+1)a + Db ≤ 1`.
- 20: two marked functions with an `L²` gain; the sharp finite-index comparison;
  quadratic counting with `B_k(δ)`; the sharp pair correction `√(m−1)`;
  supersaturation; exponent 2 sharp at density near 1/2 on `𝔽₂₉^{2m}`.

**Sources 21–27 (fifth write).**
- 21: `Q₃(δ+f) ≤ δ⁸ + 6√2δ⁴u⁴ + C₅δ²u⁶ + Cu⁸`, `C₅ = 2^{3/4}/3`, `u ≤ cδ`, absolute
  constants, sharp on every exponent-five group; the phase envelope
  `C₅(cos θ)₊²/(1+cos²φ)`; rigidity; `20/9` next on `ℤ/5ℤ`; indicator sharpness
  through `u⁸`; a projection consequence of cube Cauchy–Schwarz.
- 22: the degree-stratified finite degeneracy bound (`𝖩_{k,2} = 30k⁴+204k³+111k²+114k`);
  `δ_{k,1}(p) = (k²+3k)/p + O(p⁻²)`, exactly `4/p − 3/p²` for `k = 1`; the exact
  fixed-centre pattern minimum `q^{max(n−B,0)}`, symmetric and monochromatic budgets
  in every degree, the quadratic classification, no additive extension, norm-line
  excess.
- 23: the semigroup thresholds `C ∏Mᵢ ≤ T ≤ CB`; `L^{q+2}/∏εᵢ (1+o(1))` for
  `{L, L+1}`; optimality of `(q+2)a + qb = 1`; exact packing; almost-partitions; the
  exponent-five theorem again (second route); the common base partition with width
  `(m/3)^A`, exact transport and affine gluing (conditional on slice covers).
- 24: Lemma 7.4 with `7δ³n/(3√6)` and the scalar optimum (as 03);
  `(κ/8, 2¹⁵κ⁻⁵, 2¹⁷κ⁻⁶)`; `|B|/(kQ_k)` (as 10, weaker prefactor); `|B|/p^{⌈log_p Q_k⌉}`
  for `𝔽_p^d` (new); `2⁻⁽³⁴ᵏ⁺²⁰⁾γ¹²ᵏ⁺⁷/k` (weaker than 10).
- 25: `L q^{D−1} − C(L,2)q^{D−2} ≤ Z ≤ L q^{D−1} + U q^{D−2}`, `L = k + H_d`, over fields
  of characteristic `> 2d` (first order as 18); codimension-one components; the
  residual lower bound; selection for every `d ≥ 2`.
- 26: gain `α/3` at length `min{(r(1−δ)/(128μ))^{1/3}, (N/8)^{1/3}}`, or
  `(N/M)^{1/3}/8`; the square-root alternative; the integer-box almost-cover and the
  obstruction to exact long partitions.
- 27: first order in every characteristic; the `S_{k,d}` core directions and a cubic
  remainder; `Δ_{k,2}(q) = (k+4)/q + (k²+21k−6)/(2q²) + O(q⁻³)`; the exact
  eight-vertex count (finite rational certificate); `Δ_{1,1}(q) = 4/q − 3/q²` (as 22).

**Sources 28–33 (sixth write).**
- 28: a Section 10 local model from the original-domain spectrum retaining `αp(α)/20`,
  `p(α) = (log 2)²/(log(32/α) log(32/α²))`, with `|Γ| ≤ 2³⁴(1+α)/((log 2)α³)`, radius
  `Ω(α⁵)`, input defect `2⁻²¹`, order seven; `c₄^odd ≥ 0.5587294`; no single-cosine
  extremizer for any `d ≥ 4`; the weaker universal `c_d^odd ≤ √(160/323)`.
- 29: `‖f‖^{2^d}_{U^d} ≥ 2^{−m}C(2m,m)‖f‖^{2^d}_{U²}`, `m = 2^{d−2}`; `c₄^odd ≤ (8/35)^{1/4}`,
  `c_d^odd ≤ B_d ↓ 1/2`, `c_d^odd ≥ 1/3`; the torsion profile `K_m(τ)`; the joint
  endpoint with `20ε`, `22ε`, soft and mixed selectors; fixed-field restriction with
  threshold `8qS/(αη)`, then none.
- 30: `2m·b_B(d) ≤ |B(3ρ/2)| − |B| ≤ (3^r−1)|B|` for widths `≤ 1/4`, both parts sharp;
  radius `ρ/(8(3^r−1))` with Corollary 10.11's margins; `5/14` at Lemma 10.12; the
  rank obstruction `3^s/2 ≤ 𝓛_{2s+1} ≤ 3^{2s+1} − 1`, realized in cyclic groups of
  composite order.
- 31: `1 − F ≤ (1 − √((1+√(1−4δ))/2))/2` for `δ < 1/120`, optimal; selected graphs:
  errors `≤ ε`, infidelity `≤ (1−√(1−2ε))/2`; weighted restriction `1/(kC^{2k+1})`;
  `2⁻³⁶³c¹⁷¹` at order eight; the correlation-preserving restriction on `𝔽_p`; the
  weight-defect inequality and two counterexamples to `L¹` stability.
- 32: gain `α/3` at length `max{1, (N/M)^{1/39}/17}`; `p ≤ 2¹⁰R⁵` with `‖θp²‖ < 1/R`;
  lossless quadratic partitions above `2¹¹⁶L³⁸`.
- 33: `δ ≤ R_s(ε_s) = ε_s/s + 2(s−1)ε_s²/s² + O(ε_s³)` for `ε_s ≤ 1/(240(s−1))`, both
  coefficients sharp; `ε₄ ≥ 4δ − 24δ² + 32δ³`, sharp; `max{θ⁷, 4θ−3}N³²`; erasures;
  an exact cyclic decoder.

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

**Proved in the fourth write** (dated notes, each with its proof):
15. **16 implies the formal `proposition_17_7`**: identical hypotheses and output,
    and `(4/(3(k+2)))^{k+2} > 2^{−2(k+1)³}` for every `k ≥ 1`
    (`log₂(3(k+2)/4) < k+2`, so the loss is below `(k+2)² ≤ 2(k+1)³`).
16. **04's Corollary 8.8 in the normalization of the formal statement**:
    `c_k(m/(q+1))^{k+2}`, i.e. 91.07 bits at `k = 8` uniformly over admissible `m`
    (worst `m = 25`), 81.66 as `m → ∞`; from Theorem 8.7's first inequality 89.19
    and 80.49. The 121.66 bits compared earlier are in 04's own normalization;
    the ordering is unchanged. Exact arithmetic over odd `3k < m < 20,000`; beyond, `m/(q+1) ≥ 2km/(m+4k−1)`.
17. **17 implies the prime case of `lemma_9_3` and `corollary_9_4`** with
    `N₀ = ⌈2L^{16}(2L−1)^{15}β^{−15}⌉`, `L = ⌈17/(αη)⌉`; its constant beats 04's
    exactly for `d ≤ 97` (`(d+1)² < 100d`); at the Corollary 9.4 point
    `γ = η = β = 1/2`: `2^{−194.72}` above `N ≥ 2^{405.71}` (17), `2^{−222}` above
    `2^{231}` (04), `2^{−8,388,608}` (formal).
18. **18's finite degeneracy bound is below the formal `lemma_15_4` bound** for
    `d ≥ 2`, `p > 2d` (`J_{k,d} < 3^{2d2^k}/2`, `C_d < 3^{2d}/2`; checked exactly for
    `k ≤ 4`, `d ≤ 5`, `p < 400`).
19. **15's coupled exponents beat `lemma_14_8` and 04's (A12)** for every `k ≥ 1`
    (`56·2^k ≤ 40k4^k`); against the unweakened exponent the gain is
    `(β^{4^k}γ^{2k4^k})^{−6}`.
20. **14's sharp stability implies 15's three constants**: `τ(ε) ≤ 1.0102 ε` on
    `[0, 1/100]`; `τ(1/a − 1/a²)·a = 1`, so the leading constant of 15's first
    question is 1.
21. **20's coefficient is strictly below 06's**: `B_k^{(20)} ≤ √δ B_k^{(06)}`, strict
    for every `k ≥ 3`, `0 < δ < 1` (the term `j = k−1` carries `σ < √δ`); ratios
    0.8536 (`k = 4`, `δ = 1/2`) and 0.8367 (`k = 3`, `δ = 0.3`).
22. Checked: 18's prescribed-length exponent against 19's at the same input (269
    against 314 at `q = 1`, `κ = 11`); 18's `Q_d`, `S_d` equal `2^d S(d+1,4)`,
    `2^d S(d+1,5)`; `C₂ = φ³e^{−φ}` and the worked example of 19 (199 against 1000
    anchors). Script and output: not shipped (the write's scratch record).

**Proved or checked in the fifth write** (dated notes, each with its argument):
23. **The degree-one formal `corollary_5_8` holds trivially when `N/M ≤ 2^48`** (a
    singleton of `A`: density 1 ≥ `δ + α/16` since `α ≤ 2δ(1−δ)`, and
    `(N/M)^{1/16}/8 ≤ 1`), and 26's Corollary 2.3 implies that instance in general
    (`M ≤ N`, `(N/M)^{1/3} ≥ (N/M)^{1/16}`); 26's bound exceeds 1 only for
    `N/M > 512`.
24. **27's second coefficient** `S_{k,2} − C(k,2) − 4k − 3 = (k²+21k−6)/2`
    (`S_{k,2} = k² + 14k`, `b_{2,2,p} = 3`): 8, 20, 33, 47 for `k = 1, …, 4`.
25. **No gain at Lemma 15.5 at leading order for 22**: its `𝒜_{k,8}(λ)` has 18's
    leading term `(k+C₈)/λ`, its `𝒫_{k,8}(λ) ≥ (k+1)(k+C₈)/λ`.
26. **22, 25 and 27 lie below the formal `lemma_15_4`** in their ranges (22 via 18's
    bound; 25: `L + U/q < k3^n`; 27: `A + S/q + R/q² < k3^m`).
27. **24 against 10**: weaker by exactly `2^{10k+6}` (86 bits at `k = 8`); 24's `C₃`
    is 03's `κ*²` and `C₂` is 03's `2h − h²`; on `𝔽_p^d` 24's extraction beats 10's
    torsion budget whenever `Q_k ≤ p^{d−1}`, `k ≥ 2` (a multiple of `p` costs `p^d − 1`
    in 10's budget, so its retention is below `p^{1−d}`).
28. **25's power-form exponent**: `K_n/E_k → log 2` against the formal
    `arrangementSelectionExponent` (0.693147 already at `k = 1, …, 4`).
29. **23's sampling lemma against 19's theorem**: the same add-one argument; a
    different loss (sampled points retained, hence the factor `1 − r/n`); its stated
    sample size is one more than its own inequality and 19's need.
30. Checked: 21's `C₅` optimization and the identities between 21's and 23's rigidity
    statements (`2^{−3/4}κ² = C₅/24`); `L_{3,5} = 57`; `R_{2,2} = H₈ − 25`; 23's
    `t`-interval and the conductor `(v−1)(v−2)`; 26's remark (`11/108` against
    `1/36`). Script and output: not shipped (the write's scratch record).

**Proved or checked in the sixth write** (dated notes, each with its argument):
31. **The intake's certificate for `c₄^odd`, recomputed exactly**: on `ℤ/7`,
    `f = (181, 1000, −780, −932, 989, 540, −998)` has `‖f‖^{16}_{U⁴}/‖f‖^{16}_{U²} =
    10.2579317…` (exact integers), so `c₄^odd ≥ 0.5587725` (28's witness: 10.2611003…,
    0.5587294). A review result credited to the intake, not to a source.
32. **29's `35/8` is the best coefficient among 01–33**, not the best known (34:
    `81/16`, 35: `5`, 45: `4795/832`, placed); 28's universal bound is `(323/160)² =
    4.0754…`.
33. **31 supersedes 29's endpoint constants** under the same normalization
    (`T_φ(f)/m²`): graph error `ε` against `20ε`, squared distance
    `ε/2 + O(ε²)` against `22ε`, on the larger range `ε ≤ 1/400`.
34. **31 against 10**: 10's progression `⌊(p−2)/(k(h−1))⌋` is never shorter than 31's
    `⌊p/(kq)⌋` (`kqL ≤ p`, `L ≥ 1` give `k(q−1)L ≤ p − 2`); `2⁻²⁰⁹γ¹⁰³` beats
    `2⁻³⁶³c¹⁷¹`; the Reiher–Schoen formulas coincide (`18k+9 = 9(2k+1)`,
    `66k+33 = 33(2k+1)`).
35. **30 against 12**: 30's budget `4η + 3κ < 1` (order two) implies 12's
    `3ε + 2κ < 1`; composing 30's escape inequality with 12's sharp theorem gives the
    fixed radius `ρ/(2m)`, `m = ⌊8(3^r−1)/5⌋ + 1`, larger than 30's
    `ρ/(6·3^r − 4)` by a factor `1.75` (`r = 1`), `1.92` (`r = 2`), `→ 1.875`.
36. **32 implies the degree-two instance of `corollary_5_8`** at every scale
    (`8^{25/39} > 17/8`, `α/3 ≥ α/16`; `polynomialPartitionConstant 2 = 2048`), and with
    26 the instances `k ≤ 2`; it does not give the `k = 1` length.
37. **33's linear branch** `4θ − 3 > θ⁷` exactly for `θ ∈ (0.8045539…, 1)`.
38. Checked: 29's table of `B_d`, its interval model (`n(n²+n+1)/(3(n+1)³) → 1/3`) and
    the cube coefficient `100(8/35)^{1/4} = 69.14`; 33's bracket `23/512 ≤ c₁₆ ≤ 15/128`;
    28's retained fraction against `α⁶/20000` (`1.08·10⁻⁴` against `1.07·10⁻⁹` at
    `α = 1/6`). Script and output: not shipped (the write's scratch record).

Recomputed independently at the second write: the `ℤ/11` counterexample (exact
enumeration of all `11⁴` frequency choices, and direct summation over all cubes);
09's determinant-5 configuration (`det B = −5`, `M_S r = (10,5,5,5,5,5)`, Smith form
`1,1,1,1,1,5`, moment 4 on `ℤ/5`); 10's `2⁻²⁰⁹γ¹⁰³`; 06's and 04's coefficients at
`k = 8` (`2⁻²¹²·⁷⁰` and `2⁻¹²¹·⁶⁶`); 07's endpoint `331257600001/335923200000 < 1`;
08's and 09's order-two closed forms (identical); 09's Stirling coefficients
against 08's and 03's counts (`d = 2, …, 7`). Script and output:
not shipped (the write's scratch record).

## What the report does not claim

No source claims a new bound for `r_k(N)`. Sources 01–15, 17–21, 23 and 24 cite
Leng–Sah–Sawhney's `r_k(N) ≪ N exp(−(log log N)^{c_k})`, `k ≥ 5`, as the benchmark
(10 also Raghavan's 2026 `r₃` bound and Green–Tao's `r₄`); 16 cites no global
benchmark, and 22 and 25–27 state that their results are local; 28, 29 and 33 cite
Leng–Sah–Sawhney (28 their inverse theorem), and 30–32 state that their results are
local. No source claims literature
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
- 15: no propagation through Sections 15–18; the constant 18 and its coupled
  exponents not claimed optimal; the joint normal form is not a classification of
  product-property extremizers; no label repair or quantitative rounding;
- 16: the recurrence theorem is external, its threshold not numerical; an
  exponential-in-`k` gap remains at Proposition 17.7; the own-step obstruction is
  for full partitions; the ceiling concerns local-scale conclusions only;
- 17: prime moduli only, not a drop-in proof of the all-`N` `lemma_9_3`; thresholds
  not optimal; the limitation concerns the scalar certificate only; no efficient
  algorithm;
- 18: one threshold of Lemma 15.5 changes, not its exponent; the full degeneracy
  definition is needed; the `q⁻²` and `q⁻¹` rates do not match; Lau's preprint is
  imported; the cube circuits are classical;
- 19: `C_d` concerns this recovery certificate; synchronization needs the
  inherited-coordinate hypothesis; Lemma 16.10 and Theorems 18.1–18.2 are not
  completed; Maynard's theorem is imported;
- 20: not a substitute for the asymmetric Corollary 3.3; `B_k` not claimed sharp for
  `k ≥ 4`; indicator sharpness only on `𝔽₂₉^{2m}`;
- 21: the universal `u⁸` coefficient is undetermined, `20/9` is for the fixed
  `ℤ/5ℤ`; indicator sharpness is a lower example; its review is AI-assisted, not
  peer review;
- 22: class counts are not success loci; the second coefficient is not determined;
  the equal-allocation threshold is not claimed to dominate; global quintic
  avoidance is open; 7,810,000 is a lower bound;
- 23: the Section 16 closing comparison is not proved; the gluing is conditional on
  slice covers; no integer-representative fidelity; the threshold is eventual and
  universal;
- 24: not a new BSG record; the scalar sharpness concerns the relaxation only; its
  hashing theorem is outside its suite; its modern-input corollary imports
  Reiher–Schoen;
- 25: no full census and no selection simulation; `d ≥ 2` and characteristic `> 2d`
  are substantive;
- 26: no higher-degree result; its Appendix A is not the Section 16 interface;
  constants not optimal; its builder is Linux-only;
- 27: the exact formula rests on a finite certificate not checked by a proof
  assistant; the cubic bound is a union bound; nothing propagated through
  Lemma 15.5;
- 28: the logarithmic losses are not shown necessary; the `O(α⁻³)` count belongs to
  the new threshold; `Y` depends on `φ`; input defect at most `2⁻²¹`; `c₄^odd` is not
  determined; nothing propagated through Sections 13, 16, 18;
- 29: the norm comparison is not claimed sharp for `d ≥ 3`; the joint theorem is an
  absolute endpoint with row sums at most one; the restriction is for fixed fields;
- 30: the exponential base is open (`√3` against 3); the obstruction needs composite
  cyclic groups; no improved Theorem 10.13;
- 31: the critical-norm classification is Eisner–Tao's; the joint graph inequality,
  the cutoff `1/120`, the odd-order envelope and the exponents are not claimed
  optimal; the correlation-preserving theorem is prime-cyclic with a fibre cap;
  Appendix A is a corollary of Reiher–Schoen;
- 32: no best recurrence exponent, no parent containment in the variance branch, no
  higher degree, no integer rectification; non-trivial only for `N/M > 17³⁹`;
- 33: full or near-full domains only; `F_s` for `s ≥ 6` not claimed sharp;
  activation thresholds not optimal;
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
or dated sentences — 141 questions. The fourth write adds the 74 questions of 15–20
(15: 9, 16: 14, 17: 10, 18: 12, 19: 12 plus five at the end of its Section 6, 20: 12)
as 17 new items or dated sentences — 215 questions. The fifth write adds the 74
questions of 21–27 (21: 11, 22: 15, 23: 12, 24: 10, 25: 8, 26: 6, 27: 12) as 8 new items
or dated sentences — 289 questions. The sixth write adds the 69 questions of 28–33
(28: 15, 29: 13, 30: 12, 31: 13, 32: 4, 33: 12) as 4 new items or dated sentences —
**358 questions in all**:
- **I**, density transfer: 19 items, 53 questions;
- **II**, the inverse step: 49 items, 150 questions and one paragraph, plus four
  marked questions of the intakes (below);
- **III**, cubes and progressions: 28 items, 88 questions and one paragraph;
- **IV**, floor patterns: 7 items, 17 questions;
- **V**, integration and formalization: 3 items, 50 questions.

- **Answered or advanced in the sixth write** (dated notes at the questions):
  - **03's and 04's question on `c_d^odd` is advanced, not settled**, by 28 and 29:
    `0.5587725 ≤ c₄^odd ≤ 0.6914416` among 01–33, `c_d^odd ∈ [1/3, B_d]`; real parts of
    characters are not extremal for `d ≥ 4` (03's sub-question, 29's Question 1);
    28's question on a positive lower bound uniform in `d` is answered by 29.
  - **02's Subsection 11.1 is answered** in a prime-cyclic, bounded-fibre form by 31;
    its Subsection 11.2 is advanced by 31 and 29.
  - **04's Question 4 and 17's Question 2 are answered for fixed fields** by 29.
  - 12's Questions 4–6 are advanced by 30; 11's Question 7, 14's Questions 5–6 and
    15's Questions 2–3 on full products by 33; 26's Question 4 at degree two by 32;
    10's Question 7 by 31's Appendix A.
- **Marked question of the intake, not checked at the write** (item II.logselection):
  whether 28's theorem with its old-spectrum corollary gives the formal
  `theorem_10_13` with better parameters (it depends on the normalization of
  `DomainApproxHomOfOrder`).
- **Sixth write:** no claim of 28–33 was found wrong or unproved. Corrected in dated
  notes: 28's pin of 07 (39 digits); 29's "Section 8" of 17 (its Section 7); 28's
  "strictly improves `2^{−1/2}`" (true at its pin, superseded the same day); credits
  (30 re-derives 12's tree budget and compatibility inequality, uncited, with a weaker
  extension budget; 31's Section 7 repeats 10 with weaker constants). Kept as
  evidence: the intake's numerical optimum near 10.25714 for the `U⁴/U²` ratio and its
  recurrence search for 32.

- **Answered or advanced in the fifth write** (dated notes at the questions):
  - **14's Question 1 is answered** by 21 and 23: `C₅ = 2^{3/4}/3`, uniformly.
  - **13's Question 1 is answered** by 23: the prescribed-length frontier is
    `(q+2)a + qb = 1`, even with cell-dependent steps.
  - **18's first question is answered for `d = 2`** by 27 (and with it 22's and 25's
    first questions); **18's question on `d = 1`** is answered in its leading
    coefficient by 22, which also answers 27's single-pair question to that extent;
    the first-order count in small characteristic (25's Question 4) is 27's.
  - 19's Question 6 is advanced by 23; 14's Question 7 is advanced and its Question 8
    has a first instance by 22; 04's and 10's Questions 6 are advanced for `𝔽_p^d`
    codomains by 24.
- **Fifth write:** no claim of 21–27 was found wrong or unproved. Corrected in dated
  notes: framing (22's "direct Section 15 improvement" gains nothing at Lemma 15.5 at
  leading order; 24 presents 03's and 10's results as contributions, some weaker, and
  its "every abelian group" form of Proposition 7.3 is already formal; 25 and 27
  present 18's leading coefficient as their own; 27's remark on the research
  directory overlooks 18 and 22), and the intake's "weaker version" for 23's sampling
  lemma (made precise). Kept as evidence: the intake's convergence to 20/9, its exact
  `δ_{k,1}(p)` for `k ≤ 3`, its Monte Carlo for 27 at `k = 2`.

- **Answered or advanced in the fourth write** (dated notes at the questions):
  - **13's Question 3 is answered** by 18 and 19, conditionally on Maynard's
    published theorem (numbers from Lau's preprint).
  - 06's Question 7 is answered for the norm-conversion step by 20; 06's
    Question 6 is advanced by 20's strictly smaller coefficient.
  - 15's first question is answered in its leading constant (1) by 14; its second
    and third are 14's Questions 5–6.
  - 17's Question 7 is partly answered by 10's Corollary 8.2; 19's Question 8 partly
    by 18; 18's Question 7 is settled at `d = 3` by 04's norm gap.
- **Marked questions of the intake, in neither source, not proved at the write:**
  a restriction threshold `|B| ≥ 2(1+C(m,2))L^m` combining 17's filter with 04's
  per-tuple bound (item II.threshold), and composite moduli whose prime factors all
  exceed `2L−2` (item II.groups).
- **Fourth write:** no claim of 15–20 was found wrong or unproved. Corrected in dated
  notes: overstated novelty (15, 16, 18 §3, 20 §1), understated formal status (15:
  `cor146_direct_lower`; 16: `proposition_17_7_holds`; 17: `lemma_9_3_holds`,
  `corollary_9_4_holds`), stale counts and statuses (16; 19: 98/22, Lemma 16.9
  open, missing properness clause), and two over-broad statements of 17 §8 (the
  multiplicity product is a valid lower bound; composite failure needs a small prime
  factor). Kept as 19's reading, not checked: its claim about printed page 575.
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

**At the fourth write:** every comparison of 15–20 with the formal project was
checked at HEAD `0b4890a1c` (Section V.1, fourth table; every cited file and line read
there), and the 211 references of the three earlier tables were re-read at the same
HEAD (all correct). The statements above were proved or checked by the write's
script (exact arithmetic). The suites of 15–20 were rerun on copies by the routes
below (Windows, Python 3.14.4, NumPy and Matplotlib through `uv`): 15, 16's
partitions and cube coefficients, 18, 19 (all three outputs) reproduce the shipped
files (15 up to its elapsed time; 16's CSV modulo carriage returns); 16's
localization output agrees to relative `10⁻¹²` (last-ulp floats); 17 and 20 differ
only in one floating-point error field each (`1.73·10⁻¹⁷` against `2.08·10⁻¹⁷`;
`6.8·10⁻²¹` against `1.36·10⁻²⁰`); the figure scripts of 16, 18 and 19 regenerated
their figures on copies (the shipped figures are unchanged).

**At the fifth write:** every comparison of 21–27 with the formal project was
checked at HEAD `2dfe46f44` (Section V.1, fifth table; every cited file and line read
there; every Lean file the sources cite has the same blob as at their pins), and the
references of the four earlier tables were re-read at the same HEAD (all correct
except `proposition_17_7_holds`, printed at line 2900 of
`Proofs17LocalizedPhaseRemoval.lean`, which is at line 2941 since `c2975a00d`
inserted `proposition_17_7_with_upper` above it; the dated tables keep their
numbers). The statements above
were proved or checked by the write's script (exact arithmetic where possible); merge
fidelity was checked word by word against the delivered sections, and statement and
equation indices against separate builds of the seven manuscripts. The suites of
21–27 were rerun on copies by the routes below (Windows, Python 3.14.4, NumPy and
Matplotlib through `uv`): 22, 23, 24, 25 and 27 reproduce the shipped outputs (25 and
27 up to the Python version and timing fields; 27's certificate is rebuilt
identically); 21's order-five log and certificate are identical (but the absolute
certificate path it prints and its float-discrepancy line), its profile results agree
to relative `10⁻⁹` except last-ulp error fields (`1.7310914·10⁻¹³` against
`1.7310866·10⁻¹³`); 26's companion passes its 20 tests in normal and `-O` mode; the
figure scripts of 21 and 23 regenerated their figures on copies. 26's builder and its
tests need Linux (`/proc/self/fd`) and were not run.

**At the sixth write:** every comparison of 28–33 with the formal project was
checked at HEAD `5d4718772` (Section V.1, sixth table; every cited file and line read
there; every Lean file the sources cite has the same blob as at their pins). Since
`2dfe46f44` the tracked Lean files have changed only by new modules, the facade and
lines appended at the end of `Proofs05Downstream.lean`, so the 350 references of the
five earlier tables are as recorded at the fifth write (re-read by the same script). The statements above were
proved or checked by the write's script (exact arithmetic where possible); merge
fidelity was checked word by word against the delivered sections, and statement and
equation indices against separate builds of the six manuscripts. The suites of
28–33 were rerun on copies by the routes below (Windows, Python 3.14.4, NumPy
2.4.4): 28, 29 (three of four), 30, 33 and 31's extraction reproduce the shipped
outputs exactly (parsed JSON); 29's joint-rigidity output differs only in the NumPy
version string and three last-ulp floats; 31's spectral and weight-defect outputs only
in last-ulp floats; 30's stdout equals its shipped `check_stdout.txt`; 33's stdout
equals its unshipped `verification.log` but the path line; 32's companion passes its
default run (identical under `-O`) and its 30 tests. 32's builder and its test need
Linux and were not run; the figure scripts of 28 and 29 were not rerun (the shipped
figures are used).

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
1,879 theorems (12 quotes 154 and 1,508 from its pin); at the fourth write (HEAD
`0b4890a1c`) 101 and 19 (`lemma_13_7` closed), 233 modules and 2,138 theorems (16 and
19 quote 98/22 and 169/1,658 from `dca9f0638`); at the fifth write (HEAD `2dfe46f44`) still
101 and 19, 267 modules and 2,424 theorems (sources 21–27 quote no counts; at their pins
the ledger recorded 99/21, at 24's pin 97/23); at the sixth write (HEAD `5d4718772`)
105 and 15 (`theorem_7_1`, `theorem_7_2`, `theorem_8_2` and `corollary_8_3` closed), 297
modules and 2,676 theorems (sources 28–33 quote no counts; at their pins 99/21, at 30's
pin 100/20). Since `128f514af` the first obligation of `FORMALIZATION_STATUS.txt`
(Corollary 5.8) names source 41 as a written proof and 26 and 32 as its precursors. Each source's comparison
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

**Sources 15–20.** No statement of theirs is formalized. Four imply conclusions of
formal statements with better constants, none formally: 16's Theorem 1.1 implies
`proposition_17_7` (`Sections17_18.lean`, line 140; companion
`Proofs17LocalizedPhaseRemoval.lean`, line 2900); 17's theorem implies the prime
case of `lemma_9_3` and `corollary_9_4` (`Sections08_09.lean`, lines 77, 91;
companions `Proofs09Restriction.lean`, lines 376, 416, all `N`); 18's Theorem 2.8
implies the bound of `lemma_15_4` for `d ≥ 2`, `p > 2d`, and its Corollary 2.9 would
sharpen the constant `3^{16·2^k}k` of the private `selectionDegenerate_real_small`
inside `lemma_15_5_holds`. Proof-level facts the sources build on:
`cor146_direct_lower` (the unweakened Corollary 14.6 exponent, private;
`Proofs14Arrangements.lean`, line 759), `cor147_moment_eq_count` (line 484 of
`Proofs14HigherArrangements.lean`), `powersetDifference_pow` and
`polarizationPhase` (`Proofs17Phase.lean`, lines 142, 217),
`prop177_small_branch`, `section9_second_moment_le`. Section 16 has gained, after
19's pin, `section16_printed_distinct_sampling_counterexample`,
`section16_same_dimension_closing_comparison_fails` and a weaker local affine lift
(`section16_local_affine_lift` and its variants); `lemma_16_10` is still open. At
Lemma 13.5 (16's own-step interface) the development now proves the `1/16`
pre-trimming density and the statement at large prime `N` (`lemma_13_5_large_N`);
the catalogue `lemma_13_5` is still open.

**Sources 21–27.** No statement of theirs is formalized. Two formalization
candidates are recorded, not claimed: 26's Corollary 2.3 is a written proof of the
degree-one instance of the open `corollary_5_8` (`Section05.lean`, line 242), which is
trivial for `N/M ≤ 2^48`; the ledger does not change because the statement
quantifies over every degree (the repository proves only
`corollary_5_8_with_scale_holds`, `Proofs05FullPartition.lean`, line 94). 23's
common base partition would remove the square-root width loss of
`section16_local_affine_lift_sqrt` (`Proofs16LiftWidth.lean`, line 31), if the formal
Section 16 interface accepts its long final axes (not checked). 24's Proposition 7.3
in every abelian group is already `proposition_7_3_group_holds`
(`Proofs07BalogSzemeredi.lean`, line 854). 22, 25 and 27 imply the bound of
`lemma_15_4` in their ranges; 25's selection theorem improves the leading factor of
`arrangementSelectionExponent` (`Sections14_15.lean`, line 409) by `log 2`. 21 leaves
`lemma_3_10` (`Sections01_03.lean`, line 340; companion `Proofs03CubeUpper.lean`,
line 82) unchanged.

**Sources 28–33.** No statement of theirs is formalized. Formalization candidates,
not claimed: 32's theorem, with 26's corollary, gives written proofs of the instances
`k ≤ 2` of the open `corollary_5_8` (`Section05.lean`, line 242; the ledger does not
change); 33's linear branch would strengthen the exact `lemma_12_3`
(`Sections12_13.lean`, line 151; companion `Proofs12HigherArrangements.lean`, line
334), subject to matching the counts' conventions. Related exact statements:
`theorem_10_13_holds`, `lemma_10_10_holds`, `corollary_10_11_holds`,
`lemma_10_12_holds` (28, 30), `proposition_6_1_holds`, `lemma_7_5_holds`,
`corollary_7_6_holds` (29, 31; 31 implies the conclusion of `lemma_7_5`, as 10 does),
`lemma_9_3_holds` (29's theorem is for fixed fields and does not imply it) and
`lemma_3_10_holds` (28, 29). No declaration concerns `c_d^odd`.

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
  - 15's and 17's `verify.py` write `verification_results.json` beside themselves;
    their `build.sh` call `python3` and pdflatex on the delivered manuscript names
    (not shipped).
  - **16's `make_figures.py` resolves the package root as its parent's parent and
    writes unprefixed `data/localization_constants.csv` and `figures/…`**: run it
    only on a copy. 16's `verify_localization.py` and `verify_cube_coefficients.py`
    print to standard output; `verify_partitions.py` takes `--output`.
  - 18's `verify_refinements.py` takes `--output`; its figure script writes
    `partition_exponents.{pdf,png}` beside itself.
  - 19's verifiers write fixed names beside themselves; its `make_figures.py` writes
    `../figures/` and `poisson_constants.json` beside itself.
  - 20's `verify.py` takes `--output` (`-S` for the exact part, NumPy for
    `--gauss`); its Makefile names `article.tex` and an unshipped
    `exact_verification_report.json`.
  - **21's `verify_order5.py` and `make_figures.py` resolve the package root as
    their parent's parent and write unprefixed `data/…` and `figures/…`**; run them
    only on a copy. `verify_order5.py` prints the absolute path of its certificate
    (the shipped log has the sandbox path `/workspace/scratch/…`);
    `verify_profiles.py` takes `--output`.
  - **22's `verify_certificates.py` and `verify_two_cubes.py` overwrite
    `ROOT/data/*.json` under unprefixed names**; `verify_polynomial_patterns.py`
    prints its JSON; `verify_norm_obstruction.py --output` defaults to its own
    directory.
  - 23's verifiers print to standard output (its Makefile redirects into `data/`);
    its `make_figure.py` writes `ROOT/figures/`.
  - 24's `verify.py --output` defaults to the current directory.
  - **25's `verify.py` and `compare_cutoffs.py` write `parents[1]/data/…` under
    unprefixed names**, which in the shipped layout is this directory's `data/`: run
    them only on a copy.
  - 26's `test_companion.py` loads `ROOT/companion/exact_checks.py`; its `build.py`
    checks an exact inventory of the delivered tree and is Linux-only.
  - **27's `verify.py` reads `ROOT/code/exact_certificate.json`** (shipped as
    `data/27-…-exact_certificate.json`) and with `--write` writes `ROOT/verification.json`
    and `ROOT/code/exact_certificate.json`; run it on a copy with the delivered layout.
  - 28's verifiers take `--output` (`verify_u4.py` defaults to `./u4_exact_results.json`);
    its `make_figures.py` writes `ROOT/figures/`.
  - 29's verifiers take `--output` (`verify_rank_restriction.py` defaults beside
    itself); its `make_figures.py` writes `ROOT/figures/norm_bounds.{pdf,png}`.
  - 30's `verify.py` defaults to `ROOT/results/verification.json` (a directory not
    shipped).
  - **31's `verify_spectral_rigidity.py` has no `--output` and writes
    `ROOT/data/spectral_rigidity_checks.json` under its unprefixed name**; run it only
    on a copy. Its other two verifiers take `--output`.
  - 32's tests load `ROOT/build.py` and `ROOT/companion/exact_checks.py` by path, and
    `build.py` enforces an exact source inventory and is Linux-only.
  - **33's `verify.py` and `verify_erasures.py` import `arrangements` and
    `polynomial_checks`** (prefixed names are not importable) and write
    `ROOT/data/verification.json` and `erasure_verification.json`; restore the
    delivered names on a copy.

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
  - 16's `verify_localization.py` docstring names `phase_sliding_verify.py`; 16, 18 and
    19 cite Lau as "C. F. (Joshua) Lau" (arXiv: Cheuk Fung Lau; bibliography note);
    16's composite-modulus example makes both recurrence errors exactly 0.
  - 17's `verify.py` records the repeated-entry value "1/2" as a string; its table's
    "new" column uses the first form of its bound (0.40 dex above the abstract's).
  - 19's source audit and README quote 98/22 and 169/1,658 from its pin (dated notes
    in the article); 19 and 20's READMEs (not shipped) say `python3`.
  - 21's README (not shipped) says `make pdf`, its Makefile runs two pdflatex
    passes; its Section III.55 names `verify_order5.py` without `code/`. 21's, 22's,
    23's, 25's and 27's Makefiles and 24's and 26's READMEs use `python3`.
  - 22's `SOURCE_LEDGER.json` and 26's `SOURCES.md` give SHA-256 values of the pinned
    files with one appended newline (a retrieval artifact; the byte counts are one
    larger), not of the blobs themselves.
  - 23's small obstruction uses `R = 1331`, not `DC − 1`; any gap value works.
  - 27's Table II.95.1 lists `R_{2,2} = 2,585,419`, which is not `H₈ = 2,585,444`
    (dated note); both are correct.
  - 28's `source_provenance.json` and bibliography give source 07's pin with 39
    hexadecimal digits (`…6df6cfc065a81`; the commit is `…6df6c6fc065a81`; dated note).
  - 29 cites "Section 8" of 17's manuscript for the random linear maps; it is
    Section 7 there (bibliography note).
  - 30's text names `results/verification.json`, 31's `make verify`, 33's
    `data/example.json` and `code/…` by delivered names; 30's, 31's and 33's
    Makefiles use `python3`.
  - 32's `SOURCES.md` gives SHA-256 values of the pinned files with one appended
    newline, as 26's does (41's placement records the same finding).
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
    (`checks/verify.py`, `gowers_bohr_extension.tex`, …); so do 15's
    `provenance.json` and `integration.md`, 16's `pdf_review.txt`, 17's and 20's
    `source_manifest.json`, 18's `provenance.json`, 19's `source-audit.json` and 20's
    `BUILD_REPORT.txt` and `validation_summary.json`.
  - 21's `source_manifest.json` and `package_validation.json`, 22's
    `SOURCE_LEDGER.json`, 23's `source_manifest.json` and `build_validation.json`,
    24's `PROVENANCE.md`, 25's `SOURCE_AUDIT.md` and `build_summary.json`, 26's
    `SOURCES.md` and 27's `SOURCE_AUDIT.md` and `FORMALIZATION.md` name delivered
    files.
  - 28's `source_provenance.json` and `build_summary.txt`, 29's `source_audit.json`
    and `build_validation.json`, 30's and 33's `SOURCE_AUDIT.md` and
    `FORMALIZATION.md`, 30's `build_validation.json`, 31's `SOURCE_LEDGER.json` and
    `VALIDATION.json`, 32's `SOURCES.md` and 33's `build_validation.json` name
    delivered files.
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
    quotations;
  - fourth write: six macros renamed (16's `\conj`, `\BB`; 17's `\code`; 18's `\T`;
    19's `\commit`; 20's `\U`); 19's `question` set as "Research question" and 20's
    numbered within its section; 19's `\cref` written out; three figure paths; the
    title-page statements of 17–20 printed in their front-matter sections; 16's
    explicit equation tags kept.
  - fifth write: three macros renamed (23's `\snapshot`, 24's `\code`, 25's
    `\card`); 22's and 27's `question` set as "Research question", 21's, 24's and
    25's as "Question" (25's numbered within its section); 27's `\cref` written out
    as its own `\crefname` settings print them; 27's label `sec:d2` prefixed as
    `sec:dtwo`; four labels added to unlabelled statements (22: three, 23: one); three
    figure paths; the title-page statements of 21, 23, 24 and 27 printed in their
    front-matter sections; 22's and 23's equation tags kept.
  - sixth write: eight macros renamed (28's `\T` as `\Tcirc`, the `\pin` of 28, 30
    and 33, 29's `\code`, 30's `\defect`, 31's `\Energy` and `\ip`, 33's `\V`); 31's
    `mathrsfs` and column type `L` added; 28's, 31's and 33's `question` set as
    "Research question", 29's and 30's as "Question"; 28's `\cref` written out;
    28's three `\part` headings printed unnumbered at the head of the sections they
    introduce; three figure paths; the title-page statements of 28, 29, 30 and 33
    printed in their front-matter sections.

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

Sources 15–20 (added in the fourth write; same variables):

```sh
mkdir -p "$T/r15" && cp "$R/code/15-collision-amplification-verify.py" "$T/r15/verify.py"
(cd "$T/r15" && $PY verify.py > out_run.txt)   # compare with data/15-...-verification.txt and
                                               # ...-verification_results.json (elapsed time differs)
mkdir -p "$T/r16/code" "$T/r16/data" "$T/r16/figures" && for f in make_figures verify_cube_coefficients verify_localization verify_partitions; do
  cp "$R/code/16-phase-localization-$f.py" "$T/r16/code/$f.py"; done
(cd "$T/r16" && $PY code/verify_localization.py > loc.json &&      # NumPy; compare with data/16-...-localization_results.json
  $PY code/verify_partitions.py --output part.json > /dev/null &&
  same part.json "$OLDPWD/$R/data/16-phase-localization-partition_results.json" &&
  $PY code/verify_cube_coefficients.py > cube.txt &&
  same cube.txt "$OLDPWD/$R/data/16-phase-localization-cube_results.txt" &&
  $PY code/make_figures.py)    # Matplotlib; writes data/ and figures/ inside the copy only
mkdir -p "$T/r17" && cp "$R/code/17-polynomial-restriction-verify.py" "$T/r17/verify.py"
(cd "$T/r17" && $PY verify.py > /dev/null)    # NumPy; writes verification_results.json beside itself
mkdir -p "$T/r18" && for f in verify_refinements make_partition_figure; do
  cp "$R/code/18-arrangement-degeneracy-$f.py" "$T/r18/$f.py"; done
(cd "$T/r18" && $PY verify_refinements.py --output rerun.json > /dev/null)
mkdir -p "$T/r19/verification" "$T/r19/figures" && for f in verify_sampling verify_polynomial make_figures; do
  cp "$R/code/19-shared-interpolation-$f.py" "$T/r19/verification/$f.py"; done
(cd "$T/r19" && $PY verification/verify_sampling.py > /dev/null && $PY verification/verify_polynomial.py > /dev/null &&
  same verification/sampling_results.json "$OLDPWD/$R/data/19-shared-interpolation-sampling_results.json" &&
  same verification/polynomial_results.json "$OLDPWD/$R/data/19-shared-interpolation-polynomial_results.json")
mkdir -p "$T/r20" && cp "$R/code/20-quadratic-counting-verify.py" "$T/r20/verify.py"
(cd "$T/r20" && $PY -S verify.py --output exact_rerun.json > /dev/null &&
  $PY verify.py --gauss --output full_rerun.json > /dev/null)   # NumPy for --gauss
```

Sources 21–27 (added in the fifth write; same variables):

```sh
mkdir -p "$T/r21/code" "$T/r21/data" "$T/r21/figures"
for f in verify_order5 verify_profiles make_figures; do cp "$R/code/21-characteristic-five-$f.py" "$T/r21/code/$f.py"; done
(cd "$T/r21" && $PY code/verify_order5.py > data/order5_verification.txt &&
  cmp data/order5_cube_fourier_certificate.csv "$OLDPWD/$R/data/21-characteristic-five-order5_cube_fourier_certificate.csv" &&
  $PY code/verify_profiles.py --output data/profile_validation_results.json > data/profile_verification.txt &&
  $PY code/make_figures.py)    # Matplotlib; writes data/ and figures/ inside the copy only
mkdir -p "$T/r22/code" "$T/r22/data"
for f in verify_certificates verify_two_cubes verify_polynomial_patterns verify_norm_obstruction; do
  cp "$R/code/22-degree-filtrations-$f.py" "$T/r22/code/$f.py"; done
(cd "$T/r22" && $PY code/verify_certificates.py && $PY code/verify_two_cubes.py &&
  $PY code/verify_polynomial_patterns.py > data/polynomial_pattern_verification.json &&
  $PY code/verify_norm_obstruction.py --output data/norm_obstruction_verification.json)
  # compare data/*.json with data/22-degree-filtrations-*.json (parsed; CRLF on Windows)
mkdir -p "$T/r23/code" "$T/r23/data" "$T/r23/figures"
for f in verify_prescribed_partitions check_fifth verify_section16_gluing make_figure; do
  cp "$R/code/23-sharp-thresholds-$f.py" "$T/r23/code/$f.py"; done
(cd "$T/r23" && $PY code/verify_prescribed_partitions.py > data/partition_checks.json &&
  $PY code/check_fifth.py > data/fifth_checks.txt &&
  same data/fifth_checks.txt "$OLDPWD/$R/data/23-sharp-thresholds-fifth_checks.txt" &&
  $PY code/verify_section16_gluing.py > data/gluing_checks.json &&
  $PY code/make_figure.py)     # NumPy and Matplotlib; writes figures/ inside the copy
mkdir -p "$T/r24" && cp "$R/code/24-section7-compression-verify.py" "$T/r24/verify.py"
(cd "$T/r24" && $PY verify.py --output rerun.json > /dev/null)
mkdir -p "$T/r25/code" "$T/r25/data"
for f in verify compare_cutoffs; do cp "$R/code/25-codimension-one-$f.py" "$T/r25/code/$f.py"; done
(cd "$T/r25" && $PY code/verify.py && $PY code/compare_cutoffs.py)   # writes $T/r25/data/
mkdir -p "$T/r26/companion" "$T/r26/tests"
cp "$R/code/26-threshold-free-affine-exact_checks.py" "$T/r26/companion/exact_checks.py"
cp "$R/code/26-threshold-free-affine-test_companion.py" "$T/r26/tests/test_companion.py"
(cd "$T/r26" && $PY -B companion/exact_checks.py && $PY -B companion/exact_checks.py --full &&
  $PY -B tests/test_companion.py && $PY -B -O tests/test_companion.py)
mkdir -p "$T/r27/code" && cp "$R/code/27-degeneracy-second-order-verify.py" "$T/r27/code/verify.py"
cp "$R/data/27-degeneracy-second-order-exact_certificate.json" "$T/r27/code/exact_certificate.json"
(cd "$T/r27" && $PY code/verify.py &&
  $PY code/verify.py --subset --write)   # NumPy; rewrites code/exact_certificate.json and verification.json in the copy
```

Sources 28–33 (added in the sixth write; same variables):

```sh
mkdir -p "$T/r28/code" && for f in verify_selection verify_u4; do cp "$R/code/28-log-selection-$f.py" "$T/r28/code/$f.py"; done
(cd "$T/r28" && $PY code/verify_selection.py --output sel.json > /dev/null && $PY code/verify_u4.py --output u4.json > /dev/null)
  # compare with data/28-log-selection-selection_checks.json and -u4_exact_results.json (parsed)
mkdir -p "$T/r29/code" && for f in verify_moments verify_coefficients verify_rank_restriction verify_joint_rigidity; do
  cp "$R/code/29-moment-stability-$f.py" "$T/r29/code/$f.py"; done
(cd "$T/r29" && $PY code/verify_moments.py --output m.json && $PY code/verify_coefficients.py --output c.json &&
  $PY code/verify_rank_restriction.py --output r.json && $PY code/verify_joint_rigidity.py --output j.json) > /dev/null   # NumPy for the last
mkdir -p "$T/r30/code" && cp "$R/code/30-fixed-radius-bohr-verify.py" "$T/r30/code/verify.py"
(cd "$T/r30" && $PY code/verify.py --output v.json > out.txt &&
  same out.txt "$OLDPWD/$R/data/30-fixed-radius-bohr-check_stdout.txt")
mkdir -p "$T/r31/code" "$T/r31/data" && for f in verify_spectral_rigidity verify_weighted_extraction verify_weight_defects; do
  cp "$R/code/31-weighted-spectra-$f.py" "$T/r31/code/$f.py"; done
(cd "$T/r31" && $PY code/verify_spectral_rigidity.py &&      # NumPy; writes data/ inside the copy
  $PY code/verify_weighted_extraction.py --output data/x.json && $PY code/verify_weight_defects.py --output data/d.json) > /dev/null
mkdir -p "$T/r32/companion" "$T/r32/tests"
cp "$R/code/32-quadratic-increments-exact_checks.py" "$T/r32/companion/exact_checks.py"
cp "$R/code/32-quadratic-increments-test_companion.py" "$T/r32/tests/test_companion.py"
(cd "$T/r32" && $PY -B companion/exact_checks.py && $PY -B -O companion/exact_checks.py && $PY -B tests/test_companion.py)
mkdir -p "$T/r33/code" "$T/r33/data"
for f in verify verify_erasures arrangements polynomial_checks; do cp "$R/code/33-arrangement-stability-$f.py" "$T/r33/code/$f.py"; done
cp "$R/data/33-arrangement-stability-example.json" "$T/r33/data/example.json"
(cd "$T/r33" && $PY code/verify.py --extended && $PY code/verify_erasures.py &&
  $PY code/arrangements.py data/example.json --orders 4 16 --output data/ex.json)   # writes data/ inside the copy
```

Requirements and run times:
- 02 and 10 need NumPy; 05's `verify.py` needs mpmath (even for `--part exact`);
  09's `verify_lattices.py` needs SymPy (1.14.0 was used); 12's
  `verify_bohr_fourier.py`, 13's `verify_cubes.py` and `verify_fourier_counting.py`
  and 14's `verify_results.py` need NumPy; the figure scripts of 12, 13 and 14 need
  Matplotlib. 16's `verify_localization.py`, 17's `verify.py` and 20's `--gauss`
  need NumPy; the figure scripts of 16, 18 and 19 need Matplotlib.
- 23's `make_figure.py` needs NumPy and Matplotlib, 21's `make_figures.py`
  Matplotlib; 27's `--subset` needs NumPy. 25's and 27's JSON record the Python
  version and timings; compare parsed JSON. 26's `test_build.py` and `build.py` need
  Linux.
- 29's `verify_joint_rigidity.py`, 31's `verify_spectral_rigidity.py` and the figure
  scripts of 28 and 29 need NumPy (and Matplotlib for the figures); 29's and 31's
  JSON record float residuals and the NumPy version; compare parsed JSON. 30's
  verifier takes about 20 s, 31's extraction about 30 s, 33's `--extended` about
  25 s. 32's `test_build.py` and `build.py` need Linux.
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

At the first write the 01–05 block, at the second write the 06–10 block, at the
third write the 11–14 block, at the fourth write the 15–20 block and at the fifth
write the 21–27 block (with NumPy and Matplotlib through `uv`), and at the sixth write
the 28–33 checks (in their delivered layout, see "At the sixth write" above) run verbatim from the repository root (Git Bash on Windows, `PY=py`; 09 and 10 through
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
The build gives 1001 pages, with no LaTeX warnings, no undefined references, no
duplicate destinations and no overfull boxes. Packages: amsmath, amssymb, amsthm,
mathtools, lmodern, geometry, microtype, graphicx, booktabs, longtable, tabularx,
array, enumitem, needspace, placeins, xcolor, hyperref, xurl, bookmark, mathrsfs
(source 31's script letters), tikz
(source 07's diagram), listings (source 08's certificate code) and tcolorbox
(source 12's result box). Only
`article.pdf` is committed.

## Licences

Repository text is MIT-0. The sources quote short passages of the cited
literature with attribution. No third-party paper, repository copy or font is
redistributed.
