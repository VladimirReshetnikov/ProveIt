# Finite-Prefix Corrections and Dual Certificates for Polyomino Growth

**A computer-assisted exact-rational bound λ ≤ 2249/500 = 4.498 for Klarner's constant, a certificate theorem for convolution recurrences, and (Part II) the spectral saturation of the exact-prefix hierarchy**

This is a report of ProveIt's research-report collection
(`polyomino-growth-finite-prefix-corrections`), dated September 2026 and
built from two manuscripts: the original report (Part I, batch 36) and an
addition (Part II, batch 40). It continues the formal Lean project
`Combinatorics/Polyominoes/KlarnerConstant`, whose kernel-checked endpoint is
λ ≤ 9047/2000 = 4.5235. Author line of both sources: "Research report
prepared for Vladimir Reshetnikov", AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 | batch 36, manuscript 06 | `ProveIt_Polyomino_Research` (delivered in `e13affd32`; delivered main file `article.tex`, 27-page PDF) | `e21766d04` | `1a1396d4d` | Part I: Sections 1–11 and Appendices A–C; Sections 1.4, 1.5 and Appendix D added in the batch-36 write |
| 02 | batch 40, manuscript 05 | `ProveIt_Spectral_Saturation` (inner directory `ProveIt_Spectral_Saturation/`, arrived in `017e6c0d8`; *When Exact Prefixes Stop Improving*, 27-page PDF) | `74f7f5bdb` | `afb2d1227` (prefix `02-spectral-saturation-`) | Part II: Sections 13–28 (its Sections 1–11 and Appendices A–C); Section 12 added in the write |

**Status: AI-assisted and unrefereed. Nothing in this report is formalized.**
The bound 4.498 is a computer-assisted theorem (exact enumeration plus an
exact rational certificate, replayed in Python), not a Lean theorem; the
project's Lean-verified bound remains 4.5235. Part II's theorems have
written proofs only, and its 4.3149 is **not** a bound on λ (see below).

```
README.md                          this guide (replaces both delivery READMEs)
VALIDATION.md                      Part I source's validation record, as delivered
02-spectral-saturation-PROOF_STATUS.md   Part II source's claim-by-claim status, as delivered
02-spectral-saturation-SOURCES.md        Part II source's provenance and literature ledger, as delivered
article.tex                        the report, standalone LaTeX; \inputs tex/*.tex and two data/02-*.tex
article.pdf                        the compiled report, 61 pages (unnumbered title page,
                                   contents pages i–iii, then pages 1–57)
code/Makefile                      Part I's delivered Makefile (moved from the package root; see below)
code/check_profile.py              compares a regenerated CSV table with data/profiles.json
code/discover_certificates.py      numerical candidate search and rounding (exploratory; overwrites data/)
code/enumerate.cpp                 incremental marked enumerator, sizes 1..18 (C++17)
code/enumerate_direct.cpp          direct-scanning marked enumerator (C++17)
code/make_tables.py                regenerates tex/*.tex from data/ (not part of the proof)
code/model.py                      the 53-monomial map, patterns, exact polynomial arithmetic
code/research.py                   set-based Python enumerator and float critical-point search (exploratory)
code/verify.py                     exact rational replay of every Part I certificate (standard library only)
code/02-spectral-saturation-bui_model.py   Part II: the map transcribed from model.py, profile reader, exact Jacobian
code/02-spectral-saturation-verify.py      Part II: exact replay of the 4.3149 witness and scalar brackets (standard library)
code/02-spectral-saturation-discover.py    Part II: numerical witness search (NumPy; outside the proof)
code/02-spectral-saturation-build.sh       Part II: the delivered pdfLaTeX build script (see below)
data/critical_estimates.json       floating-point critical estimates (not certified)
data/dual_original.json            the 53 balanced integer weights at ζ_dual = 100000/452349
data/profiles.json                 exact unmarked and marked counts, sizes 1..18
data/profiles_18.csv               the same table as CSV (19 columns × 18 rows); also Part II's input
data/profiles_python_11.json       the source's independent Python enumeration through size 11
data/requirements-discovery.txt    NumPy/SciPy/SymPy for Part I's exploratory scripts (moved from the root)
data/upper_N7.json … upper_N18.json   twelve rational upper certificates, prefix sizes 7..18
data/verification.json             Part I verifier's exact record (rewritten by every --report run)
data/verification.txt              Part I verifier's recorded stdout
data/02-spectral-saturation-bui_spectral_certificate.json   Part II: the positive integer witness w
data/02-spectral-saturation-verification.json   Part II verifier's exact record (six rational brackets)
data/02-spectral-saturation-verification.txt    Part II verifier's recorded stdout
data/02-spectral-saturation-scalar_table.tex    Part II: generated Table 9 (\input by article.tex)
data/02-spectral-saturation-witness_table.tex   Part II: generated Table 10 (\input by article.tex)
tex/dual_table.tex                 generated table of dual weights (cites \ref{eq:map})
tex/profiles_1_9.tex               generated profile table, sizes 1..9
tex/profiles_10_18.tex             generated profile table, sizes 10..18
tex/progress_table.tex             generated table of the prefix hierarchy
tex/upper_table.tex                generated N = 18 certificate table
```

That is 49 files: 6 at the root, 13 in `code/`, 25 in `data/` and 5 in
`tex/`. Part I's delivery had 39 files (35 shipped byte-identical; its
`article.tex` is the source of the Part I text; its README, 27-page PDF and
checksum manifest `SHA256SUMS`, 38/38 entries matching at intake, not
shipped). Part II's delivery had 15 files: the 11 prefixed files above are
byte-identical to it; its `article.tex` is the source of the Part II text;
its README and 27-page PDF are not shipped; and its `data/profiles_18.csv`
is not shipped because it is byte-identical (blob `82648328`) to Part I's
`data/profiles_18.csv`, which Part II's text and scripts therefore use.

## Labels

Part I's labels carry the prefix `kfp:` with **one exception, `eq:map`**
(the 53-monomial map, equation (6)): the delivered, generated and
byte-identical `tex/dual_table.tex` cites it as `\ref{eq:map}`, and
`code/make_tables.py` regenerates that text, so the key is kept unprefixed.
Part I had 56 labels after the batch-36 write (52 prefixed source labels,
`eq:map`, `kfp:sec:notation`, `kfp:sec:formal-status`,
`kfp:app:provenance`). All 56 are unchanged, and keep their printed
numbers.

Part II's labels carry the prefix **`kfp:sat:`**. The report now has 137
labels (pattern `\label(\[[^]]*\])?\{`): the 56 above; `kfp:sec:conclusion`
(Part I's conclusion, labelled so that Part II can point to it); the
manuscript's 77 labels, all given the prefix `kfp:sat:` (for example
`thm:critical` → `kfp:sat:thm:critical`, `eq:key` → `kfp:sat:eq:key`); and
three new ones (`kfp:sat:sec:source`, `kfp:sat:sec:notation`,
`kfp:sat:tab:notation`). The twelve Part II lemma, proposition and corollary
labels carry cleveref type hints (`\label[lemma]{…}` and so on), as Part I's
do. `02-spectral-saturation-PROOF_STATUS.md` names the manuscript's
unprefixed labels (`thm:critical`, `thm:limit`, `thm:sharp`, `thm:branch`,
`thm:bui`); they are Theorems 15.2, 16.3, 18.2, 19.1 and 22.2 here.

Text added in the batch-36 write is marked `[write]` in the PDF; text added
in the batch-40 write is marked `[write]` inside Part II and "[Added 29
September 2026, batch 40: …]" in Part I.

## Notation

Section 1.4 fixes Part I's conventions; no delivered Part I symbol was
renamed and no normalization changed.

- The seventeen upper-case letters `C, D, E, F, G, H, P, Q, R, S, T, U, V, W,
  X, Y, Z` name the neighborhood types and their counts; lower-case `c … z` are
  the coordinates of the vector `X`. Many of these letters are reused
  (`P_N` the exact prefix, `D_N` the defect, `T_N`, `Y_N`, `B_N`, the
  enumerator's sets `S`, `U`, `E`, the offset sets `R`, `E`, `B`, the nonlinear
  part `H`, the dual product `𝒞`, the map `F(X) = Φ(ζ,X)` and the unknowns
  `X_1, …, X_d` of a general system, …); Section 1.4 tabulates every reuse
  across sections (constants local to one proof are left to context).
- **Collision with the project.** The project's research note
  (`Combinatorics/Polyominoes/KlarnerConstant/Research/klarner-bound-4.5235.md`,
  §3) writes `b_N` for the ζ-weighted prefix profile. That profile is
  `p_N = P_N(ζ)` here; this report's `b_N` (Section 8, and Part II's
  (35)) is the high-degree forcing vector, and `b_{ik}` are ξ-exponents. The
  project's supersolution `a` is `v` here. `λ`, `A(n) = A_n`, `ζ` and the map
  (`Φζ` there, `Φ(ζ,·)` here) agree.
- `A_0 = 0` here, unlike OEIS A001168's `a(0) = 1`.
- `μ_original` (growth of Bui's *uncorrected equality recurrence*) occurs only
  here. Tempting false reading printed in the article: its lower bound 4.52349
  is a lower bound on λ. **It is not.**

**Part II** (Section 12.2 and Table 8) keeps the manuscript's notation with
two disclosed renamings: the manuscript's formal size variable `z` (its
Sections 1–8) is written `ξ`, as in Part I and in the manuscript's own
Section 9 onward, where `z` is a coordinate; and the manuscript's Perron
eigenvalue `λ`, `λ(t) = spr J(t)`, is written `Λ`, because `λ` is Klarner's
constant in Part I. No normalization changed. Table 8 lists every Part II
symbol against Part I: `t` (Part II) is Part I's `ζ`; Part II's `A` is Part
I's bold `a`; `D` is the full defect `Φ(ξ,A) − A` and `𝓡_N = D − D_N` its
tail (Part I's `[ξ^{>N}]` operator is a different thing); `R` is a radius,
not an offset set; `G(t,h,r)`, `Q_t(h)`, `F_N`, `S`, `H_N`, `T`, `w` collide
with coordinate letters or Part I objects and are distinguished there. The
delivered table `data/02-spectral-saturation-scalar_table.tex` heads its gap
column `ρ_* − ρ_N`; that `ρ_*` is the text's `r_* = 1/3`.

## What the report claims

Numbers are those of the built `article.pdf`.

### Part I (batch 36)

- **Lemma 3.2** (formal fixed points and comparison) for proper positive
  polynomial systems (nilpotent linear part).
- **Theorem 3.3 (prefix-corrected majorant).** With the exact prefix `P_N`
  of the true counts, `Ψ_N(ξ,Y) = Φ(ξ,P_N+Y) − T_N` has nonnegative
  coefficients, and its fixed point gives `B_N = P_N + Y_N` with `A ⪯ B_N`
  and `[ξ^{≤N}]B_N = P_N`. No convergence is assumed.
- **Theorem 3.4 (rational upper certificate).** `v ≥ P_N(ζ)` (the tail
  condition, essential by Remark 3.5) and `v ≥ Φ(ζ,v) − D_N(ζ)` give
  `a_{i,n} ≤ v_i ζ^{-n}`, hence `A_n ≤ v_G ζ^{-n}` and `λ ≤ 1/ζ`.
- **Theorem 3.6.** `A ⪯ B_{N+1} ⪯ B_N`; a certificate for `N` is one for `N+1`.
- **Theorem 4.1 (computer-assisted).**
  `A_n ≤ (927884613/10^9)(2249/500)^n` for `n ≥ 1`, so
  **λ ≤ 2249/500 = 4.498 < 4.5**. It uses the size-≤18 marked table
  (Appendix A) and the `N = 18` rational vector (Table 2); every residual is
  at least 99/10^9 and every tail budget at least 14724/10^6. The certificates
  for `N = 7, …, 17` give 4.5233, 4.5225, 4.5212, 4.5194, 4.5173, 4.5149,
  4.5123, 4.5096, 4.5068, 4.5039 and 4.5009 (Table 3).
- **Proposition 4.2** (correctness of the include/exclude enumerator) and an
  a-priori `uint64` overflow bound through size 18.
- **Theorem 5.1 (balanced-monomial obstruction)**, by weighted AM–GM, and the
  lower-growth consequence (18).
- **Theorem 6.3 (certificate alternative)**, with Lemma 6.2: for productive,
  strongly connected, nonlinear positive polynomial systems with rational data,
  exactly one of "positive supersolution" and "balanced integer weights with
  product > 1" holds. This answers the certificate-existence part of Bui's
  Question 2 for that class.
- **Theorem 7.1.** `452349/100000 ≤ μ_original ≤ 9047/2000` for the
  uncorrected equality recurrence (53 integer weights of total 1,000,000, an
  exact rational log enclosure (20), and the project's 4.5235 vector
  replayed). So no supersolution of the uncorrected system proves a bound below
  4.52349; the improvement comes from the prefix correction.
- **Theorem 8.1 (stability and obstruction)** of the prefix hierarchy
  (`spr(J) < 1` gives certificates for large `N`; a supercritical, irreducible,
  nonzero-forcing case obstructs every `N`).
- **Theorem 8.2.** For `Φ = ξ + x²` and `A = ξ/(1−ξ)` (growth 1) the
  prefix-majorant growths tend to 3.
- A conditional sensitivity formula (24), a Lean extension plan (Section 9.3)
  and ten research questions (Section 10).

### Part II (batch 40)

For a proper positive polynomial system with `A ⪯ Φ(ξ,A)`, full defect
`D = Φ(ξ,A) − A`, tail `𝓡_N = D − [ξ^{≤N}]D`, `J(t) = Φ_X(t,A(t))` at the
**true** profile:

- **Theorem 15.2 (critical alternative).** If `A(t)` is finite, `J(t)` is
  **irreducible** and `spr J(t) ≥ 1`, then a level-`N` certificate at `t`
  exists iff `𝓡_N(t) = 0` iff `D = D_N` iff `B_N = A`. This classifies the
  equality case `spr(J) = 1` that Part I left open, **for irreducible `J`
  only**. Corollary 15.3: with a nonlinear monomial and `A(t) > 0`, the only
  possible certificate is `A(t)`.
- **Theorem 16.3 (spectral saturation).** If `D` is not a polynomial and
  `J(t)` is irreducible on `(0,R)`, the corrected radii increase to the first
  Perron crossing `r_*` (or to the true radius `R` if there is none), and no
  finite-prefix series converges at an interior `r_*`. Proposition 16.1 is a
  quantitative supersolution test with slack `α` and curvature `C`.
- **Lemma 17.1 / Corollary 17.2.** Tails of a nonnegative series analytic
  beyond `r` are flat on windows of width `O(√tail)`, with no regularity or
  nonlacunarity assumption on the coefficients.
- **Theorem 18.2 (square-root law).** At an interior nonlinear crossing,
  with `κ = ℓᵀJ'(r_*)u > 0`, `β = ½ℓᵀΦ_XX[u,u] > 0`, `η_N = ℓᵀ𝓡_N(r_*)`:
  `r_* − ρ_N ~ (2√β/κ)√η_N` (43), `B_N(ρ_N) − A(ρ_N) = u√(η_N/β) + o(√η_N)`
  (44), and the growth version (45). Lemma 18.3 localizes every possible
  certificate, so the fold is the actual radius.
- **Theorem 19.1.** A universal scaled branch, and the local square-root
  amplitude `a_N = u√(r_*κ) β^{-3/4} η_N^{1/4} + o(η_N^{1/4})` (57); local
  positive-axis statements only.
- **Section 20.** For Part I's scalar example (Theorem 8.2):
  `1/3 − ρ_N ~ (2/9)√(2N−1) 3^{−N/2}` and `μ_N − 3 ~ 2√(2N−1) 3^{−N/2}` (62),
  with an independent derivation from the exact root equation (64) and six
  rational brackets (Table 9; 260 bisections each).
- **Section 21.** Four examples showing that zero residual forcing,
  irreducibility and nonlinearity cannot be dropped, and that primitivity is
  not needed.
- **Theorem 22.2 (all-prefix barrier).** For the fixed seventeen-variable Bui
  map (6) and the size-18 profile of Appendix A, the integer vector `w` of
  Table 10 satisfies `J_18(t_0) w ≥ (1000001/1000000) w` at
  `t_0 = 10000/43149` (exact rational arithmetic; smallest ratio minus one
  about 4.934886683e−6). With a vertical-column argument for nonzero forcing
  at every size and persistence, **every corrected majorant has growth
  `μ_N ≥ 43149/10000 = 4.3149`**, including its `g` component.
- A proof audit and a three-layer formalization sequence (Section 23), ten
  research projects (Section 24), the replay algorithm (Section 27) and the
  evidence ledger (Section 28).

## What the report does not claim

Appendix D.3 lists Part I's thirteen limitations (N1–N13) and three added in
the batch-36 write (W1–W3):

- (N1) `μ_original ≥ 4.52349` is **not** a lower bound on λ.
- (N2) No new Lean formalization; the Lean proof of 4.5235 is not a proof of
  4.498, of the finite-prefix theorem, or of the size-18 data.
- (N3) The arithmetic checker does not prove that the table enumerates the
  stated objects; its consistency checks are necessary conditions only.
- (N4) The enumeration cross-checks are not a formal certificate that every
  size-18 object was generated exactly once; the two C++ implementations share
  one generation strategy. (The source's caveat that no fresh size-18 run was
  made after the final command-line changes is re-scoped below.)
- (N5) AI-assisted draft, not independently refereed.
- (N6) Novelty only relative to the inspected snapshot and sources; no
  exhaustive priority search.
- (N7) Geometric programming, weighted AM–GM and Redelmeier-style enumeration
  are prior tools.
- (N8) The alternative covers only productive, strongly connected, nonlinear
  systems; no uniform bit-length bound; no maximum or signed recurrences.
- (N9) The case `spr(J) = 1` is not classified. **Re-scoped 29 September
  2026:** Part II classifies it for irreducible `J` (Theorem 15.2); the
  reducible case is still open. Dated pointers were added where Part I says
  so (after Theorem 8.1, in D.3, in the audit row of Appendix C) and in
  Sections 1.2, 1.5, 8.2, research questions 4 and 9, and the conclusion.
- (N10) Theorem 8.2 does not disprove Bui's Question 1.
- (N11) The sensitivity formula is conditional and unused in Theorem 4.1.
- (N12) The numerical critical estimates (Table 3, middle column;
  `data/critical_estimates.json`) are not certified.
- (N13) The OEIS comparison is a consistency check, not an input.
- (W1) The geometric lemma is kernel-checked in ProveIt only relative to the
  transcription of Bui's diagrams into `Patterns.lean`.
- (W2) 4.498 remains unverified by Lean; 9047/2000 remains the project's
  Lean-verified bound.
- (W3) The earlier bounds (Eden, Klarner–Rivest, Barequet–Shalah) were not
  re-examined; their bibliographic data were checked, their contents not read.

Part II keeps every limitation of its source (Sections 13.5, 19, 22.3, 23.3,
Section 12's status box, and `02-spectral-saturation-PROOF_STATUS.md`):

- **4.3149 is not a lower bound on Klarner's constant, and not an
  improvement on 4.498.** It bounds the growth of the majorants `B_N` from
  below; the true counts lie below the majorants. It is a floor under every
  upper bound that the unchanged map plus exact prefixes can certify; Part I's
  certificates (4.5233 … 4.498) and the Lean-verified 4.5235 lie above it.
  Tempting false readings, printed in the title-page box, Section 12 and
  Section 22.3: "λ ≥ 4.3149" and "4.3149 < 4.498 is a better bound". Both are
  false. It also does not locate the actual saturation constant, which could
  be higher.
- It does not determine Klarner's constant, does not resolve Bui's
  neighborhood-refinement question, and does not certify the repository's
  corpus.
- Ordinary written proofs, unrefereed, not Lean-verified; the
  implicit-function and localization arguments (Lemma 18.3, Section 18) need
  independent review before correctness or novelty is treated as settled.
- The checker proves finitely many rational inequalities and identities, not
  the analytic theorems; six scalar values are a consistency check.
- The size-18 marked profile is inherited from Part I, not re-enumerated for
  the manuscript (Part I's intake did regenerate it; it is not kernel-checked).
- Classification and saturation are for irreducible systems only; Theorem
  19.1 is a local positive-axis statement, and no global coefficient
  asymptotic `c_N ρ_N^{-n} n^{-3/2}` is claimed; the data-requirement
  consequences of Section 19.1 are conditional on a tail law.
- Bounded novelty assessment; Perron–Frobenius theory, the fold mechanism,
  inductive upper bounds (Winkler–Katoen), Newton methods
  (Stewart–Etessami–Yannakakis) and positive-system singularity theory
  (Drmota; its PDF was not read in full) are prior work, and the prefix
  construction, monotonicity, strict criterion and scalar limit 3 are Part
  I's.
- Explicitly unresolved: the exact fixed-map saturation constant; whether its
  crossing is interior; the reducible critical case; crossings at the true
  singularity; simultaneous `n, N` coefficient asymptotics; formal
  certification; convergence under neighborhood refinement.

## Relation to the formal project

The report does not live in, and is not part of, the Lean development; filing
it in the collection or citing the development confers no formal status on
it. What the project **has** formalized (namespace
`LeanProofs.KlarnerConstant`, files in
`Combinatorics/Polyominoes/KlarnerConstant/Lean/KlarnerConstant/`, no
`sorry`, project axiom or `native_decide`; audit in `Audit.lean`; the files
are unchanged between both pins and the placement commit `afb2d1227`):

| Statement in the report | Lean declaration | File:line |
|---|---|---|
| Bui's Lemma 4 for the actual marked counts, i.e. (7) coefficientwise (the manuscript calls it "imported") | `geometricPublishedBuiRecurrences : PublishedBuiRecurrences geometricCoefficientProfile` | `GeometricComplete.lean:63` |
| the five partitions (8), as equalities | `buiF_occurrenceCount_eq_g_add_p`, `buiG_…_eq_e_add_q`, `buiH_…_eq_d_add_s`, `buiR_…_eq_y_add_w`, `buiT_…_eq_x_add_v` | `GeometricLinear.lean:279–312` |
| `A_n ≤ G_n` (half of (5); `G_n ≤ nA_n` is not formalized) | `fixedPolyominoCount_le_geometricCoefficientProfile_g` | `GeometricProfile.lean:371` |
| supermultiplicativity and Fekete (3) | `fixedPolyominoCount_supermultiplicative`, `tendsto_realNthRoot_fixedPolyominoCount_growthSup` | `GeometricComplete.lean:97` (the latter) |
| λ ≤ 9047/2000 (the "old" bound, upper half of Theorem 7.1) | `certificate_isSupersolution`; `fixedPolyominoCount_le_9047_div_2000_pow`, `fixedPolyominoCount_real_le_9047_div_2000_pow`, `growthSup_fixedPolyominoCount_le_9047_div_2000` | `Certificate.lean:232`; `GeometricComplete.lean:69, 76, 88` |

Nothing else is formalized: not Lemma 3.2, Theorems 3.3–4.1, the size-18
table, anything in Sections 5–8, **nor anything in Part II** (Sections
12–28, including the 4.3149 barrier). The Lean endpoint chain is hard-wired
to `certificateZeta = 2000/9047`: `PrefixRecurrence.g_le_certificate`,
`PrefixRecurrence.g_lt_one`, `CoefficientProfile.g_lt_9047_div_2000_pow` and
`dominatedCoefficient_le_9047_div_2000_pow` (`Recurrence.lean:321, 327, 457,
477`). Only `buiIterate_le_supersolution` (`:283`) and
`PrefixRecurrence.le_supersolution` (`:309`) are ζ-generic, and
`growthSup_le_of_le_pow` (`Growth.lean:38`) is generic. A formal 4.498 needs a
prefix-corrected variant of that engine and a computable bridge to the
noncomputable `BuiNeighborhood.occurrenceCount` (`Patterns.lean:140`); the
`N = 7` certificate (4.5233, counts through size 7 only) would be a smaller
first target. Part II's own formalization plan (Section 23.4) puts its
finite rational obstruction (Lemma 22.1 plus the witness) before the
analytic layer; none of it exists. These are formalization targets, not
claims.

**Stale claims corrected in the text.** The delivered Part I status box and
Sections 1.3 and 2.3 call the geometric lemma "imported from Bui and the
pinned repository"; `[write]` notes there say that in ProveIt it is a Lean
theorem for the actual counts. The article's statement that the repository's
endpoint is 4.5235 is kept: it is the Lean-verified bound, and 4.498 stands
beside it as an unverified improvement. Part I's "the equality case is
deliberately not classified" (after Theorem 8.1), limitation N9 and research
questions 4 and 9 are re-scoped by dated pointers to Part II, not deleted.
The project's own READMEs, its research note and the walkthroughs are not
edited by this report.

**Bibliography added in the batch-36 write.** The source compares its bound
only with Bui's 4.5238 and the repository's 4.5235. A `[write]` paragraph in
Section 1.1 adds the history recorded in the project's research note: Eden
6.75; Klarner and Rivest 5, 4.83 and 4.649551; Barequet–Shalah 4.5252. The
Barequet–Shalah entry is copied from that note (Algorithmica 84 (2022),
3559–3586, doi:10.1007/s00453-022-00948-6). The note names Eden and
Klarner–Rivest without bibliographic data; the entries used (Eden, Proc.
Fourth Berkeley Symp. Math. Statist. Prob., Vol. 4, 1961, 223–239;
Klarner–Rivest, Canad. J. Math. 25 (1973), 585–602) were checked against
Project Euclid and Cambridge Core listings during that write. The research
note is itself a bibliography entry. Part II's bibliography is appended with
keys prefixed `sat` (the pinned report — Part I itself —, the project
directory, `code/model.py`, `data/profiles_18.csv`, Winkler–Katoen,
Stewart–Etessami–Yannakakis, Drmota); its entry for Bui's paper is the
existing `bui`.

**Neighbouring reports.** No other report in the collection treats Klarner's
constant; the parallelogram polyominoes of
`SetTheory/Cardinals/docs/reports/enumerative-combinatorics/skew-partition-continued-fractions/`
are unrelated mathematics.

## Intake verification

All runs were on copies outside the repository.

Part I (Appendix D.2):

- `code/verify.py --report …` passed ("ALL ARITHMETIC CHECKS PASSED.", 4.3 s
  at intake, 0.7 s on a rerun during the write) and printed exactly
  `data/verification.txt` (up to Windows line endings);
  `code/check_profile.py data/profiles_18.csv` reports "MATCH: sizes 1..18; 18
  unmarked and 306 marked counts."
- **Size-18 regeneration.** `code/enumerate.cpp` was compiled afresh
  (`c++ -O3 -std=c++17`, g++ 16.1.0, MinGW-w64 UCRT) and run as
  `enumerate 18` (8 min 23 s on one core). After CSV parsing its output equals
  `data/profiles_18.csv` in all 19 columns of all 18 rows (the raw files
  differ only in CRLF line endings). Fresh runs for sizes 11–14, 16 and 17
  (8 min 48 s) and `enumerate_direct 12` matched as well.
- An independent set-based Python enumerator, with pattern coordinates taken
  from the project's `Patterns.lean` rather than from this package, matched all
  10 unmarked and 170 marked entries through size 10.
- An independent transcription of the map from the project's research note
  reproduced the first defect (13), the `N = 18` residual minimum (≥ 9.9e−8),
  tail minimum (0.014724) and `v_G`, and confirmed the 4.5235 vector.
- Table 1 was compared with `Patterns.lean` entry by entry; `A_1 … A_18`
  equal OEIS A001168 (`A_18 = 1,540,820,542`, total through 18
  2,083,404,030).
- A 50-digit evaluation of `log 𝒞` gave 1.000668023145208770…, inside (20).
- The proofs of Lemma 3.2 and Theorems 3.3, 3.4, 3.6, 5.1, 6.3 and 8.2 were
  checked and that of Theorem 8.1 read; no gap was found. This is not an
  independent proof review.

**Re-scoped caveat.** `VALIDATION.md` (lines 31–35) says that no fresh size-18
run was made after the enumerators' final command-line changes. That run has
now been made from the final source, and matched. What remains: the
regeneration uses the same program and algorithm; the arithmetic checker
verifies arithmetic and necessary consistency conditions only; the
correctness of the enumeration rests on Proposition 4.2 and the
incremental-update argument together with this regeneration. The size-18
row also matters numerically: every `N = 18` residual is about 1e−7 and
`ζ^18 ≈ 1.8e−12`, so the certificate tolerates an error of only about
5.6 × 10^4 (relative 1e−5) in a single size-18 entry. The `N = 17` bound
4.5009 does not depend on that row.

Part II:

- At placement (`afb2d1227`), on a copy with the delivered layout:
  `verify.py --write` passed (17 inequalities, 323 defect and 95 partition
  checks, 6 brackets) and reproduced every output up to line endings;
  `discover.py` reproduced the integer witness.
- During this write, on a scratch copy rebuilt from the shipped files by the
  recipe below: the checker printed exactly
  `data/02-spectral-saturation-verification.txt` (0.5 s); `--write`
  reproduced `data/02-spectral-saturation-verification.json` and both tables
  byte for byte (up to CRLF); `discover.py` (NumPy) reproduced the integer
  witness, differing only in the floating field
  `discovery_eigenvalue_approx`.
- All eleven staged Part II files were compared with the delivery (identical),
  the delivered `data/profiles_18.csv` hashes to Part I's blob `82648328`,
  and Part I's `article.tex`, `code/model.py` and `data/profiles_18.csv` have
  the same blobs at the pin `74f7f5bdb` and at `afb2d1227`.
- The manuscript's display of the map (its Appendix A) agrees row for row
  with (6), and is printed once, there (Section 26).
- Part II's proofs were not independently reviewed at intake.

## Build

MiKTeX or TeX Live with newpx, amsmath, mathtools, geometry, microtype,
booktabs, longtable, enumitem, fancyhdr, titlesec, listings, tcolorbox, xurl,
hyperref and cleveref. `article.tex` `\input`s the five `tex/*.tex` tables
and `data/02-spectral-saturation-scalar_table.tex` and
`…-witness_table.tex` by relative path, so build from the report directory
(or copy `tex/` and those two files along):

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX 26.2, pdfTeX) has 61 pages: title page, contents
i–iii, Part I on pages 1–29 (Sections 1–11 and Appendices A–D), Part II on
pages 30–55 (Sections 12–28), references on pages 56–57. It has no errors,
undefined references or citations, multiply defined labels, duplicate
destinations, LaTeX or package warnings, or overfull boxes; the two underfull
boxes of the batch-36 build remain in narrow cells of the audit table
(Appendix C). Part II is placed after Part I's appendices so that no Part I
number changes; its sections continue at 12. Table numbers jump from 6 to 8:
Part I's uncaptioned audit longtable (Appendix C) steps the table counter,
as it already did. The title page was respaced (smaller vertical gaps) to
keep its status box, which gained the batch-40 note, on one page. The
manuscript's evidence table (Section 28) got a ragged-right first column,
removing one underfull box; no Part II text changed through that. Part I
alone built to 32 pages; the Part II manuscript as delivered to 27.

## Rerunning the checks

Every command runs from the report root under the shipped names for Part I,
but several scripts **rewrite shipped files**, so work on a copy of the
whole directory.

Part I:

- `code/verify.py --report data/verification.json` rewrites
  `data/verification.json` (with CRLF line endings on Windows);
- `code/make_tables.py` rewrites all five `tex/*.tex` (it hardcodes the
  "1–6" row value 4.523499228 in `tex/progress_table.tex` rather than
  deriving it);
- `code/discover_certificates.py` overwrites `data/upper_N*.json` and
  `data/dual_original.json`.

`code/research.py` writes `critical_estimates_new.json` (no arguments) or the
named output file into the working directory. `verify.py` and
`check_profile.py` need only the Python standard library; the exploratory
scripts need NumPy, SciPy and SymPy (`data/requirements-discovery.txt`).

On this machine (`python3` is spelled `py`; GNU make is not installed):

```sh
cp -r <report-dir> <scratch>/kfp && cd <scratch>/kfp
py code/verify.py --report data/verification.json
py code/check_profile.py data/profiles_18.csv
c++ -O3 -std=c++17 code/enumerate.cpp -o enumerate
./enumerate 11 > prefix11.csv && py code/check_profile.py prefix11.csv
./enumerate 18 > regenerated.csv && py code/check_profile.py regenerated.csv   # ~8–9 min
```

Where GNU make exists, the moved Makefile works from the (copied) report
root as `make -f code/Makefile verify` (or `tables`, `article.pdf`); it calls
`python3`.

Part II: **do not run its scripts in place.** Renamed, they cannot import
`bui_model` (shipped as `code/02-spectral-saturation-bui_model.py`), they
look for the unprefixed `data/bui_spectral_certificate.json`, and
`--write` would overwrite **Part I's** `data/verification.json` and write
stray `data/scalar_table.tex` and `data/witness_table.tex`;
`discover.py` rewrites the certificate. Rebuild the delivered layout in a
scratch directory instead (tested during the write):

```sh
R=<report-dir>; mkdir -p <scratch>/sat/code <scratch>/sat/data && cd <scratch>/sat
for f in bui_model verify discover; do cp $R/code/02-spectral-saturation-$f.py code/$f.py; done
cp $R/data/02-spectral-saturation-bui_spectral_certificate.json data/bui_spectral_certificate.json
cp $R/data/profiles_18.csv data/
py code/verify.py                    # prints data/02-spectral-saturation-verification.txt
py code/verify.py --write            # writes data/verification.json and the two tables in the copy
uv run --no-project --with numpy python code/discover.py   # optional; rewrites the copy's certificate
```

Compare the copy's `data/verification.json`, `scalar_table.tex` and
`witness_table.tex` with the shipped `data/02-spectral-saturation-*` files.
The checker needs only the Python standard library (3.10 or later).

## Delivered files that use delivery names or name unshipped files

- The Part I delivery README (not shipped) named `SHA256SUMS` and
  `article.pdf`, `Makefile` at the root, `requirements-discovery.txt` at the
  root and `python3`. `SHA256SUMS` is not shipped; `article.pdf` is a new
  build; the other two files are in `code/` and `data/`.
- `code/Makefile` is written for the package root (`python3 code/verify.py`,
  `article.tex`); see above.
- `VALIDATION.md` uses `python3`, describes the delivered 27-page PDF (with
  contact-sheet inspections that are not shipped), and states the size-18
  caveat re-scoped above.
- `article.tex` Section 9.2 speaks of "the archive" and its PDF and uses
  `python3`; a `[write]` note there gives the shipped layout.
- `research.py`'s default output and `discover_certificates.py`'s
  certificate files are not shipped outputs; see "Rerunning".
- `code/02-spectral-saturation-verify.py` and `…-discover.py` import
  `bui_model` and read and write `data/bui_spectral_certificate.json`,
  `data/verification.json`, `data/scalar_table.tex` and
  `data/witness_table.tex` (delivery names; the second is Part I's file in
  this directory); see "Rerunning".
- `code/02-spectral-saturation-build.sh` changes to its own directory and runs
  pdfLaTeX three times on `article.tex`, which is not there; use the build
  command above.
- `02-spectral-saturation-PROOF_STATUS.md` names the manuscript's unprefixed
  labels and `code/verify.py --write`; `02-spectral-saturation-SOURCES.md`
  says the table "was copied to `data/profiles_18.csv`" and names
  `code/bui_model.py`, the manuscript's `article.tex` and "the article
  appendix"; the shipped equivalents are Part I's `data/profiles_18.csv`,
  `code/02-spectral-saturation-bui_model.py`, and Part II with Section 26.
- In Part II's printed text the file names were changed to the shipped ones
  (Sections 20.3, 22.4, 23.1, 28) and `[write]` notes explain the change; the
  two `python3 code/verify.py` listings of Section 23.1 are kept as
  delivered, with a note that they assume the delivered layout.

## Provenance

- **Part I.** Pin `e21766d04c2b8a9b2cdba0cd43e563024b3bd1b9` (delivery README
  and `article.tex` preamble). The project was unchanged between the pin and
  the placement commit `1a1396d4d`. Placed in `1a1396d4d` as a new
  single-source report, first under
  `Combinatorics/Polyominoes/KlarnerConstant/Research/finite-prefix-corrections/`
  and then moved into this collection; the archive was delivered in
  `e13affd32` and retired in the placement commit. Manuscript 06 of batch 36.
  The batch-36 write prefixed labels (`eq:map` kept); added cleveref type
  hints on three labels; Sections 1.4 (notation) and 1.5 (formal status) and
  Appendix D; `[write]` notes in the title-page box, the "three levels" box,
  Section 1.1 (earlier bounds), Section 2.3 (twice), Section 4.4 (intake
  regeneration), Section 9.2 (layout), Section 9.3 (Lean plan), Research
  question 1 and three rows of Appendix C; four bibliography entries; `xurl`
  and two macros in the preamble. No delivered sentence was deleted and no
  statement changed.
- **Part II.** Manuscript 05 of batch 40, *When Exact Prefixes Stop
  Improving: Spectral saturation, sharp square-root laws, and a certified
  barrier for convolution majorants* (dated 28 September 2026). Pin
  `74f7f5bdba1aa728b340509701a0fa4e45e8dbf3` (with Part I's `article.tex`
  blob `4a021fb3`, unchanged at placement). Arrived in `017e6c0d8`, placed in
  `afb2d1227` as eleven `02-spectral-saturation-` files (the archive retired
  there); its `article.tex`, README, PDF and duplicate `data/profiles_18.csv`
  are not shipped and survive in the arrival commit.
- **What the batch-40 write changed.** Part II (Section 12 new; Sections
  13–28 the manuscript's whole text, including its abstract, printed in
  Section 12) appended after Part I's appendices; labels prefixed `kfp:sat:`;
  the renamings `z → ξ` and `λ → Λ`; file names in the text changed to the
  shipped ones; the manuscript's appendices printed as Sections 26–28, with
  its map display replaced by a pointer to (6); five `[write]` restatement
  notes where it re-proves Part I results (Lemma 14.1, Proposition 14.2,
  Lemma 14.4, Corollary 16.2, Section 20.1); `[write]` notes locating Part I's
  passages (Sections 13.2, 22.1, 26, 28), on the size-18 regeneration
  (Section 22.1), the tempting false readings (Section 22.3) and the file
  layout (Section 23.1); seven
  bibliography entries. In Part I: dated "Added 29 September 2026" pointers
  (title-page box, Sections 1.2, 1.5, 8.1, 8.2, research questions 4 and 9,
  conclusion, Appendix C row, Appendix D.1 and N9), contents entries for
  Part I and its appendices, the label `kfp:sec:conclusion`, four preamble
  macros, the PDF subject line and the title-page spacing. No Part I sentence
  was deleted and no Part I number changed.
- **Where the merge had to choose.** (1) Part II placed after Part I's
  appendices, not before them, because Part I's appendix tables are numbered.
  (2) The manuscript's restatements of Part I results are kept as stated
  (Part II's proofs cite them in its own formulation) and marked, with their
  different proofs kept as second proofs; only the map display, a pure
  duplicate of (6), is printed once. (3) The size variable renamed to `ξ`
  throughout Part II, and the Perron value to `Λ`. (4) The delivered
  `data/profiles_18.csv` is not staged; Part I's identical file serves.
