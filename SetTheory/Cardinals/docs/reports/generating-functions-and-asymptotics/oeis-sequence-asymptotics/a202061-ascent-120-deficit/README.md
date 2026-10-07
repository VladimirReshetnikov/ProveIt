# The Logarithmic Deficit of 120-Avoiding Ascent Sequences (OEIS A202061)

**From the order of growth to every fixed inverse-logarithmic order**

This research report was built on 2 October 2026 from five manuscripts of
batch 77. All five are dated 2 October 2026; the derivation notes of source 39
are dated 1 October. Each paper refines the one before it. Author lines: "A
proof and reproducible research report" (source 39) and "A proof and
reproducible research companion" (sources 41, 40, 42 and 38). No tool or person
is named.

| Source | Batch-77 manuscript | Archive (main file) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 39 | 39 | `oeis-a202061-report.zip` (`a202061-report.tex`, 517 lines, 11-page PDF) | none (search commits `63b9d6840`, `b4d1ba280` recorded; see below) | `f76fcb566` | Part I, Sections 1–9 |
| 41 | 41 | `oeis-a202061-sharp-deficit.zip` (`a202061-sharp-deficit.tex`, 429 lines) | none (checks its embedded copy of 39 against 39's manifest) | `f76fcb566` | Part II, Sections 10–15 |
| 40 | 40 | `oeis-a202061-second-order-report.zip` (`a202061-second-order.tex` + 5 `\input` files) | none (pins 41's manifest, SHA-256 `be1c7732…`) | `f76fcb566` | Part III, Sections 16–23 |
| 42 | 42 | `oeis-a202061-third-order-report.zip` (`a202061-third-order.tex` + 3 `\input` files) | none (pins 40's manifest, `a05af510…`) | `f76fcb566` | Part IV, Sections 24–29 |
| 38 | 38 | `oeis-a202061-allorders-report.zip` (`a202061-allorders.tex` + 4 `\input` files) | none (pins 42's manifest, `46235c0b…`) | `f76fcb566` | Part V, Sections 30–37 |

All five archives arrived in commit `096ee7b87` and survive there
(`git show 096ee7b87:docs/incoming/<archive>`). Each archive embeds its
predecessors byte for byte: 41 contains 39, 40 contains 41, 42 contains 40, and
38 contains 42. Archive 38 therefore carries all five papers. The placement
staged each paper's files once, from its own archive.

Every result, proof, remark, conjecture, open question and limitation of the
five manuscripts is printed. Two kinds of material are printed once. Source
41 restated four displays of source 39 verbatim: the walk equation, the jump
quadratic, the block formula and the first-hit bound. They appear in Part I
and Part II cites them. The later coefficient theorems also imply the earlier
ones, but every theorem is still printed, because each later paper imports
inputs proved only in the earlier ones. Part IV's proof is a separate route
to the J = 1 case of Part V (see "Where the merge had to choose").

**Status: AI-assisted, unrefereed, not formalized.** Each source calls its
audits "research verification, not journal peer review or formal
proof-assistant certification".

## Files

```
article.tex        the merged report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 81 pages (title page and contents 1–3,
                   Guide 4–9, Part I 9–20, II 20–29, III 29–45, IV 45–61, V 61–81)
README.md          this guide

Source 39 (Part I), files from oeis-a202061-report.zip
39-foundation-verification.md                      release verification note
39-foundation-audit-README.md                      audit directory readme
39-foundation-audit-audit.md                       independent audit
39-foundation-audit-integrated-report-review.md    review of the integrated report
39-foundation-derivation-README.md                 derivation-notes readme
39-foundation-derivation-operator_proof.md         six original proof notes (historical draft headers)
39-foundation-derivation-stretch_bound_proof.md
39-foundation-derivation-upper_scale_proof.md
39-foundation-derivation-log_scale_refinement.md
39-foundation-derivation-inverse_order_corollary.md
39-foundation-derivation-non_dfinite_corollary.md
39-foundation-derivation-source_scope.md           scoped source comparison (1 October 2026)
code/39-foundation-critical_certificate.py         exact critical-point identities, rational intervals
code/39-foundation-block_formula.py                positive binomial block formula vs operators
code/39-foundation-state_search.py                 normalized suffix recurrence (imported by the checks)
code/39-foundation-check_operators.py              state/operator coefficient comparison
code/39-foundation-check_height_walk.py            height walk vs normalized states and OEIS
code/39-foundation-check_word_states.py            literal-word transitions through length 10
code/39-foundation-check_narayana.py               fixed-gap polynomial transformation
code/39-foundation-check_staircase.py              staircase lengths, legality, tilt cancellation
code/39-foundation-audit-independent_checks.py     auditor's independent checks
code/39-foundation-audit-staircase_checks.py       auditor's (longer) staircase checks
code/39-foundation-verify_all.sh                   runs the seven author checks
code/39-foundation-build.sh                        delivered PDF build
data/39-foundation-certificate-output.txt          recorded outputs of the seven author checks
data/39-foundation-block-formula-output.txt
data/39-foundation-operator-check-output.txt
data/39-foundation-height-walk-check-output.txt
data/39-foundation-word-state-check-output.txt
data/39-foundation-narayana-check-output.txt
data/39-foundation-staircase-check-output.txt
data/39-foundation-audit-author-replay.txt         auditor's replay of the author checks
data/39-foundation-audit-independent-check-output.txt
data/39-foundation-audit-independent-staircase-output.txt
data/39-foundation-requirements.txt                sympy>=1.13, mpmath>=1.3

Source 41 (Part II), files from oeis-a202061-sharp-deficit.zip
41-sharp-verification.md                           release verification note
41-sharp-sharp_lower_bound.md                      source proof notes for the article
41-sharp-sharp_upper_bound.md
41-sharp-finite_height_radius.md
41-sharp-inverse_and_scope.md
41-sharp-kernel-kernel-asymptotics.md              kernel note; partly OUTSIDE the audit (see below)
41-sharp-source_scope.md                           scoped source check (2 October 2026)
41-sharp-audit-independent-audit.md                independent audit
41-sharp-audit-integrated-report-review.md         review of the integrated report
code/41-sharp-kernel-derive_constants.py           symbolic certificate for the kernel identities
code/41-sharp-audit-independent_identities.py      auditor's identity checks
code/41-sharp-check_manifest.py                    manifest checker (needs the unshipped SHA256SUMS)
code/41-sharp-verify_all.sh                        delivered suite (runs the embedded foundation too)
code/41-sharp-build.sh                             delivered PDF build
code/41-sharp-make_release.py                      delivered release script (writes files; do not run here)
data/41-sharp-kernel-certificate-output.txt        recorded output of derive_constants.py
data/41-sharp-audit-independent-identities-output.txt
data/41-sharp-producer-replay.txt                  recorded run of verify_all.sh
data/41-sharp-requirements.txt                     sympy>=1.12, mpmath>=1.3

Source 40 (Part III), files from oeis-a202061-second-order-report.zip
40-second-verification.md                          release verification note
40-second-proofs-coefficient-lower-second-order.md source proof notes
40-second-proofs-coefficient-upper-second-order.md
40-second-proofs-finite-height-explicit-constant.md
40-second-audit-README.md                          audit directory readme
40-second-audit-lower-construction-audit.md        audits of the three proofs
40-second-audit-upper-calibration-audit.md
40-second-audit-finite-height-constant-audit.md
40-second-audit-integrated-report-review.md        review of the integrated report
code/40-second-checks-second_order_checks.py       exact second-order checks
code/40-second-checks-check_dependencies.py        checks the embedded copy of 41 against its pinned manifest
code/40-second-audit-check_finite_height_amplitude.py  auditor's amplitude and c* check
code/40-second-check_manifest.py                   manifest checker
code/40-second-verify_all.sh                       delivered suite
code/40-second-build.sh                            delivered PDF build
code/40-second-make_release.py                     delivered release script (writes files; do not run here)
data/40-second-producer-replay.txt                 recorded run of verify_all.sh
data/40-second-audit-finite-height-amplitude-output.txt
data/40-second-audit-foundation-identities-replay.txt  same bytes as data/41-sharp-audit-independent-identities-output.txt
data/40-second-requirements.txt                    sympy

Source 42 (Part IV), files from oeis-a202061-third-order-report.zip
42-third-verification.md                           release verification note
42-third-proofs-coefficient-upper.md               SAME BYTES as 42-third-audit-one-sided-next-constant-proof.md (see below)
42-third-proofs-normalized-kernel-lower.md         lower-bound source note (header: "NOT independently audited")
42-third-audit-one-sided-next-constant-proof.md    auditor's completed upper-bound proof
42-third-audit-lower-construction-audit.md         audit of the lower construction (supersedes that header)
42-third-audit-integrated-report-review.md         review of the integrated report
42-third-audit-producer-visual-qa.md               page-render QA of the delivered PDF
code/42-third-checks-third_order_checks.py         exact third-order checks
code/42-third-checks-check_dependencies.py         checks the embedded copy of 40 against its pinned manifest
code/42-third-checks-check_proof_sources.py        checks proof notes against an unshipped hash ledger
code/42-third-audit-check_constants.py             auditor's constant check (kappa, kappa_inv, ...)
code/42-third-check_manifest.py                    manifest checker
code/42-third-verify_all.sh                        delivered suite
code/42-third-build.sh                             delivered PDF build
code/42-third-make_release.py                      delivered release script (writes files; do not run here)
data/42-third-producer-replay.txt                  recorded run of verify_all.sh
data/42-third-audit-constants-output.txt
data/42-third-requirements.txt                     sympy, mpmath>=1.3

Source 38 (Part V), files from oeis-a202061-allorders-report.zip
38-allorders-verification.md                       release verification note
38-allorders-proofs-classical-action-reduction.md  source proof notes
38-allorders-proofs-action-expansion.md            (labels P3, P4 "generated-only"; see the polynomial audit)
38-allorders-proofs-inverse-scaling.md
38-allorders-audit-audit.md                        independent analytic audit
38-allorders-audit-polynomial-audit.md             independent check of P3, P4
38-allorders-audit-integrated-report-review.md     review of the integrated report
38-allorders-audit-visual-qa.md                    page-render QA of the delivered PDF
code/38-allorders-checks-generate_action_polynomials.py  universal recurrence, P0..P4
code/38-allorders-checks-verify_action_coefficients.py   direct substitution through P2
code/38-allorders-checks-verify_inverse_scaling.py       inverse covariance identities
code/38-allorders-checks-check_hierarchy.py              hierarchy identities
code/38-allorders-checks-check_dependencies.py           checks the embedded copy of 42 against its pinned manifest
code/38-allorders-checks-check_proof_sources.py          checks proof notes against an unshipped hash ledger
code/38-allorders-audit-independent_checks.py            auditor's checks (local p_j, P1, P2, quadratures)
code/38-allorders-audit-verify_p3_p4_direct.py           independent derivation of P0..P4
code/38-allorders-audit-verify_p3_p4_direct-original.py  the same, with the producer's workspace path
code/38-allorders-check_manifest.py                manifest checker
code/38-allorders-verify_all.sh                    delivered suite (runs the whole chain)
code/38-allorders-build.sh                         delivered PDF build
code/38-allorders-make_release.py                  delivered release script (writes files; do not run here)
data/38-allorders-producer-replay.txt              recorded run of verify_all.sh
data/38-allorders-audit-independent-checks-output.txt
data/38-allorders-audit-polynomial-verification-output.txt
data/38-allorders-audit-inverse-replay-output.txt
data/38-allorders-audit-integrated-review-replay.txt
data/38-allorders-requirements.txt                 sympy==1.14.0, mpmath==1.3.0
```

That is 122 files: 45 delivered Markdown notes, 46 files in `code/`, 28 in
`data/`, and the three report files. Every delivered file is byte-identical to
its archive. The four `check_manifest.py` files are one file (same bytes).

**Delivery names.** A file at `<dir>/<name>` in archive NN is shipped as
`NN-<slug>-<dir>-<name>`, with slugs `foundation` (39), `sharp` (41), `second`
(40), `third` (42) and `allorders` (38). Scripts and build files go in `code/`,
recorded outputs and requirements in `data/`, and Markdown notes in the root.
Example: `checks/check_dependencies.py` of archive 38 is
`code/38-allorders-checks-check_dependencies.py`.

The delivered texts still use their delivery names throughout: the notes,
audits, `verification.md` files, scripts and shell suites. They also name files
that are not shipped:

- the five PDFs (`a202061-report.pdf`, …, `a202061-allorders.pdf`; the notes
  give their delivered page counts, for example 11 pages for source 39 and 20
  for source 38);
- every `SHA256SUMS` manifest, read by each `check_manifest.py` and
  `check_dependencies.py`;
- the audit hash ledgers (`audit/source-sha256.txt` of 39,
  `audit/audited-source-sha256.txt` of 40, `audit/*-sha256.txt` of 42 and 38).
  These are read by `check_proof_sources.py` and `make_release.py`;
- the embedded predecessor trees `foundation/` and `dependency/…/`;
- the producer's workspace paths (`/workspace/shared/…`,
  `../a202061-third-order-research/root-sharp-upper-plan.md`,
  `../a202061-allorders-research/…`).

All of these survive in `096ee7b87`. Every entry of the audit hash ledgers was
checked at intake against the shipped file of the same name and matched, so
the audits were made on the shipped bytes.

## Labels

Every label in `article.tex` carries the prefix `a61:`. The Part prefixes are
`a61:fd:` (Part I, source 39), `a61:sh:` (II, 41), `a61:o2:` (III, 40),
`a61:o3:` (IV, 42) and `a61:ao:` (V, 38). Labels already unique in their
source (`low:`, `upp:`, `rad:`, `up3:`, `lo3:`, `inv3:`) also carry the Part
prefix, for example `a61:o3:up3:section`. The base manuscript had 33 labels
and the five sources 252. The report has **267**:

- the 252 source labels, less the four that source 41 used for its restated
  displays (`eq:walk`, `eq:quad`, `eq:binomial`, `eq:hit`; references to them
  now point to Part I);
- five Part labels (`a61:part:*`) and nine Guide labels (`a61:guide*`);
- five section labels added for cross-references (`a61:fd:sec:recurrence`,
  `a61:fd:sec:walk`, `a61:fd:sec:nondfinite`, `a61:fd:sec:closing`,
  `a61:sh:sec:inputs`).

No formalization ledger maps any of these labels.

## What the report claims

- **Part I (39).** An exact normalized state recurrence for 120-avoiding
  ascent sequences. A positive height-walk representation with an explicit
  positive binomial block formula. An exactly certified critical point
  (α a root of 7α³+14α²−7α−1). The theorem
  `μ^n e^{−CΦ(n)} ≤ a_n ≤ C μ^n e^{−cΦ(n)}`, with `Φ(n) = n^{1/3}(log n)^{2/3}`,
  at every large n. Corollaries:
  - no equivalent `C₀ μ^n exp(−d n^γ) n^g` with γ ≥ 1/3, which rules out the
    pure n^{3/8} stretch that Conway–Conway–Elvey Price–Guttmann estimated
    numerically;
  - `N(Y) = log Y/log μ + Θ((log Y)^{1/3}(log log Y)^{2/3})`;
  - the generating function is not D-finite (by G-function regularity and
    Pringsheim).
- **Part II (41).** `D_n/Φ(n) → C⋆ = (3π²α²/(2v))^{1/3} = 2.2326253076…`,
  where `D_n = n log μ − log a_n`. The finite-height radius shift
  `log(ρ_H/ρ) ~ (α/2) log H/H`. The leading inverse constant
  `C⋆ λ^{−4/3} = 0.8935682576…`.
- **Part III (40).** `D_n = C⋆F + (7C⋆/3) F log L/L + O(F/L)`, with `L = log n`
  and `F = Φ(n)`. The corresponding inverse. The finite-height radius with
  explicit constant `c⋆ = 0.8667962458…`. A conditional conjecture for the next
  constant.
- **Part IV (42).** The next term, `C⋆κ F/L + o(F/L)` with
  `κ = log Y₀ − 2 log 3 + 2c⋆ = −1.9401481831…`; this proves Part III's
  conjecture. The inverse constant `κ_inv = −2.3980035405…`. A variational
  (classical-action) statement at that precision.
- **Part V (38).** For every fixed J,
  `D_n/(C⋆F) = Σ_{j≤J} P_j(κ + (7/3) log L)/L^j + o(L^{−J})`. The `P_j` are
  universal polynomials of degree j with leading coefficient
  `binom(2/3, j)(3/2)^j`. A finite beta-moment recurrence generates them, and
  P₁ to P₄ are explicit (P₃ and P₄ involve π² and ζ(3)). Part V also gives a
  tunable reduction to a classical action and the inverse expansion to every
  fixed order.

**What Part V does not imply.** Part V implies the coefficient and inverse
theorems of Parts I–IV (J = 0, 1), but not three of their results:

- the non-D-finiteness of Part I;
- the exact walk representation of Part I, which Part V imports;
- the finite-height radius theorems of Parts II and III.

Part V is not self-contained, and it says so. It imports inputs from all four
earlier Parts.

## What the report does not claim

These non-claims come from all five sources, and all are kept in the text.

- No multiplicative equivalent for a_n: the remainder in log a_n may diverge at
  every fixed order.
- No amplitude, power-law prefactor or fluctuation determinant.
- No convergent series, and no exponentially complete transseries.
- No uniformity in J.
- No effective constants or thresholds, no finite-data crossover threshold,
  and no exact integer rounding rule for N(Y).
- Priority is not established. The literature checks were scoped. The gap
  reduction may overlap the unpublished polynomial-time enumeration mentioned
  by Conway–Conway–Elvey Price–Guttmann.
- The finite computations supplement the proofs. They are not curve fits, and
  they do not certify finite thresholds.

Two notes about particular files:

- **Source 41's kernel note** (`41-sharp-kernel-kernel-asymptotics.md`)
  contains stronger local theorems: full local equivalents and amplitudes.
  Its own header places them **outside the audit boundary**. The report
  neither prints nor cites them, and they are not claimed here.
- **Source 42's two upper-bound files are the same document.**
  `42-third-proofs-coefficient-upper.md` and
  `42-third-audit-one-sided-next-constant-proof.md` are byte-identical
  (17,038 B). The text is titled "Independent proof audit". It is the
  auditor's completion of a plan file in the producer's workspace, which was
  not delivered. The upper-bound "source note" is therefore the auditor's
  text.

## Relation to neighbouring reports and to the repository

- **Same family, same directory.** Three reports cover the three
  length-3-pattern classes of ascent sequences studied by Conway, Conway,
  Elvey Price and Guttmann (EJC 29(4), 2022, P4.25):
  [`a202058-ascent-000-growth`](../a202058-ascent-000-growth/) (000-avoiding;
  factorial growth), [`a202062-ascent-201-enumeration`](../a202062-ascent-201-enumeration/)
  (201-avoiding; cubic generating function, `μ^n n^{−9/2}` asymptotics) and this
  report. A202061 and A202062 share μ. *[Dated note, 7 October 2026, batch-102
  reciprocal note: the 100- and 110-avoiding classes of the same paper
  (A202059, A202060), which grow factorially with
  `log aₙ = n log n − 2n log log n + O(n)` (for A202059 with the sharp
  linear constant, `log 2 − 1`), are treated in
  [`a202059-ascent-100-110-growth`](../a202059-ascent-100-110-growth/)
  (batch 102, bundle Reports 243 and 241), so the "three reports" above are
  now four; no shared theorem.]*
- **Same method, other sequences** (dated note, 5 October 2026, batch 104).
  [`a279551-inversion-log-deficit`](../a279551-inversion-log-deficit/)
  treats the Britt–Beaton inversion-sequence classes A279551 and A279556 by
  commitment trees and proves the same three kinds of statement as Parts
  I–III here: the order `F = n^{1/3}(log n)^{2/3}`, the sharp constant
  `σ_D = (3π²/(2D))^{1/3}`, and the second term with coefficient `7σ_D/3`.
  Its local root `(½ log p + log log p + c)/p` matches Part III's row
  threshold `κ(r)/r` here (measured in `Ψ`, which carries a factor `1/α`),
  and its potential `1/3 + (7/6) log L/L` matches Part III's
  `B_n = α/3 + (7α/6) log L/L + O(1/L)`. Its Remark 1.2 excludes
  Britt–Beaton's numerical `n^{3/8}` forms as Part I here excludes CCEG's.
  Different sequences, constants in another normalization, no
  cross-citation between the source manuscripts; its next constant (the
  analogue of Part IV's `κ`) is open there, with Parts IV–V here as the
  model. A dated note after Theorem 16.1 (`a61:o2:thm:main`) says so.
- **Second route to μ.** The A202062 report, in its section "A consequence for
  120 avoidance", derives `lim a_n^{1/n} = μ` for A202061. It uses CCEG's
  Theorem 4 (equal growth rates) and its own proof of the Guttmann–Kotěšovec
  cubic. That route gives the growth rate only. Part I proves the rate
  directly, with the deficit. A dated note after Part I's Corollary 1.2 says
  so.
- **Transseries volume.** Part V's local cutoff equation (a = 1, b = −1) and
  peak equation (a = 3, b = −7/2) are instances of the Lambert core
  `p0:thm:lambert-core` in
  `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/`.
  The inverse corollaries of all five Parts are instances of its
  `p0:thm:perturbed-inversion` and `p0:thm:staircase`. The report claims no
  novelty for these steps.
- **No formal status.** No Lean or Rocq declaration in the repository states
  any result of this report. Placement in the `SetTheory/Cardinals` report
  collection confers no formal status.
- **Stale repository statement.** Source 39's source note (1 October 2026,
  search commits `63b9d6840`, `b4d1ba280`) found no A202061 material in
  ProveIt. That was true then. The note is kept as provenance; this report is
  now that material.

## Where the merge had to choose

- **Order of Parts.** The Parts follow the chain order 39, 41, 40, 42, 38, so
  every Part cites only earlier Parts. Source 39's Section k is Section k here.
  The other sources' sections are shifted by 9 (41), 15 (40), 23 (42) and 29
  (38). Equations are now numbered within sections.
- **Source 41's restated displays.** They are replaced by references to
  Part I. Sources 40, 42 and 38 restate inputs in their own notation, under
  labels their proofs cite. Those restatements are kept, each with a dated note
  naming where the input is proved.
- **Citations.** References to the earlier papers of the chain (`\cite{Foundation}`,
  `Sharp`, `Second`, `Third`) became references to Parts, and those
  bibliography entries were dropped. Sources 40, 42 and 38 cite source 39
  under a wrong title, "A202061 positive height-walk and logarithmic deficit
  foundation"; that title no longer appears. The OEIS entry is that of source
  39. It says "Inspected 2 October 2026", while source 39's source note records
  the check on 1 October.
- **Dated `[write, 2 October 2026]` notes** were added at these places:
  - Part I: after Corollary 1.2, on the status of its paragraph and the second
    route to μ; and at the end of Section 9, on the status of its open
    questions.
  - Part II: in Section 10, on the restated displays; at the end of Section 15
    (the questions left open); and after the radius proof in Section 14 (the
    refinement in Part III).
  - Part III: at the start of its inputs section, naming where each input is
    proved; after the conjecture (proved in Part IV; it uses Y for Y₀); and
    after "What the theorem does not determine".
  - Part IV: after Theorem 24.1 (it proves the conjecture and is the J = 1 case
    of Part V); after its inputs; after its inverse corollary; and at its
    closing paragraph.
  - Part V: after its abstract, which says "entire dominant
    inverse-logarithmic sector"; the note qualifies this to every fixed finite
    J, not uniform in J, and not a transseries. Also after Theorem 30.1 (what
    it does and does not imply); at the definition of B (the false reading
    below); at the two Lambert-type equations; and at the end of the scope
    section.
- **Removed.** Only the five title blocks and bibliographies (merged into
  one), and source 38's table of contents. Each source's abstract is printed
  at the head of its Part.
- **Notation.** No symbol was renamed. The Guide has a table that fixes each
  letter's meaning in each Part. Watch for these readings:
  - **C⋆.** It is written `C_⋆` (Parts II, III), `C_*` (Part III's conjecture
    section and Part IV) and plain `C` (Part V). In Part I, `c` and `C` are
    unspecified constants.
  - **κ.** It is 0.2830… in Parts I–II, a coordinate of the critical entropy
    point. In Parts IV–V it is −1.9401…, the third-order constant.
  - **z and t.** In Part I they are variables. In Parts II–V they are the
    critical constants, and the variables are u and T.
  - **B.** In Part V, `B = κ + (7/3) log log n` is **not a constant**.
    Elsewhere B is a block coefficient (Part I), a calibration bound
    (Part II) or Part IV's inverse constant `B_* = 0.8935…`.
  - **Y.** In Part III's conjecture section, Y is the constant Y₀, not the
    threshold target.
  - **The inverse variable.** `log Y` is called L, S or T in Parts II, III and
    IV. Part V uses `T = log p`, `S = log T`.

## Build

```
mkdir <scratch>; cp article.tex <scratch>/; cd <scratch>
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build uses pdflatex with the standard AMS packages, `booktabs`,
`longtable`, `array`, `geometry`, `hyperref`, `microtype` and Latin Modern. It
gives 81 pages (80 before the batch-104 reciprocal note), with no errors, undefined references, multiply defined labels,
duplicate destinations or overfull boxes. The three `\pdfmapfile` lines come
from source 39; on MiKTeX they produce several hundred harmless "fontmap
entry … already exists" messages. Copy back only `article.pdf`.

## Rerunning the checks

The delivered suites expect their delivery layout: `SHA256SUMS`, the
embedded `foundation/` and `dependency/` trees, and the unprefixed names.
They do not run from `code/`. Run them on a fresh extraction of archive 38,
which carries all five packages, in a scratch directory:

```
git -C C:/ProveIt show 096ee7b87:docs/incoming/oeis-a202061-allorders-report.zip > a61.zip
unzip -q a61.zip && cd oeis-a202061-allorders-report
bash verify_all.sh            # whole chain; or run each package's verify_all.sh in
                              # dependency/third-order/..., .../second-order, .../sharp-deficit,
                              # .../sharp-deficit/foundation
```

The suites call `python`. On this Windows machine bare `python` may hit the
Store alias, so run the steps one by one with `py` (or `uv run --no-project
--with sympy==1.14.0 --with mpmath==1.3.0 python`). Never run
`make_release.py` or `build.sh` inside the repository. The release scripts
rewrite `SHA256SUMS` and write a zip and a `.sha256` file. The build scripts
write the PDF and a `.build/` directory. The verification scripts only print.

Nothing was replayed in full at intake. The machine was at 100 % CPU with
under 1 GB free, and each step ran with a 170 s timeout on a copy of
archive 38 (Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0). The delivered runs
used Python 3.12.14.

| Package | Result at intake |
|---|---|
| 39 | Manifest PASS. The seven author checks PASS, with output identical to the recorded `*-output.txt`. `audit/independent_checks.py` timed out with no output. `audit/staircase_checks.py` was not run (its README calls it "deliberately more extensive"). |
| 41 | Manifest PASS. `kernel/derive_constants.py` identical to its recorded output (157 s). `audit/independent_identities.py` timed out with no output; its recorded output has 8 PASS lines. |
| 40 | Manifest, dependency, `second_order_checks.py` and the amplitude audit all PASS, matching the recorded replay. |
| 42 | Manifest, dependency, proof-source, `third_order_checks.py` and `check_constants.py` all PASS, matching the replay. |
| 38 | Manifest (158 hashes), dependency, proof-source, `verify_action_coefficients.py`, `verify_inverse_scaling.py` and `check_hierarchy.py` PASS. `audit/verify_p3_p4_direct.py` PASS in 72 s (differs only in the interpreter-version line). `generate_action_polynomials.py 4` timed out with a matching partial output; with argument 3 it passes in 36 s. `audit/independent_checks.py` timed out after the T = 200 quadrature row, matching the replay up to there. |

An independent intake script confirmed several identities and values. It
checked Part V's derivative identity `P′_{j+1} = (1 − 3j/2)P_j + (7/2)P′_j` for
j ≤ 3, and the leading coefficients `binom(2/3, j)(3/2)^j` for j ≤ 4. It also
checked the four beta-log moments, and μ, α, v, c⋆, C⋆, κ, C⋆κ, B⋆ and κ_inv
to 25 digits. The only check of P₃ and P₄ independent of their generator is
`verify_p3_p4_direct.py`; P₃ and P₄ enter no theorem except as explicit
checked polynomials.

## Not shipped

These files are all in `096ee7b87`:

- the five delivered PDFs and README files;
- the member manuscripts, sources 41, 40, 42 and 38, with their `\input`
  files. They are printed in `article.tex`, and source 39's manuscript is the
  base of `article.tex`;
- every `SHA256SUMS` manifest and audit hash ledger, all verified at intake;
- the 317 nested copies inside archives 41, 40, 42 and 38.

Source 39's delivered README is replaced by this file. Its content is kept
here and in Part I: the claims, the non-claims, the attribution to OEIS,
Conway–Conway–Elvey Price–Guttmann and Garoufalidis–Bellissard, and the
remark that the proof does not assume that all D-finite functions have
regular singular points. No heavy regenerable artifact was excluded from this
report.
