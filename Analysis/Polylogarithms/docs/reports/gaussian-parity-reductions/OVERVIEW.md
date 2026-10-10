# Gaussian parity reductions: overview of the sources

Reconciliation note, 2026-10-09. `README.md` here is the base delivery's own
README, kept as delivered; this file says how the merged report's sources
fit together. Delivered files are not edited. All four sources are unrefereed
research continuations (16 says AI-assisted; none claims peer review), and
nothing is formalized. Placement `d4dead2c6b`; the status of every claim and
correction of the PolyLog programme is kept in the project README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects).

All four continue the unified manuscript under `../../manuscript/` (pinned at
`afed07429d` (14, 17) or `0599fe867a` (15, 16); the manuscript is unchanged from
both pins to the placement). They cite its labels (`gauss:eq:*`, `mixed:*`,
`bloch:eq:sgP3`, `integral:neg:cubic`, `stieltjes:prop:jetrank`, `tower:thm:rank`).
That manuscript is maintained separately; nothing here edits it.

## Files by source

**14 `polylogarithms_exact_reductions_20261009`: the base** (unprefixed manuscript)

- `article.tex` (delivered `article/polylogarithms_exact_reductions.tex`):
  *From Polylogarithm Conjectures to Exact Reductions*; `references.tex`;
  `sections/01_scope.tex` … `sections/07_research.tex`
- `README.md` (delivered)
- `code/14-exact-reductions-*` (the `run_checks.py` driver, `shuffle_certificates.py`,
  `verify_s4_candidate.py`, `make_moment_figure.py`, the `Makefile`, and the
  components `depth-`, `ladders-`, `moments-` with their READMEs)
- `data/14-exact-reductions-*` (shuffle normal forms, validation reports, the
  integration register as CSV and JSON, the source manifest, the 112-digit cubic
  certificate, the Gaussian table through weight 12, figure data and caption)
- `figures/14-exact-reductions-moment_asymptotics.{pdf,png}`
- `14-exact-reductions-analytic_cross_review.md`,
  `14-exact-reductions-loggamma_sources.md`

**Members**, prefixed; their manuscripts and READMEs are not staged (retrievable
from their arrival commits):

- **15** `polylogarithm_research_20261009` (`cbe9e9b599`), *Parity Reductions and
  Rational Distribution Ranks*: `15-parity-ranks-integration_notes.md`,
  `code/15-parity-ranks-*`, `data/15-parity-ranks-*`.
- **16** `ProveIt_Gaussian_Polylogarithms_Research` (`eaad5886ed`), *Gaussian
  reductions and certified polylogarithm evaluation*:
  `16-gaussian-certified-INTEGRATION.md`,
  `16-gaussian-certified-editorial-ledger-addendum.md`, `code/16-gaussian-certified-*`
  (with the delivered `.gitignore`, inert under its prefixed name),
  `data/16-gaussian-certified-*` (the exact weight-8 and weight-10 tables are
  `weight8.tex`, `weight10.tex`).
- **17** `proveit_polylog_gap_reductions_2026-10-09` (`eaad5886ed`), *Mixed-Point
  Elimination and Certified Parity Reductions*: `17-gap-reductions-INTEGRATION.md`,
  `17-gap-reductions-manuscript_supplement.tex` (a proposed manuscript fragment,
  `gapcont:` labels), `code/17-gap-reductions-*`, `data/17-gap-reductions-*`
  (`MANIFEST.sha256` staged as delivered; the compiled `parity_tables.pdf` is not
  staged, its source `parity_tables_document.tex` and `parity_tables.tex` are).

## What was delivered more than once

| Result | 14 | 15 | 16 | 17 | Note |
|---|---|---|---|---|---|
| depth-two parity formula on the unit circle, every weight (a specialization of Panzer 2017) | ✓ `thm:binomial-parity` | ✓ `thm:gaussian` | ✓ `thm:parity` | ✓ `thm:parity` (solver, determinant `2^⌊w/2⌋`) | four derivations; all credit Panzer |
| the five weight-six Gaussian doubles `gauss:eq:g51` … `g15` | ✓ | ✓ | ✓ | ✓ | coefficients unchanged |
| the weight-five relation `gauss:eq:wt5-sporadic` = 960·(1,4)-shuffle − 224·(2,3)-shuffle | ✓ | ✓ | ✓ | ✓ | |
| both shuffle rows: the four weight-five `g` span at most two directions mod `π⁵, Gζ(3), β(4)log2` | ✓ | ✓ | (uses both rows only in the `π`-free combination, for every odd weight: `thm:oddfamily`) | ✓ | |
| infinite height-one family `g_{2m−1,1}` | | ✓ `cor:edge` | ✓ `cor:heightone` | ✓ (all angles, `thm:allangle`) | |
| Gaussian tables at higher weight | through 12 (JSON, TeX) | through 12 (66 formulas) | 8 and 10 (16 rows) | 2–8, Gaussian and Eisenstein (56) | |
| `Li₁,₁(z,1/z) = −Li₂(z/(z−1))` (`mixed:eq:gauss-w2`, `mixed:eq:eis-w2`) | | ✓ `prop:Li11` | | ✓ (`D₁₁ = F₁₁ + Li₂`, Landen) | the `a = b = 1` case of the batch-138 formula (X1) |
| the four mixed constants `Re Li₄,₁`, `Im Li₅,₁` at `(i,−i)`, `(ρ²,ρ)` | ✓ (labelled inherited) | ✓ `thm:four` | | ✓ | **repeat** of 10 (batch 138, X1), see below |
| all-weight reduction of `Li_{a,b}(z,1/z)` to `Li_{r,s}(z,1)` | (inherited) | ✓ `thm:mixed` (a parity form) | | ✓ `thm:gap`, plus `T² = I` | `thm:gap` is 10's formula term for term |
| `S₄` reduction (`gauss:eq:S4-closed`) | open; equivalent short form | open; `S_p = Im Li_{p,1}(i,1) + Im Li_{p,1}(i,−1)` | open; residual enclosure | – | **open in all** |

Single-source parts: 14's formal shuffle count at every weight and depth
(`thm:witt`, generalizing the weight-six rank seven of `corpus-corrections` C11),
the three weight-four Gaussian triples and the index family `(2,1,…,1)`
(`thm:one-two`), the supergolden and `x⁴+x−1` trilogarithm ladders with the
complementary-power theorem, and the log-gamma moment analysis (late-coefficient
asymptotic, divergence, effective remainder, 112-digit cubic certificate);
16's Chebyshev-moment evaluator (geometric error uniform through `xy = 1`, sharp
kernel rate, 89 interval certificates) and its infinite odd-weight shuffle family;
17's integral involution, all-angle last-index-one identities and positive-measure
midpoint evaluator (six rational rectangles below `10⁻⁷⁰`); 15's weighted
distribution presentation (below).

**Base: 14.** The parity formulas are equally general (every weight, every
point of the unit circle but 1, boundary cases included); 14 proves the most of
the manuscript's numerical candidates (eleven: the six above, three triples, two
ladders), alone gives the all-depth formal count, and alone credits the batch-138
results it re-derives. Credit all four for the shared results.

## Repeats of results already placed

- The four mixed constants and the all-weight reduction of `Li_{a,b}(z,1/z)` were
  proved by 10 (batch 138; `../corpus-corrections/10-exact-structure-CORRECTIONS.txt`
  item 1; `thm:mixed` in `../rational-grid-distribution-ranks/article.tex`,
  section `sec:mixed`). 14 says so; 15 and 17 do not cite it. 17's `thm:gap` with
  its correction `C_{a,b}` (`eq:Cdef`) is 10's formula term for term. Intake checked
  that the printed constants agree (identical up to `ζ(2) = π²/6`, `ζ(4) = π⁴/90`)
  and recomputed all four.
- 15's rank theorems (`thm:jet-rank`, `cor:stieltjes-rank`, `cor:parameter-rank`)
  are a fourth proof of the ranks of `../rational-grid-distribution-ranks/`. Its
  primitive-residue `Q`-basis for nonzero integer exponents is the rational form
  of that report's top-denominator basis (`thm:dist-normal-form` and the paragraph
  after `eq:dist-top-coordinate`), with explicit rational elimination certificates.

## Caveats

- Every source says it proves no independence, transcendence or minimal depth;
  formal quotient dimensions are not numerical dimensions; numerical residuals
  (including 16's enclosure of the `S₄` residual) are not proofs.
- `S₄` stays open; see also question 1 of `../alternating-harmonic-polylogarithms/`.
- 14 attributes the cubic log-gamma moment to Bailey–Borwein–Borwein (Ramanujan J.
  36 (2015), Thm 6) and the fixed-order moment expansion to Amdeberhan et al.
  (Proc. AMS 139 (2011), Thm 8.1); these literature statements were not checked
  at intake.
- The prefixed scripts still name their delivered paths and write their outputs
  in place; `article.tex` expects `figures/moment_asymptotics.pdf` under its
  delivered name. Rerun on copies in a scratch directory under the delivered names.

## Later sources (batch 140, 9 October 2026)

Dated note, 2026-10-09. Two more continuations of the same manuscript chapter
arrived after this report was placed and are added to it as sources 18 and 19,
prefixed like 15–17 (placement `49a6356865`). Their
manuscripts, PDFs and READMEs are not staged; they are retrievable from the
arrival commit `412dbd0048`. Both were pinned before this report existed (18 at
`afed07429d`, 19 at `09812e81e5`; the manuscript is unchanged from both pins),
so neither cites 14–17. Both are unrefereed; 19's provenance record says it was
prepared with ChatGPT; neither claims a proof-assistant check.

**18 `polylogarithms_gaussian_continuation`**, *Gaussian Double Polylogarithms:
Exact Reductions, Signed Kernels, and a Unique-Zero Theorem* (23 pp.):
`18-signed-kernels-{INTEGRATION,RESULTS,VALIDATION}.md`, the proposed manuscript
fragments `18-signed-kernels-gaussian-continuation-section.tex` and
`18-signed-kernels-bibliography-items.tex` (`gcc:` labels), `code/18-signed-kernels-*`
(with the delivered `.gitignore`, inert under its prefixed name),
`data/18-signed-kernels-*` (the 64 even-weight formulas through weight 16 as JSON
and TeX, interval certificates, the `S₄` enclosure and obstruction witness, the
odd-weight rank census, `PROVENANCE.json`, `source-status.json`, and
`MANIFEST.sha256` as delivered).

**19 `gaussian_polylogarithms_research_package_20261009`**, *Gaussian
polylogarithms: proofs, reductions, and exact certificates* (modular article;
master, `sections/` and `references.tex` not staged):
`19-gaussian-proofs-{CLAIM_STATUS,INTEGRATION}.md`, the proposed manuscript patch
`19-gaussian-proofs-proposed_corrections.diff` (chapters 4 and 6 of the
manuscript; not applied here), `code/19-gaussian-proofs-*` (the Hölder certificate
engine, verifier, replay, and the `independent-*` derivations with their README),
`data/19-gaussian-proofs-*` (coefficient tables, 75 rational certificates, enclosure
and replay summaries, the `independent-*` results with their delivered
`reference-` copies, and eleven `.log` run records, force-added because the root
`.gitignore` ignores `*.log`), and
`figures/19-gaussian-proofs-branch_and_alphabet.{pdf,png}`.

### What 18 and 19 repeat

| Result | Earlier sources | 18 | 19 |
|---|---|---|---|
| depth-two parity specialized to the unit circle, every weight | 14–17 | ✓ `thm:parity` (branch-safe, inner index 1 included) | ✓ `thm:gaussian-inversion` (singular limit exposed) |
| the five weight-six doubles `gauss:eq:g51` … `g15` | 14–17 | ✓ | ✓, and again by a differential recurrence with exact double-zeta boundary data |
| `gauss:eq:wt5-sporadic` = 960·(1,4) − 224·(2,3) shuffle rows; span at most two | 14, 15, 17 (16: `π`-free form) | ✓ (both rows, "at most two") | – (keeps the manuscript's conditional "at most three") |
| even-weight Gaussian tables | through 12 (14, 15) | through 16 (64 formulas) | weight 8 (seven rows), Bernoulli rule at every even weight |
| height-one column `g_{2m−1,1}` | 15, 16, 17 | ✓ `cor:height-one` | |
| the three weight-four Gaussian triples; every position of one `2` among `1`s | 14 `thm:one-two` (via `Li_k(1−z)`) | | ✓ `one2:thm:triples`, `one2:thm:closed` (via `Li_k(1/(1−z))`) |
| the four mixed constants `Re Li₄,₁`, `Im Li₅,₁` at `(i,−i)`, `(ρ²,ρ)` | 10 (batch 138, X1); 14 (inherited), 15, 17 | | ✓ `thm:inverse-color`; credits "companion work" without naming it |
| `S₄` (`gauss:eq:S4-closed`) | open in 14–16 | open: the two-coordinate form of 14, a rational enclosure of the difference in `[−10⁻¹¹⁸, 10⁻¹¹⁸]` | – |

Intake compared the tables exactly: 18's 36 rows of weights 2–12 equal 14's,
18's twelve rows of weights 6 and 8 equal 19's, 18's height-one corollary equals its
table for `m = 2,…,8`, and 18's weight-six rows equal the manuscript's five.

### What is new in 18 and 19

- **18:** a signed density for `Li_{a,b}(z,1)` (integer `a ≥ 1`, real `b > 0`):
  moments `H_{n−1}^{(b)}/n^a`, zero mass, exactly one sign change
  (`thm:kernel`); hence `Im Li_{a,b}(e^{iθ},1)` has exactly one zero in `(0,π)`,
  simple and below `π/2`, and every `g_{a,b}` is negative (`thm:unique-zero`); a
  four-term large-`a` expansion of the zero, uniform for `b ≥ 1`; a one-sided Euler
  enclosure `[E_N − C_b2^{−N}, E_N]` with `O(N)` exact updates, and the sharp Euler
  error with its full logarithmic polynomial; the rank `⌊w/2⌋` and Pascal inverse of
  the same-point shuffle system in every weight; two weight-seven identities; a
  rational witness that `S₄`'s target is not in the row span of one specified
  `92 × 23` weight-five depth-two system (an obstruction for that system only); and
  an odd-weight rank conjecture (`rank A_w = 5w − 6`), checked through weight 31.
- **19:** the top coefficient `(−1)^{N+a}C(N−1,a)` of the one-2 family, giving at
  most one imaginary direction per weight at the half-Gaussian point modulo stated
  products, and closed forms for the top two series-depth layers; sixth-root
  closure of the one-2 family; Gaussian weight-five and weight-six one-2 reductions;
  an exact Hölder-convolution certificate with a uniform tail bound and polynomial
  bit cost (also over a fixed imaginary quadratic field), 75 certificates replayed by
  an independent nested sum; and three corrections to placed documents, recorded in
  the project README.

So the report now has four certified evaluators: 16's Chebyshev moments, 17's
midpoint rule, 18's signed Euler sums and 19's Hölder decomposition.

### Caveats for 18 and 19

- 18's unique-zero, asymptotic and Euler theorems were checked at intake only by
  sampling (one sign change, below `π/2`, at six index pairs including `b = 1/2`);
  their proofs were not re-derived. 18's zero table is explicitly not certified.
- 18's obstruction says nothing about relations outside its specified matrix; 18's
  rank pattern is a conjecture.
- 19's patch targets the manuscript, which this report does not edit. Its last
  chapter-4 hunk does not apply to the repository's bytes (it removes a blank line
  after the file's last line: the extra trailing newline of the retrieved copy that
  also makes its recorded SHA-256 values differ), and its chapter-4 text still calls
  the weight-five span "at most three", superseded by 14, 15, 17 and 18.
- The prefixed scripts resolve inputs and outputs relative to their delivered
  locations and rewrite their recorded outputs; rerun on copies in a scratch
  directory under the delivered names. 19's `check_source_patch.py` compares the
  same newline-shifted SHA-256 values and would report a mismatch on this checkout.

## Later sources (batch 141, 9 October 2026)

Dated note, 2026-10-09. Five continuations arrived together (arrival commit
`a2a4cf58c4`); three of them are added here as sources 21, 23 and 24, prefixed like
15–19 (placement `3b0bae5f5a`), and two (20, 22) are added to
[`../rational-grid-distribution-ranks/`](../rational-grid-distribution-ranks/). Their
manuscripts, PDFs and delivery READMEs are not staged; they are retrievable from the
arrival commit. All three were pinned before this report existed (21 at `29d9344771`,
23 at `78f9e5df05`, 24 at `d00eba30c1`; the batch-139 placement is `d4dead2c6b`), and the
manuscript under `../../manuscript/` has been rebuilt since all three pins, so their
manuscript line numbers are stale. 24 had read 14's arrival archive and cites it; 21 and
23 cite no source of this report. All are unrefereed; 23 and 24 say they were prepared
with OpenAI assistance; none claims a proof-assistant check.

**21 `ProveIt_polylogarithms_complementary_depth`**, *Complementary depth, classical
ladders, and exact shuffle ranks* (18 pp.): `21-complementary-depth-BUILD-REPORT.md`,
the proposed manuscript material `21-complementary-depth-integration-EDITORIAL-NOTES.md`
and `21-complementary-depth-integration-complementary-depth-insert.tex`,
`code/21-complementary-depth-*` (the exact word engine `polylog_words.py`, checks,
interval certifier, `S₄` row audit, standard-library replay, `Makefile`),
`data/21-complementary-depth-*` (the high-depth catalogue, 1.06 MB, one-zero and
two-zero tables, the weight-six triple matrix, Gaussian interval endpoints, the `S₄`
row matrix and witness, `tables-shuffle_ranks.csv`, `SOURCE-PROVENANCE.json`,
`MANIFEST.sha256` as delivered, and the run record `verification.log`, force-added
because the root `.gitignore` ignores `*.log`).

**23 `polylogarithms_research_2026-10-10`**, *Sharp Remainders and Exact Reductions in
Polylogarithm Arithmetic Bridges* (37 pp.; master, `sections/` and `references.tex` not
staged): `23-sharp-remainders-proposed_changes-README.md`, the manuscript patch
`23-sharp-remainders-proposed_changes-manuscript-corrections.patch` (not applied; it no
longer applies to the rebuilt manuscript) and the fragment
`23-sharp-remainders-proposed_changes-mixed_survivor_insertion.tex`,
`code/23-sharp-remainders-*` (moments, Herglotz, Tornheim, relation spaces, `S₆` Mellin,
Euler and exact rational residual certificate, figures, `Makefile`), `data/23-sharp-remainders-*`
(check records, `claim_ledger.json`, `source_manifest.json`, the `audit-` records and the
exact `S₆` residual-enclosure certificate, which does not prove `S₆`), and `figures/23-sharp-remainders-{herglotz_oscillation,moment_remainders}.{pdf,png}`.

**24 `polylogarithms_rigidity_20261010`**, *Complementary-Power Rigidity, a Gaussian
Euler-Sum Identity, and Reflected Gamma Moments* (35 pp.; master, `article/sections/`
and `article/references.tex` not staged): `24-rigidity-integration-INTEGRATION.md`, the
manuscript patch `24-rigidity-integration-even_weight_normalization.patch` and its text
`24-rigidity-integration-proposed_P_even_correction.tex` (not applied),
`code/24-rigidity-*` (the `S₄` verifier `verify_s4.py`, standard library only, and its
discovery program, ladder, reflected-moment and saddle checks, `Makefile`),
`data/24-rigidity-*` (`S4_certificate.json`, 538 kB, its verification and numerical
audit, ladder certificates, degree counts, reflected-moment and saddle records,
`provenance.json`, `mathematical_review.json`), and `figures/24-rigidity-saddle_rate.{pdf,png}`.

### `S₄`, proved by an exact certificate

24 (`thm:s4`) gives `gauss:eq:S4-closed` in the form: with `S₄ = g₄₁ + Im Li₄,₁(i,−1)`,
`Im Li₄,₁(i,−1) = −(3g₄₁ + 3g₃₂ + 9g₂₃)/7 + π⁵/224 − (27/224)Gζ(3) − 2β(4)log2`. This is
proved by 24's exact rational certificate (911 double-shuffle and distribution rows plus
one convergent duality), replayed at intake with the delivered standard-library verifier
(empty residual), row schemas checked by hand and the identity confirmed to 40 digits;
no independent re-derivation of all 911 rows has been made.
The certificate is an exact rational identity `F = −1120D + Σ q_r R_r` among formal weight-five
words: 911 standard rows (713 convergent double-shuffle rows, 181 rows with one
regularized `Li₁(1)` factor, 17 lifted convergent distribution rows, with products of
depth one by depth up to four) and one convergent instance `D` of the involution
`t ↦ (1−t)/(1+t)`, which permutes `{0, ∞, ±1, ±i}`. This answers question 1 of 14
(`sections/07_research.tex`, "Prove the `S₄` relation with an exact colored certificate").

Intake (dossier141_POLYLOG, not re-proved in this note): the delivered verifier, read in
full, replayed the certificate on a copy with an empty residual; the pullback
`φ*ω_a = ω_{φ(a)} − ω_{−1}`, the distribution normalization `2^{w−d}` and the
single-divergence cancellation were checked by hand; the identity holds numerically to
40 digits. The four restricted-row obstructions delivered at the same time (20: 96 rows;
21: 134 rows; 22: 96 rows; 23: a separating functional) and 18's (92 rows) concern
families of depth-two product rows only, so they do not conflict with 24: they show
what such rows cannot reach. 24 credits an earlier representation of `S₄` by two
colored doubles to a 2021 discussion (Hintze and pisco); not checked.

### What 21, 23 and 24 repeat

| Result | Earlier sources | 21 | 23 | 24 |
|---|---|---|---|---|
| the three weight-four Gaussian triples | 14, 19 | ✓ `thm:gaussian` (via the one-zero family) | | |
| every position of one `2` among `1`s (`Li_{{1}^a,2,{1}^b}`) | 14 `thm:one-two`, 19 `one2:thm:closed` | ✓ `thm:onezero`, `thm:terminal` (via `q = 1/(1−z)`, like 19) | | |
| formal shuffle count `ℓ_{w,d}` (Witt) and rank 7 on the ten weight-six triples | 14 `thm:witt`; C11 | ✓ `thm:rank` | | |
| the two weight-five shuffle rows (span at most two) | 14, 15, 17, 18 | | ✓ `prop:two-g` | used, not counted as new |
| inverse-argument mixed doubles; `Im Li₅,₁(i,−i)` reduces | 10 (X1); 14, 15, 17, 19 | | ✓ `prop:inverse-mixed`, `eq:mixed-weight-six` (credits 10) | |
| the mixed-point antisymmetry must swap colours | 19 (batch 140) | ✓ exact value at `a = b = 1` | | |
| cubic log-gamma moment in Tornheim–Witten derivatives (Bailey–Borwein–Borwein 2015, Thm 6) | 14 | | ✓ `sec:cubic`, independent proof and evaluator | |
| late coefficients `c_k ~ Cρ^{−k}k^{−3/2}` of the log-gamma moment expansion | 14 | | ✓ complete expansion (`thm:late`) | the case `m = 0` of `gam:thm:late` (credited) |
| `S₄` not reachable from a specified family of depth-two product rows | 18 | ✓ 134 × 23, rank 19 → 20 | ✓ separating functional | `S₄` proved by an exact certificate with a larger family (replayed at intake; see above) |

### What is new in 21, 23 and 24

- **21:** complementary depth (`thm:complement`): every one-variable multiple
  polylogarithm of weight `w` and depth `d` is a rational combination of
  `L^j Li_A(q,1,…) ζ(B)` with `q = 1/(1−z)`, `L = log q`, `depth(A) + depth(B) ≤ w − d`,
  hence depth at most `⌊w/2⌋` with the argument family enlarged (`cor:halfb`); a
  two-zero height-one reduction of `Li_{3,{1}^{w−3}}` to doubles (`thm:twozero`);
  rational interval certificates for the triples below `10⁻⁹⁰`.
- **23:** for the classical log-gamma moment expansion, the least term at
  `k = (n + 3/2)/Λ + O(1)` and the sharp remainder, half the first omitted term with two
  corrections (`thm:optimal-moment`, `cor:moment-second`; question 7 of 14); for the
  Herglotz function, a finite Bernoulli–Hurwitz evaluator of `F^{(r)}(p/q)`
  (constructive form of Radchenko–Zagier's closure, credited), an effective remainder at
  large derivative order, a two-term oscillatory asymptotic and infinitely many sign
  changes (`thm:herglotz-*`, `cor:herglotz-signs`; a different limit from the large-`x`
  truncation of [`../herglotz-cyclotomic-obstructions/`](../herglotz-cyclotomic-obstructions/));
  the all-exponent Gaussian mixed endpoint identity (`thm:mixed-endpoint`); all-weight
  dimensions of one specified imaginary quotient at levels 3 and 4 (`thm:level-three`,
  `thm:level-four`; formal only); and a new conjecture for `S₆` (`conj:S6`, weight seven)
  with a frozen integer vector and an exact rational residual enclosure below `10⁻²⁶⁰`
  (`thm:euler-certificate`).
- **24:** the `S₄` proof above; complementary-power rigidity: a real `0 < r < 1` has at
  most two pairs `r^a + r^b = 1`, two exactly when `r^d = ω` (`ω` the root of
  `x³ + x² − 1`), with pairs `(d,5d)`, `(2d,3d)` (`thm:complement-collisions`, from
  Ljunggren–Tverberg), signed unit counts `0, 3, 6, 12`, an exhaustive exponent bound and
  an exact count of bases by degree (question 5 of 14); proofs of the plastic `Li₂` and
  `Li₃` ladders and two log-free plastic identities; exponential cancellation at
  proportional harmonic depth for `T_{p,h}` (`thm:saddle`, continuing the transition of
  [`../alternating-harmonic-polylogarithms/`](../alternating-harmonic-polylogarithms/));
  reflected log-gamma moments `∫₀¹ Γ(x)^z f(1−x)^m dx` at fixed `m` (continuation,
  residues, late coefficients, effective remainder; question 8 of 14), a finite
  reflection identity among their residues, and a formal proof of Conjecture 5.5 of the
  2010 Amdeberhan et al. author preprint (third-party; not checked).

### Caveats for 21, 23 and 24

- Intake checked numerically (40 digits; dossier141_POLYLOG): `thm:s4` and its mixed
  form, 23's two rows, `eq:S4-two`, `thm:mixed-endpoint` for `p = 2, 3, 4`, `eq:K41`,
  `eq:mixed-weight-six`, `conj:S6` and its integer vector (evidence only), 21's exact
  antisymmetric value, the four plastic identities, and 24's degree claims on
  complementary pairs for five bases. 23's and 24's asymptotic theorems, 21's general
  theorems and the triples were not re-derived.
- `S₆` is a conjecture; the `10⁻²⁶⁰` enclosure does not prove it.
- 21's and 23's dimension statements are dimensions of specified formal quotients, not
  of evaluated periods; 24's 911-row count is not minimal.
- 23's patch and 24's patch target the manuscript, which this report does not edit; 23's
  no longer applies to the rebuilt manuscript, 24's still does.
- The prefixed scripts resolve inputs and outputs relative to their delivered locations
  and rewrite their records; rerun on copies in a scratch directory under the delivered
  names. `24-rigidity-verify_s4.py` takes the certificate path as an argument.
