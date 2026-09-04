# Draft manifest

Global inventory of every research draft under this directory, grouped by
theme. Each draft directory holds one source package and any supporting data,
scripts, or figures; most also retain a compiled publication PDF, while a
source-only package records that status explicitly. Drafts are **temporary
inboxes** (see [`../README.md`](../README.md)): once a draft's content is
either integrated into the primary exposition or absorbed into the
canonical frontier volume, the draft is deleted; this manifest must be
updated when that happens.

New drafts arrive through `incoming/` (as archives or directories),
are unpacked into the matching group, and are recorded here.

Reorganized into thematic groups on 2026-08-28. Path strings inside the
documents themselves (corpus inventories, provenance banners,
`\nolinkurl{...}` pointers) predate the reorganization and refer to the
old flat layout; the **Previous path** column below is the map. Documents
were moved verbatim — no `.tex` content was changed by the reorganization,
so no PDF was rebuilt for it.  The same holds for the 2026-09-02 split that
moved the six polynomial-logarithmic transseries packages out of `lambert-w/`
into the new `series-and-transseries/` group.

**Current artifact checkpoint (2026-09-01).** The live Lean audit scans 675
source modules and 8,909 public declarations, with no missing module headers or
declaration comments.
Several PDFs below are retained,
readable publication checkpoints rather than renders of the final merged TeX.
In particular, the primary exposition, Lean walkthrough, canonical frontier,
Integration-and-Transform master, notation catalogue, Representation master,
New Frontiers-2, inverse-computability report, canonical inverse-theory
synthesis, and canonical forward/inverse q-series synthesis require a fresh
final-source build (the inverse-theory PDF has not yet been published).
Documented pre-replay checkpoints include 167 pages
for the primary exposition, 126 for the walkthrough, 237 for the canonical
frontier, 377 for the Integration master, 88 for the notation catalogue, 301
for Representation, 41 for New Frontiers-2, 42 for inverse computability, 158
for the comb synthesis, 354 for the consolidated q-series synthesis, and 238
for Exponents. The
listed page counts are artifact receipts, not claims of current source/PDF
synchronization except where a package explicitly records it.

The notation-unification tranche completed on 2026-09-01 was source-only: no
PDF was regenerated.  For every affected package, the exact live-source
fingerprint recorded in the thematic checkpoint below supersedes an older
inline source count or any earlier statement that the retained publication PDF
renders the current TeX.  Immutable arrival records and all historical build
fingerprints remain provenance evidence rather than current-source claims.

The historical inverse-computability predecessor is retired and survives only
through the pinned pre-retirement snapshot and canonical provenance record.
Its latest source-only checkpoint supersedes the older inline boundary: the
report was 2,992 lines (SHA-256
`359ac1239788d1d7af25214a6be26e421f716db6d1c254692469bddd2d25833a`).
`EffectiveMonotoneInverse.lean` now proves the certified fixed-depth
tolerant-bisection realizer and restricted sequential inversion, while
`FabiusInverseComputable.lean` proves the totalized inverse is an
`IsComputableRealFunction`. `EffectiveGapInverse.lean` additionally derives a
computable reciprocal inverse modulus and effective continuity from computable
positive rational forward gaps. The retained 42-page PDF remains historical;
exact endpoint-mass ceiling minimality and input-bit asymptotics remain outside
Lean.

The two canonical syntheses have source/artifact receipts. The current
q-series source has 14,516 lines, 682,778 bytes, and SHA-256
`3184b1ed82998f7a9a903cbd0e95a6836cbeab2edd3194e5dc35c7243b9b9618`.
Its retained PDF is a historical 354-page, 3,030,302-byte A4 artifact with
SHA-256
`1050a9a3b0b7a8df8e7de0870946ae64940d7d7839a2f20427be0ebe14b0ba8c`,
built from the preceding 14,381-line, 675,239-byte source with SHA-256
`240bff72fb47562e9a8fd87085b5a3a96d738189714518db17988f7c4ac15d31`.
The live TeX adds the Bell-block and MacMahon q-Catalan notation successor as
well as later formalization crosswalks, so it is source-only relative to that
build; the two payloads are distinct and no render parity is claimed.  The
still earlier 348-page artifact checkpoint also remains historical evidence:
its PDF SHA-256 is
`8bf14b52d8a0fc0abc4d54cca503fd47a2df37cf76ee1bb4e442bea1fd2a4aa7`,
and its 14,158-line, 661,835-byte build source had SHA-256
`79ee5e60a6c7e42a91c58dcd9bcae56173cc6b4aa3e54739a461943f705f3904`.
Six finite/infinite q-series modules contribute 69 public declarations for
continuity at `q = 1`, Euler and q-binomial sums, Jacobi's triple product,
q-Pascal summation, the noncommutative q-binomial theorem, and Rogers--Szegő
polynomials. A further six-module inventory adds `QMultinomial.lean`,
`QPochhammerInfiniteBounds.lean`, `QPochhammerComplexOrder.lean`,
`BasicHypergeometricSeries.lean`, `HeineTransformation.lean`, and
`QGaussSummation.lean`. The newest four modules are
`GaussianBinomialPalindromic.lean` (12 theorems), `JacksonIntegral.lean` (one
definition, seven theorems), `QExponential.lean` (three definitions, eight
theorems), and `ThetaQuasiPeriodicity.lean` (one definition, six theorems).
The subsequent tail adds `QPochhammerLogDerivative.lean` (10 theorems),
`QPochhammerOrderDerivative.lean` (three theorems), `JacobiCubic.lean` (two
theorems), `CentralQBinomialReduction.lean` (six theorems), and
`CyclotomicFactorization.lean` (seven theorems); the final two modules make the
central-reduction and cyclotomic-factorization rows Exact at their audited
commutative-ring, field, and integral-domain boundaries.
The root-of-unity tail adds `CyclotomicDivisibility.lean` (three theorems),
`PrimitiveRootBlock.lean` (three theorems), `QCatalan.lean` (one definition
and eleven theorems), and `QLucas.lean` (eight theorems), for one definition
and twenty-five theorems in all.
The newest analytic/algebraic tail adds `QBetaIntegral.lean` (one definition
and eight theorems) and `NewtonInterpolation.lean` (three definitions and
nineteen theorems). The latter exposes `newtonCoeff`, `nodeNewtonPoly`, and the
collision-safe compatibility definition `newtonInterpolant`; its six theorem
wrappers complete the seven-alias union while the older scalar `newtonPoly`
remains a different object.
The final q-series tail adds `GaussianBinomialInteger.lean` (one definition
and ten theorems), `GaussianBinomialComplexOrder.lean` (one definition and
five theorems), and `QPfaffSaalschutz.lean` (three theorems). It extends
Gaussian coefficients to integer and principal-complex upper indices and
proves the terminating balanced q-Pfaff--Saalschütz sum under its explicit
nonzero and denominator hypotheses.
`QuantumMultinomial.lean` adds five theorems: antidiagonal tuple recursion,
noncommutative Gaussian symmetry, and the ordered q-multinomial theorem for
pairwise q-commuting variables.
`GaussianBinomialBounds.lean` adds six theorems for inversion reciprocity and
evaluated reciprocity, nonnegative-nome lower and strict-contraction upper
bounds, and dimension-dominant two-sided estimates for real nomes greater than
one. Its positivity input is the already-counted
`finiteQPochhammerIn_self_pos` imported from `GeneralQConditionNumber.lean`.
`RvachevSuperconvergentSynthesis.lean` adds one definition and eight theorems
for the selected dyadic phases and their monomial, polynomial, deconvolution,
and Appell sampling identities, without a maximality claim.
The local reciprocal-power zero-lattice theorem completes
`QPochhammerEntire.lean` to five theorems, and two further general-product
theorems complete `QPochhammerInfinite.lean` to one definition and 29
theorems. The source also adds the zero-definition, three-theorem
`GeometricPochhammerNormalConvergence.lean` crosswalk: the outer spectral
product's locally uniform convergence is exact for every complex strict
contraction, including `q = 0`, with dyadic Rvachev and bounded-Fabius Fourier
specializations. The compound centered/MGF and exterior reciprocal/pole
theorem remains Partial. The forward status ledger covers 282 labelled
results: 90 Exact / 84 Partial / 100 None / 8 N/A interface rows. No PDF was
generated for this source-only merge, so the retained 354-page artifact
remains historical. The comb synthesis also
has a later chapter-03 notation edit: its retained 158-page, 2,456,105-byte
A4 PDF has SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`;
it is a validated historical checkpoint pending a fresh three-pass render.

The q-series consolidation retired the three general guides, the former
forward q-Pochhammer monograph, and the former inverse-q driver after recording
their source dispositions. Their content and provenance now live in the single
root-level `q_pochhammer_q_binomial_monograph/`; every retired layout remains
recoverable from its pinned revision and Git history. The remaining standalone
q-series reports retain their thematic subgroup paths. In particular,
Exponents has a 16,369-line current source and a retained 238-page PDF.  That
PDF is the three-pass artifact built from the preceding 16,274-line source;
basic structural and font checks passed, but the larger batch stopped before a
fresh full log, page-box, and visual publication audit.  It therefore remains a
historical payload rather than a render of the current TeX.  Cyclotomic has a
1,875-line current source and a retained 28-page PDF; both packages require
final-source rebuilds before synchronization is claimed. Package-local
inventories may record current TeX and historical PDFs as distinct payloads;
such a record does not assert render parity, and synchronization receipts wait
for final renders. Immutable arrival fingerprints remain unchanged. All
repository checksum-ledger files have been abolished; this manifest makes no
claim of operational checksum verification. Historical SHA-256 values below
are artifact receipts only.
Any older row below that calls one of these changed pairs synchronized, gives
Exponents as 236 or 237 pages, gives Cyclotomic as 29
pages/1,896 lines, gives the comb synthesis as 156 pages, or treats a retained
inverse/New-Frontiers PDF as current is superseded by this checkpoint. The
closed-form Gaunt/Wigner-square boundary recorded below and the q-jet status
in the linked q-series registry remain unchanged by this merge.

For the final source-only union, package-local READMEs record the current
q-series and Exponents source fingerprints. The live Exponents TeX is
16,369 lines and 737,912 bytes with SHA-256
`a4aecd625f7eb405de866e2b368bbdc648fb0f9e11b423cb936a2f319d195f02`;
it includes the exact zero-order/exponent identifiability and constructive
first-difference crosswalk from the new zero-definition, six-theorem Lean
module, while zeta-quotient, cumulant/analytic-sample, and probability-law
identifiability remain Partial in Lean. It also records the exact
zero-definition, three-theorem outer q-Pochhammer normal-convergence API;
the centered/MGF wrappers, outside-disk reciprocal formula, pole divisor, and
zero--pole exchange in the compound claim remain Partial.
The retained Exponents PDF is 238 A4
pages and 6,953,898 bytes with SHA-256
`fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`.
It was rendered from the preceding 16,274-line, 731,692-byte source with
SHA-256
`4be184dc95f7c9d7665e5edf56cd22dc66bdacbc2f113b03b700468836018f8b`.
The retained q-series and Exponents PDFs both predate their latest merged
crosswalk and notation successors and are therefore distinct historical
payloads; no final-source/PDF parity is claimed. These current facts supersede
the older rows below.

## Incoming status

No research payload is awaiting intake.  The `incoming/` directory contains
only its permanent `README.md`.  The ten archives received on 2026-09-02
(commit `3065a34fe`) were filed the same day by a quick archival intake --
six dyadic up-extraction/extrapolation reports into
`inverse-and-sampling/dyadic-up-extraction/`, three articles on reversing
`x + W(x)` into `series-and-transseries/lambert-inverse-transseries/`, and
one byte-identical reship (`rvachev_q_extrapolation_bundle (1).zip`, same
SHA-256 as `rvachev_q_extrapolation_bundle.zip`) deleted without a second
directory.  Claim review, comparison, consolidation, and Lean crosswalking of
this batch are deferred past the intake publication gate.  Text files inside
the packages are stored with repository (LF) line endings; each package's own
`SHA256SUMS` ledger, where present, was computed by its author on the
submitted bytes and is kept verbatim.

## fourier-decay — `rvachev_up_fourier_decay/`

The former twelve-document Fourier-decay corpus was consolidated editorially
on 2026-08-31. The canonical article deduplicates the original question, eight
reports, two audits, and the Gentle Guide; supplies missing proofs; corrects
the LIL normalization, Pochhammer formula, numerical transcriptions, and gauge
overclaims; and adds integer-ratio `q`-Pochhammer, ray, and variance theorems.
Its source concordance preserves the independent audit history through immutable
links to pre-consolidation commit `2e3567feb14947ee3ebcdab11adca64e746ad26f`.

| Directory | Document | Supporting evidence | Previous paths / provenance |
| --- | --- | --- | --- |
| `Rvachev_Up_Fourier_Decay/` | *Fourier Decay of Rvachev's Up-Function* — single canonical TeX/PDF synthesis, proof corpus, correction ledger, and Lean parity appendix | `verification_scripts/` retains the valid audit programs and captured data; the invalid legacy `stage4.py` sampler was retired in favor of `stage4b.py` | At commit `2e3567feb14947ee3ebcdab11adca64e746ad26f`: `asymptotic-decay-rate-of-an-infinite-product-of-sinc-functions/`;<br>`rvachev_up_fourier_decay-1/`;<br>`Rvachev_Up_Fourier_Decay-2/`;<br>`Rvachev_Up_Fourier_Decay-3/`;<br>`rvachev_up_fourier_decay-4/` through `rvachev_up_fourier_decay-8/`;<br>`Rvachev_Up_Fourier_Decay_Comparative_Audit/`;<br>`Rvachev_Up_Fourier_Decay_Second_Wave_Audit/`;<br>`Rvachev_Up_Fourier_Decay_Gentle_Guide/` |

## thue-morse — `thue-morse/`

Besides the consolidated volume, the group holds three independently written
articles on one question, filed 2026-09-03 from `incoming/` as separate
members pending comparison and merge: the two-dimensional table obtained by
repeated weighted prefix summation of the signed Thue–Morse sequence, its
identification `s(n,k) = σ_{2n+1}(k−n−1)` with the odd iterated prefix sums,
and the diagonal polynomials `D_r` with generating function
`TM(z²)/(1−z)^{2x}`. All three archives wrapped an inner directory of the same
name, so the archive stems were used as directory names. No source loads
`docs/fabius-notation.tex`. Quick intake only; claim comparison, deduplication,
proof checking, numerical reproduction, and Lean crosswalking are deferred.

| Directory | Document | Previous path |
| --- | --- | --- |
| `thue_morse_diagonal_polynomials/` | *Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue–Morse Summation* — 1,763-line/56,520-byte source, 24-page A4/724,035-byte PDF (pdfTeX-1.40.26; 25 font rows, 7 Libertinus; 3 Type-3 rows inherited from the Matplotlib figure `row_profiles.pdf`); 14 theorems, 1 proposition, 1 lemma, 3 corollaries in 15 sections; `experiments.py`, `thue_morse_table.wl`, `verification_report.txt`; submitted `SHA256SUMS` kept as payload | `incoming/thue_morse_diagonal_polynomials.zip` |
| `thue_morse_diagonal_polynomials-2/` | *Diagonal Polynomial Laws in Odd Iterated Thue–Morse Summation: Riordan-array structure, 2-adic Bell recurrences, exact arithmetic, and fast Wolfram Language evaluation* — 2,202-line/72,380-byte source, 37-page A4/801,220-byte PDF (fully embedded, Type-3-free, 7 Libertinus rows); 11 theorems, 2 propositions, 7 corollaries, 1 conjecture, 3 definitions in 16 sections; `diagonal_polynomials.py`, `diagonal_polynomials.wl`, `VERIFICATION.txt`; submitted `SHA256SUMS` kept as payload | `incoming/thue_morse_diagonal_polynomials-2.zip` |
| `thue_morse_diagonal_polynomials_article_and_code/` | *Diagonal Polynomials and Dyadic Block Geometry in Repeated Thue–Morse Prefix Summation: Exact formulas, denominator laws, rational roots, and fast Wolfram Language evaluation* — 2,136-line/76,590-byte source, 33-page A4/536,235-byte PDF (26 font rows, no Libertinus; 2 Type-3 rows inherited from the Matplotlib figure); 10 theorems, 10 propositions, 1 lemma, 6 corollaries, 1 definition in 14 sections; `diagonal_analysis.py`, `thue_morse_diagonals.wl`, `generated/` (two CSV tables, run log, verification report), `figures/`; submitted `MANIFEST.sha256` kept as payload; the two CSV tables received the repository's CRLF-to-LF normalization at commit, so their submitted checksums no longer match the filed bytes | `incoming/thue_morse_diagonal_polynomials_article_and_code.zip` |
| `Thue_Morse_Atlas_and_Frontiers/` | *The Thue–Morse Sequence: Formula Atlas and Fabius–Rvachev Frontier Results* (137 pp) — consolidation (2026-08-28) of the former `Thue_Morse_Formula_Atlas/` (*A Unified Formula Atlas for the Thue–Morse Sequence*) and `Fabius_Rvachev_Thue_Morse_Frontier_Results/` (*A Finite-Block Calculus for the Fabius–Rvachev–Thue–Morse System*, heavily Lean-crosswalked); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## combinatorial coefficient calculus — `combinatorial-coefficient-calculus/`

Six standalone archival arrivals were filed here on 2026-09-01 and have been
consolidated into one document. The non-suffixed
`Combinatorial_Coefficient_Calculus/` package is the sole survivor: it used the
stronger suffixed sibling as its mathematical spine, and the distinct
incidence, Bernoulli--Barnes, Good-inversion, Catalan, inverse-singularity, and
algorithmic layers of the other five were merged theorem by theorem. The five
donor directories were deleted once every source, topic, and claim row of the
disposition ledger reached a completed disposition; git history is the archive,
and PROVENANCE.md pins the immutable pre-consolidation identities.

The final pass proved the sharp Bell bound the arrivals had only asserted,
supplied Euler's limit and the Weierstrass product on which an existing
polygamma proof silently depended, merged thirteen further donor-only results,
repaired eight double-superscript errors that had made the source fail to
compile at all, and completed the notation-catalogue migration. The filed PDF
now renders the filed TeX. None of the manuscript proofs is claimed as Lean
verification; the in-document "Lean formalization register" states the
formalization status per result.

| Directory | Document | Previous path / provenance |
| --- | --- | --- |
| `Combinatorial_Coefficient_Calculus/` | **Canonical, consolidation complete:** *Combinatorial Coefficient Calculus* — 8,966-line/390,732-byte source and the 174-page A4 PDF built from it in the same run | Six-source provenance, closure, and disposition ledgers in the package; original non-suffixed arrival was `incoming/Combinatorial_Coefficient_Calculus.zip` (SHA-256 `a22479ac8f58e1710117af9d0a3f515c7d24ec250548f537520c9f9024f4321a`); the five retired donors are identified in `SOURCE_CLOSURE.sha256` |

## exponents-and-q-series — `exponents-and-q-series/`

There are two live document packages, both at this topic root:
`q_pochhammer_q_binomial_monograph/` and `geometric_q_fabius_frontiers/`.

The subgroups `q-fabius-parameter-deformations/` and
`geometric-sinc-and-exponent-families/` no longer exist. On 2026-09-02 their
six standalone documents were consolidated into
`geometric_q_fabius_frontiers/` — *Geometric q-Fabius–Rvachev Frontiers* — and
deleted from the working tree. The former
`geometric-sinc-and-exponent-families/Exponents_and_q_Series_Frontiers/`
became the volume's Parts I–VII and was renamed in place, keeping its assets;
the other five became Parts VIII–XII in this order:

| Absorbed package | Part |
| --- | --- |
| `geometric-sinc-and-exponent-families/Fabius_Rvachev_Frontier_Report/` | VIII |
| `geometric-sinc-and-exponent-families/Cyclotomic_q_Fabius_Rvachev_Frontier/` | IX |
| `q-fabius-parameter-deformations/fabius_q_frontiers_report/` | X |
| `q-fabius-parameter-deformations/Continuous_Parameter_Edgeworth_and_q_Gevrey_Frontier/` | XI |
| `q-fabius-parameter-deformations/Fabius_Flat_Parameter_Response_Dynamics/` | XII |

A new Part 0 was written for the merge: the six reports had each fixed the
shared geometric-uniform family for themselves, in three mutually
incompatible affine normalizations and with `X_q` and `Y_q` denoting
different objects in different reports, so Part 0 states that layer once with
proofs and tabulates the dictionary. Every absorbed report's scripts, data,
generated tables, and figures are preserved under
`geometric_q_fabius_frontiers/assets/`.

The rows below are retained in full as provenance: they record arrival
commits, archive hashes, intake payload counts, and CRLF normalizations that
nothing else records. Their Directory cells now name the absorbing part
rather than a live path. The former `q-pochhammer-and-inversion/` locations
are likewise provenance-only.

For the canonical q-series and Exponents packages, the exact source and
retained-artifact checkpoints above govern; older numbers embedded in the long
provenance rows are superseded and do not assert current source/PDF parity.

| Directory | Document | Previous path |
| --- | --- | --- |
| *(absorbed 2026-09-02 as Part~XI of `geometric_q_fabius_frontiers/`; directory deleted)* | **Absorbed.** *Continuous-Parameter Edgeworth Theory, Large Deviations, and Quadratic q-Gevrey Regularity at the Fabius--Rvachev Frontier* (29-page retained A4 PDF; 1,387 main-source lines at arrival and 1,372 currently). Landed 2026-08-30 in direct-arrival commit `52179f63fe955a64508915eedaa560de9f3056da` from the bare generic wrapper `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-G/` under this title-derived collision-safe name. Its manifest covers the full delivery; historical payload hashes reflect three CSV CRLF-to-LF normalization changes. Its title and abstract concern Edgeworth/deviation regimes, Lambert endpoint asymptotics, and quadratic-exponential Denjoy--Carleman regularity. It remains standalone pending post-publication claim and experiment review, comparison, and a Lean crosswalk; manuscript proof labels do not establish Lean proof status | `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-G/`; renamed and filed here |
| *(absorbed 2026-09-02 as Part~X of `geometric_q_fabius_frontiers/`; directory deleted)* | **Absorbed.** *Parameter-Flow, Gaussian, and Large-Deviation Frontiers for the q-Fabius--Rvachev Family* (23 A4 pp, 1,506 source lines; two scripts, four CSV tables, two captured outputs, and four PDF/PNG figure pairs). Landed 2026-08-30 as a bare directory in direct-arrival commit `8a184546747082cbd92ad4675fb61981c6b8c3b6`; no archive or outer hash was supplied. Historical intake hashes cover all 20 payloads and reflect four CSV CRLF-to-LF normalization changes. All five PDFs are readable and unencrypted (27 pages total); its title and abstract concern q-transport, convex order, Gaussian/Edgeworth limits, large deviations, and a Lambert-W boundary. It remains standalone pending assessment, document-style normalization, comparison with the closely overlapping continuous-parameter report, and a Lean crosswalk; manuscript labels and numerical checks do not establish Lean verification | `drafts/incoming/fabius_q_frontiers_report/`; filed here and removed from the live inbox |
| `q_pochhammer_q_binomial_monograph/` | *q-Series and Inverse q-Analogs: A Proof-Oriented Synthesis* — the single canonical publication for forward q-Pochhammer, Gaussian, hypergeometric, theta, partition, Bailey, interpolation, Thue--Morse, and Fabius--Rvachev theory together with branch-aware inverse q-analogs, asymptotics, certification, and labelled frontiers. The former q-Pochhammer/q-binomial monograph supplies the forward backbone; the former inverse-q synthesis supplies its nine inverse chapters; and the three general q-series guides were reviewed as donor manuscripts, with repetitions collapsed into the strongest proved statement. The historical 260-row inverse theorem concordance, package/archive provenance, 77-row asset-disposition ledger, and unique reproducibility assets remain intact. `audit/MERGE_SOURCE_REVISION` separately pins the five-publication source surface used for this merge. The current source and retained historical 354-page PDF are the distinct, no-parity payloads fingerprinted in the exact checkpoint above; retained PDFs under `assets/` are research figures only. | Former live publications: `general-q-series-guides/q-series-proof-oriented-article/` (arrival commit `1360db6064c676f83bceb23bece5ed304dd09ce8`), `general-q-series-guides/q_series_from_first_principles/` (`c167e550348bfb33b4297684100d55dfb48b8c1a`), `general-q-series-guides/q_series_monograph/` (`1f0f98390d551725fc7d2274638dbd7de86ee346`), `q-pochhammer-and-inversion/q_pochhammer_q_binomial_monograph/`, and `q-pochhammer-and-inversion/inverse_q_analogs_and_series/`; all layouts remain recoverable from pinned revisions and Git history |
| *(absorbed 2026-09-02 as Part~IX of `geometric_q_fabius_frontiers/`; directory deleted)* | **Absorbed.** *Cyclotomic Blow-Ups and Natural Boundaries for the q-Fabius--Rvachev Sinc Product* (25 pp and 1558 source lines at arrival; currently 29 A4 pp and 1896 source lines, with a 577-line deterministic high-precision experiment, five CSV tables, two further generated data files, and four PDF/PNG figure pairs). Landed 2026-08-30 from `drafts/incoming/Cyclotomic_q_Fabius_Rvachev_Frontier.zip` (outer SHA-256 `029da7d9ec96a0b2e5c4164c37f2b361dd015112bd0c6237263e3c538c5b0f64`) in its own collision-safe wrapper. Historical intake hashes covered all 22 payloads; five CSV entries changed after CRLF-to-LF repository normalization. Its title and abstract concern the complex geometric sinc product, radial root-of-unity expansions and a claimed natural boundary, cyclotomic blow-ups, Bell/moment condensation, and inverse frequency and q-branches. A post-publication revision crosswalks the global geometric-sinc q-Pochhammer factorization while leaving the cyclotomic asymptotic and natural-boundary layers manuscript-only; the historical intake hashes record all 22 payloads. The current five PDFs have 33 pages in total (29 main plus four one-page figures). The main report remains Latin Modern with nine embedded/subset Type-3 figure-font rows, and the four standalone figures contain nine more; normalization remains deferred | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| *(exact reship of the package now absorbed as Part~VIII; no second directory)* | `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-E.zip` (outer SHA-256 `174bf733156cd874cf4f9321c6ab71ca44f311856cc01dc158ddf83dc00cf813`) was processed on 2026-08-30 as an exact reship of `Fabius_Rvachev_Frontier_Report/`: the same 15-file set, with every non-CSV, non-ledger payload byte-identical and all three CSVs identical after the repository's existing CRLF-to-LF normalization. Its 13 submitted hashes again matched but omitted `README.txt`; only the historical hash receipt differs from the filed normalized package. No redundant wrapper was created, and no claim-level reassessment or experiment rerun was performed | duplicate archive verified and deleted; existing filed directory remains canonical |
| *(absorbed 2026-09-02 as Part~XII of `geometric_q_fabius_frontiers/`; directory deleted)* | **Absorbed.** *Flat Parameter Fronts, q-Susceptibility, and Smooth Dynamics: New Frontier Results in the Fabius–Rvachev System* (23 pp, 1792 source lines; with a 519-line deterministic exact/Monte-Carlo program, five CSV tables, and two PNG figures). Landed 2026-08-30 from `drafts/incoming/fabius_frontier_report_2026.zip` (outer SHA-256 `afdcf522589a7baad82c81a527c02dcc09e58455ab14c57a9c492e65563c647e`) and filed under a title-derived collision-safe directory. Historical intake hashes covered all 13 payloads; five CSV entries changed after CRLF-to-LF repository normalization. The manuscript concerns parameter susceptibility and tangent measures, flat q-parameter fronts, transform/moment/Legendre response, and Schröder/Böttcher-style Fabius dynamics. All 23 A4/Type-1 report pages rendered cleanly; blank author metadata and a nearly empty final bibliography page remain document-policy work. It remains standalone pending post-publication assessment and a Lean crosswalk; its 23 nonconjectural labels, four conjectures, and three problems record manuscript status only, and none of the new layers is thereby Lean-verified | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| *(absorbed 2026-09-02 as Part~VIII of `geometric_q_fabius_frontiers/`; directory deleted)* | **Absorbed.** *Negative Parameters, Reciprocal Bases, and the Gaussian Boundary* (26 pp, 1491 source lines; with a deterministic numerical script, three CSV tables, a generated TeX fragment, and three dual-format figures). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30.zip`; all 13 payload checksums verified. Its principal paper-level strands are the affine transport from negative to positive geometric-uniform parameters, finite reciprocal-base digit reversal, residue-class multiplication, real-base log-concavity and plateau phases, and the Gaussian boundary with explicit cumulants and Berry--Esseen control. It overlaps Part VII's signed/reciprocal q-Fabius layer and therefore remains a separate member pending a claim-by-claim audit and deliberate editorial merge; no Lean status is inferred from the report labels | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `geometric_q_fabius_frontiers/` | *Geometric q-Fabius–Rvachev Frontiers* (2026-09-02: renamed from `geometric-sinc-and-exponent-families/Exponents_and_q_Series_Frontiers/`, given a new Part~0 common-framework part, and extended by the five reports above as Parts~VIII–XII; the merged source builds in three serial passes with 0 errors, 0 undefined references, 0 multiply-defined labels, and 0 duplicate hyperref destinations). Its Parts~I–VII are the former *Exponent-Sequence and q-Series Frontiers* (current notation-source TeX: 16,369 lines, 737,912 bytes, SHA-256 `a4aecd625f7eb405de866e2b368bbdc648fb0f9e11b423cb936a2f319d195f02`; retained historical PDF: 238 A4 pages, 6,953,898 bytes, SHA-256 `fa719a8ea68d3c474928b9fae7449f827eb35a5452613f2b660d8e88ba27267e`; the source and artifact hashes are retained as historical receipts, but no render parity is claimed) — consolidation (2026-08-28) of the former `Fabius_Newton_Rvachev_Frontier_Report/` (*Exponent-Sequence and Newton-Basis Frontiers*, Lean-crosswalked) and `fabius_frontier_results/` (*q-Binomial Richardson Acceleration of Geometric Sinc Products*), joined the same day by the eighth-wave `finite_sinc_products_report/` (*Finite Dyadic Sinc Products and Piecewise-Polynomial Approximants to Rvachev's Up-Function*, from `drafts/incoming/finite_sinc_products_report_bundle.zip`) as Part III — exact truncated-power prefix formula with Thue–Morse jumps, sharp derivative plateaux, exact error law 2^(C(r+3,2)−1)/(9·4ⁿ), exact Kolmogorov 1/(9·4ⁿ), Bell–Bernoulli all-orders expansion, q=1/4 Richardson weights, uniform scale mixture X = R·U, positive Gauss/Radau/Lobatto tail quadrature with exact constants (incl. the previously open variance-matched positive 16⁻ⁿ scheme) — and by the two ninth-wave same-topic reports `Rvachev_Piecewise_Approximation_Fourier_Images/` and `rvachev_fourier_frontier_report/` **merged editorially** as Part IV (*Fourier Images of the Repeated-Integration Approximants*): master factorization F̂ₙ = Φ·A(2⁻ⁿt) with the transfer function A = sinc z/Φ(z), valuation-weighted canonical product with divisor 1−v₂(m), digit-sum zero counts and Thue–Morse sign law, exact Taylor radius 4π with dominant-pole asymptotics and arithmetic Darboux hierarchy, finite/limit zero filtration, sharp o(2ⁿ) relative window, conditioning thresholds π2ⁿ/4π2ⁿ, deconvolution impossibility, weighted-L^p and Sobolev all-orders laws, exact mean-square tails with sharp H^s threshold s<n+½, and positive atomic/dyadic/polynomial closure menus (16⁻ⁿ–256⁻ⁿ) complementing Part III's box mixtures; and by the tenth-wave `fabius_finite_products_frontier/` as Part V (*Finite Dyadic Sinc Products and Exact Transport Geometry of Rvachev Spline Approximants*): convex-order and peakedness chains, exact E\|X_N\| = 5/18 − 4⁻ᴺ/9, fixed single crossing of the density error at ±½, the exact metric collapse W₁ = d_K = 4⁻ᴺ/9, TV = 2·4⁻ᴺ/9, stop-loss = Zolotarev-2 = 4⁻ᴺ/18, W∞ = 2⁻ᴺ, the exact Thue–Morse call-potential spline, the positive-mixture no-go theorem (signed weights are structurally necessary for Richardson acceleration), entropy/Fisher monotonicity with I(u_N)<∞ ⟺ N≥3 and KL(u‖u_N)=∞, and conjectural weighted information/W_p expansions with the p≈2N transport crossover; and by the thirteenth-wave `atomic_sinc_splines_report_package/` as Part VI (*Atomic Sinc-Product Splines Beyond the Binary Point*): an English translation and frontier expansion of Rvachev's Chapter 3 on atomic functions — the geometric family h_a with ĥ_a = ∏ sinc(2πa⁻ʲξ), the zero-matching existence criterion for general atomic equations, closed cumulants κ₂ₘ = 2²ᵐB₂ₘ/(2m(a²ᵐ−1)) with Bell/Lambert-series moment calculus, weighted Prouhet identities and the full derivative hierarchy with exact norms a^{n(n+3)/2+1}/2^{n+1} (L¹: a^{n(n+1)/2}), the Cantor gap atlas for a>2 (dim_H = log2/log a, exact per-gap degree, one-branch symbolic localization, complete Taylor-germ trichotomy), the rational-power Strang–Fix reproduction theorem with Appell coefficient operator, log-Gaussian Fourier envelope, all-orders prefix expansion with r₁ = −1/(6(a²−1)) and exact leading norm a⁶/(48(a²−1)) (specializing to the binary 4/9 and 31/16200), the a↓2 collapse, the reconstructed uniqueness theorem, and the periodic-Lambert/double-scaling/lattice-obstruction conjecture register; Part VI was then **merged editorially** (2026-08-28) with its fourteenth-wave twin `Atomic_Functions_Beyond_Dyadic_Report/` (*Atomic Functions Beyond the Critical Dyadic Case*) — a second independent reconstruction of the same Rvachev chapter (identical readings on every commonly transcribed equation; shared translation/h_a core deduplicated, OCR ledger preserved in assets) whose distinctive layers became dedicated Part VI sections: the fractal-string geometry of K_a (geometric zeta ℓ₀^s/(1−2a^{−s}), complex dimensions D_a+2πik/log a with residues ℓ₀^{s_k}/log a, exact tube formula with continuous nonconstant one-periodic Minkowski profile ⇒ K_a not Minkowski measurable, explicit logarithmic average), the geometric local-degree law P(N_a=r)=((a−2)/a)(2/a)^r with E N_a=2/(a−2) and (a−2)/2·N_a → Exp(1) as a↓2 (identifying the first marginal of the critical double-scaling program), quantitative parameter limits at both ends (a↓1: standardized cumulants 3^m2^{2m}B_{2m}(a²−1)^m/(2m(a^{2m}−1)), λ₄=−(6/5)(a²−1)/(a²+1), first characteristic correction; a→∞: W∞ ≤ 1/(a−1), TV ≤ 1/(2(a−1)), exactly uniform core g_a=1/2 on |y|≤(a−2)/(a−1)), the exact general-base negative-Laplace decomposition Λ_a(u) = −(log u)²/(2 log a) + (log u)/2 + P_a(log_a u) + E_a(u) with 0 ≤ E_a(u) ≤ e^{−u}/((1−e^{−u})(1−e^{−(a−1)u})) and real-analytic one-periodic P_a whose Fourier modes are −Γ(−χ_k)ζ(1−χ_k)/log a, χ_k=2πik/log a (settling the transform-level half of the periodic-Lambert program, pinning the Lambert normalization c_a=√a·log a/2, and re-verified independently during the merge to 10⁻¹³–10⁻²⁸), the divisor-polynomial form of log M_a, and the canonical Fup ladder G_n → 2Up(2·) in every C^m (first rung of the factor-redistribution direction); and (same day) with its fifteenth-wave twin `Rvachev_Atomic_Functions_Report/` (*Atomic Functions, Rvachev's up-Function, and Smooth Cantor Splines*) — a third independent reconstruction (again identical shared readings; repairs ledger and crosswalk preserved in assets) contributing the signed gap leading coefficients L_ω = (−1)^{N₊(ω)}a^{(r+1)(r+2)/2}/(2^{r+1}r!) with fixed-point verification at a=3, the derivative equimeasurability theorem with the full L^p ladder ‖h_a^{(n)}‖_p = (a^{n(n+3)/2}/2ⁿ)(2/a)^{n/p}‖h_a‖_p and the exact derivative-value mixture law (atom 1−(2/a)ⁿ at 0 + fair-signed amplified copy), the endpoint jet-reduction remark with the Bernoulli→cumulants→moments→jets→gap-polynomials exact engine, the classical Fup_n hierarchy F̂up_n = sinc(t2^{−n−1})ⁿ·Û(t2^{−n}) with the exact triangular reconstruction of Up by n(n+1)/2 dyadic averaging steps (limit: the cosine-multiplicity product ∏cos(t2^{−r})^{r−1}), closed Fup_n cumulants (σ_n² = 4^{−n}(3n+4)/36) and the quantitative CLT (Berry–Esseen O(n^{−1/2}), standardized cumulants O(n^{1−m})), the edge pantograph equations g_a′(u) = (a²/2)g_a(au) and F_a′(x) = a²/(2(a−1))F_a(ax) generalizing F′=2F(2·), and three more register items (Fup_n Edgeworth, graph-directed atomic splines, pressure-function Taylor multifractal); then with the two **revised fourteenth-wave editions** (`Atomic_Functions_Beyond_Dyadic_Report-2/`, `-3/`) contributing the Orlicz/rearrangement form of equimeasurability (all a≥2, all 0<p<∞, exact rearrangement thinning (h^{(n)})*(t)=C_{a,n}h*(t/(2/a)ⁿ)), the **spectral Stieltjes–Wigert bridge** (the normalized Fourier energy of h_a has squared-frequency moments a^{n(n+2)}/2ⁿ — the scaled Stieltjes–Wigert sequence, moment-equal to lognormal N(2log a−log2, 2log a) yet a distinct density ⇒ explicit non-lognormal representing measures for an indeterminate problem, with exact q-Pearson equations, Hankel determinants c^{N(N+1)}q^{−N(N+1)(4N+5)/6}∏(q;q)_k, monic OPs, and a Nevanlinna–Pick register conjecture), the **Mellin law of the distance to K_a** (Δ =d ½ℓ₀a^{−N_a}V; E Δ^s with pole lattice D_a−1+2πik/log a — the complex dimensions shifted by −1; distribution function = the exact tube formula; critical logarithmic gap scale → Exp(1)), and — decisive for provenance — the **eleven-page Russian source scan itself** (`source_rvachev_scan.pdf`), against which the translation layers were checked; the scan and the raw OCR were both deleted once their recoverable content was merged and verified (SHA-256 hashes in the volume's provenance list, the deduplicated repair ledger in Part VI's concordance appendix, git history the archive); then with the **revised fifteenth-wave edition** (`Atomic_Functions_Rvachev_Report_Package/`) contributing the **q-Gaussian derivative Gram geometry** (normalized towers ψ_n=h^{(n)}/‖h^{(n)}‖₂ split into two orthogonal parity towers with exact stationary kernel ⟨η_j,η_k⟩=q^{(j−k)²}, q=1/a; Gram determinants det G_N=∏_{r≤N}(q²;q²)_r, pivots (q²;q²)_N, sharp Riesz bounds ϑ₄(0,q) ≤ symbol ≤ ϑ₃(0,q) — the derivative tower is a uniformly conditioned Riesz sequence), the **log-Weibull jet-intermittency law** (leading amplitude A=L_{N_a}: exact staircase tail P(A≥L_r)=(2/a)^r, log P(A>x)/√log x → −log(a/2)√(2/log a), all positive moments infinite, log-moments finite), and the **PROOF of the Fup_n Edgeworth program** (uniform on ℝ, all orders, after any fixed number of derivatives, exact-cumulant Bernoulli–Hermite coefficients λ₄,n=−18(15n+16)/(25(3n+4)²), λ₆,n=144(63n+64)/(49(3n+4)³); register conjecture resolved, replaced by the beyond-all-orders Stokes program); then with the **expanded fifteenth-wave edition** (`Atomic_Functions_Rvachev_Expanded_Report/`, from `drafts/incoming/Atomic_Functions_Rvachev_Expanded_Report.zip`; audit-aware — it explicitly marks the previously merged layers as inherited baseline, so only its new layer was merged) contributing the **closed q-Gram–Schmidt orthogonalization** ψ*_n = Σ_j q^{n−j}·[n,j]_{q²}·e_j with norms ‖ψ*_n‖² = (q²;q²)_n, explicit Cholesky factorization C G_N Cᵀ = diag((q²;q²)_r) and closed inverse Gram (G_N⁻¹)_{jk} = Σ_n q^{2n−j−k}[n,j][n,k]/(q²;q²)_n, the Rogers–Szegő identification q^n H_n(z/q;q²) of the orthogonalizers, the uniform-innovation corollary dist²(e_n, span before) = (q²;q²)_n ↓ (q²;q²)_∞ > 0, the **wrapped-heat-kernel circle model** (each parity tower is unitarily the monomial sequence in L²(𝕋, ϑ₄(θ/2,q) dθ/2π) — the wrapped heat kernel at time log a centred at θ=π; two more derivatives = multiplication by z), the MacMahon determinant constant det G_N = (q²;q²)_∞^{N+1}·𝔐(a⁻²)(1+O(Nq^{2N})) with parity-factored full-sequence determinants D_{2N} = (det G_{N−1})², D_{2N+1} = det G_N det G_{N−1}, triple-product Riesz forms A_a = (q²;q²)_∞(q;q²)_∞², B_a = (q²;q²)_∞(−q;q²)_∞² with a verified numeric table (A₂ ≈ 0.1211242080, B₂ ≈ 2.1289368272), and the overlap-regime theta conjecture (translated correlations for 1 < a < 2 → the same theta kernel unless a log-periodic cycle obstructs; reduces to two-term derivative-norm asymptotics); then with two **expanded fourteenth-wave editions** (`Atomic_Functions_Beyond_Dyadic_Expanded/` and `Atomic_Functions_Beyond_Dyadic_Frontiers/`, both from `drafts/incoming/` zips, both audit-aware, both re-shipping byte-identical copies of the recorded source scan/OCR — again not retained) contributing disjoint new layers: the first the **physical-space Stieltjes–Wigert differential ladder** Υ_{a,n} = P_{a,n}(−d²/dx²)h_a (compactly supported orthogonal system with norms c^{2n}q^{−n(2n+1)}(q;q)_n‖h_a‖², explicit q-binomial expansion in even derivatives, three-term operator recurrence with α_n = cq^{−2n−1}(1+q−q^{n+1}), β_n = c²q^{−(4n−1)}(1−q^n)) — **identified during the merge with the expanded-15th-wave Gram–Schmidt vectors**, Υ_{a,n} = (−1)^n‖h^{(2n)}‖₂ψ*_n (a cross-edition unification; the check also caught and repaired a sign-convention slip in the first printing of the closed Gram–Schmidt theorem: the closed coefficients orthogonalize the raw tower, the sign-corrected basis takes alternating coefficients) — plus both parity **derivative-jet Gram determinants** (odd exponent −(N+1)(N+2)(4N+3)/6), the **autocorrelation germ** (−1)^n acf_a^{(2n)}(0)/acf_a(0) = a^{n(n+2)}/2^n with zero Taylor radius and provable ladder incompleteness (Riesz density criterion, spectral law absolutely continuous), and the explicit-spectral-null-modes conjecture; the second the **exact derivative-energy factorization** μ_{a,n,p} = Law(S_{a,n} + a^{−n}Y_{a,p}) (every normalized p-energy of every derivative = level-n Bernoulli address sum + compressed base profile) with W∞(μ_{a,n,p}, ν_a) ≤ 2a^{−n}/(a−1) to the symmetric **Bernoulli convolution** ν_a (uniform at a=2, equal-weight Cantor measure on K_a for a>2; Peres–Schlag–Solomyak cited), exact Hausdorff support rate b₁a^{−n}, exact **Rényi/Shannon entropy laws** H_β(n) = H_β(0) + n log(2/a) (0<β≤∞) with the critical entropy discontinuity and the information-dimension reading (address entropy n log2 / geometric scale n log a = D_a), and the overlap-regime derivative-energy conjecture (companion of the theta conjecture); then with two **expanded fifteenth-wave editions** (`Atomic_Functions_Rvachev_Report_Expanded/` and `Atomic_Functions_Rvachev_qBinomial_Frontiers/`, both from `drafts/incoming/` zips, both audit-aware; the first re-shipped byte-identical copies of the scan, OCR, **and the two previous editions of its own lineage** — all SHAs previously recorded, none retained) contributing four closures of the orthogonalization theory and two of the jet theory: the **nodal-polynomial reading** (residual generating polynomial P_n(z) = q^{n²}∏_{j<n}(z−q^{−2j}); orthogonality = interpolation at geometric nodes, pivot = value at the next node), the **exact inverse transform** η_n = Σ_k q^{(n−k)²}[n,k]_{q²} r_k with C′B = BC′ = I and the entrywise-positive Cholesky G = BDBᵀ, the **minimum-phase theta whitening** (innovation filters → a_r = (−q)^r/(q²;q²)_r in ℓ¹, A_q(z) = 1/(−qz;q²)_∞, exact identity |A_q|²·ϑ₃(θ/2,q) = (q²;q²)_∞ — the Szegő spectral factor of the q-Gaussian covariance; both editions' statements independently confirm the repaired sign convention), the **Schur-minor strict total positivity** (every mixed minor = q-power × Vandermonde × Schur polynomial > 0; oscillation-matrix and checkerboard-inverse consequences, Karlin cited), the **two-term jet tail** log P(A>x) = −γ_a√log x − (log(a/2)/(2 log a))·log log x + O(1) with the sharp Orlicz threshold E exp(θ√log A) < ∞ ⟺ θ < γ_a (boundary divergent), and the **highest-jet partial-theta law**: 𝒥_a = |h^{(N_a)}(Y)| has exact staircase tail with quadratic level inversion, reciprocal moments E𝒥^{−s} = p_a2^s a^{−s}·ϑ_p(2^{s+1}a^{−1−3s/2}; a^{−s/2}) (partial theta), and joint jet–distance transform whose s=0 limit degenerates to the distance-Mellin law — for s>0 the fractal pole lattice is replaced by an entire partial theta series; five new register conjectures (infinite dual tower with 1/ϑ₃ generating function, finite-section theta boundary layer, centered staircase limit set, partial-theta recreation of the complex dimensions, graph-directed Gaussian-binomial prediction) plus the transcendental-dichotomy sharpening of the algebraic-breakpoint conjecture; and by the sixteenth- and seventeenth-wave same-topic twins `Fabius_Q_Connections_Report/` (*Beyond the Dyadic Fabius Web*) and `Signed_Reciprocal_q_Fabius_Frontiers/` **merged editorially** as Part VII (*Signed and Reciprocal q-Fabius Frontiers*): the geometric-uniform family Y_q=(1−q)Σqʲ U_j on the full Klein-four orbit {q,−q,q⁻¹,−q⁻¹} — affine sign conjugacy Y_{−a} =d λ_a Y_a − β_a (λ_a=(1+a)/(1−a); no new normalized shapes at negative q), the reciprocal meromorphic germ with M_q(t)M_{1/q}(−t)=1 and finite digit-reversal duality Y_q^{[m]} =d Y_{q⁻¹}^{[m]} (giving q=±2,±4 exact finite/limiting meaning), geometric multisection Y_q =d Σ q^r/[m]_q·Y_{q^m}^{(r)} (Fabius = convolution of two quarter-base laws; u_{1/2}=u_{1/4}*2u_{1/4}(2·)) = Pochhammer dissection, the spectral q²-Pochhammer factorization ψ_q=∏_k((1−q)²t²/4π²k²;q²)_∞ with zero–pole exchange under inversion and base-b zero divisor 1+ν_b(n), cumulants κ_n=B_n/n·(1−q)ⁿ/(1−qⁿ) with spectral zeta ((1−q)/2π)^s ζ(s)/(1−|q|^s), log-concavity and the exact plateau phase |q|≤1/2 (crosswalked to Part VI's h_a plateau), the positive Laplace representation of reciprocal germs (moments on Re z=1/2, Hankel signature (−1)^{C(n,2)}, orthogonal polynomials with vertical zeros), the q-Fabius–Bernoulli Appell deconvolution family 𝔅_n^{(r)} (Bernoulli polynomials at r=0, centered monomials at r→1), the moment polynomial 𝒫_n(q)=(q;q)_n m_n/((1−q)ⁿn!) with degree C(n,2), boundaries 1/(n+1)! and B_n(1)/n!, and the odd-q-integer divisor conjecture ∏[d]_q | 𝒫_n (checked n≤16), the two-nome partition function Z_N(u,t;ρ,σ) unifying Gaussian layers and Prouhet cancellation (renormalized maximal Prouhet jet = the q-Fabius MGF; partial cancellations at root-of-unity nomes) plus the digit-position product Ξ_m(u,z;q) with position-parity companion χ(n) (4-state automaton), the exact q-Prouhet moment transfer S_{N,N+ℓ}=(−1)^N (N+ℓ)!/ℓ!·q^{C(N,2)}E T_{q,N}^ℓ ≡ general-radix Bell–Bernoulli, comb transport (sign=translation×parity, inversion=dilation), the Grassmannian/Hermitian finite-geometry square (Fu–Reiner–Stanton–Thiem) for both orbits, box-spline derivative combs with the quartic Cantor skeleton dim_H=1/2 and the comb factorization Δ_{q,2N}=Δ_{q²,N}*(D_q)_*Δ_{q²,N}, reciprocal q-Lagrange row reversal λ^{(q)}_{n,k}=λ^{(q⁻¹)}_{n,n−k}, the stop-loss simplex endpoint formula and exact inverse-geometric lattice G_q(qⁿ)=q^{C(n+1,2)}𝒫_n/(q;q)_n generalizing F(2⁻ⁿ) (new inverse-quartic values 1/6, 1/240, 1/51840, …) with all derivative jets G_q^{(r)}(qⁿ)=(1−q)^{−r}q^{−C(r,2)}G_q(q^{n−r}), the uniform two-term endpoint law log G_q = −ℓ²/2L − ℓ log ℓ/L + O(ℓ) and its √(2L log(1/y))−½ log log(1/y) inversion, and the RESOLUTION of the sixteenth wave's periodic-cocycle conjecture by Part VI's exact Γ–ζ Laplace decomposition (transform level closed uniformly in the base; density-level all-orders Lambert-W₋₁ transseries remains the shared open program, with the quartic phase conjecturally reconstructible from the dyadic one through decimation); the eighth-wave fold also repaired the volume's part-boundary section numbering; figures/data/scripts under `assets/` (absorbed source .tex files deleted after merging; SHA-256 provenance in the document) | absorbed drafts deleted; git history is the archive |



| *(all seven siblings merged and deleted)* | **The q-series sibling family is fully consolidated (2026-08-29).** Seven sibling drafts arrived through `drafts/incoming/` on 2026-08-28 — one 1106-line article-class survey and six book-class variants of 5663–6375 lines, all branched from the same monograph project, each appending its own "Fabius bridge". No sibling was a superset of the others (each carried 60–135 labels the rest lacked, out of 613 distinct new labels), so they were merged one measured pair at a time into `q_pochhammer_q_binomial_monograph/`, which grew from 96 pages; the sibling-consolidation snapshot was 210 pages (the later exact q=-1 crosswalk rebuild was 211 pages, and the current geometric-sinc crosswalk rebuild is 212 pages). Each was chosen as the closest remaining pair at the time: `q_pochhammer_q_binomial_monograph_bundle/` (0.942 against the filed monograph, its bridge part adopted wholesale); then `q_pochhammer_q_binomial_article-2/` with `q_pochhammer_q_binomial_monograph-3/` (0.680 against each other, merged jointly into the new Chapter 24, *Dyadic Gaussian–Thue–Morse structure and the values of F* — of monograph-3's 23 candidates, 4 were duplicates of article-2 items, 8 overlapped and are stated once in merged form, 11 were independent, and 7 of article-2's 10 items were absorbed); then `q_pochhammer_q_binomial_article/` with `q_pochhammer_q_binomial_monograph-2/` (0.588); and finally `q_pochhammer_and_q_binomial_coefficients-2/` (0.474), whose four bridge chapters contributed a ring-level residual principle valid over an arbitrary commutative ring with arbitrary weights and possibly repeated nodes, the exact formula on every dyadic cell, midpoint-centred truncations with an exact second-order rate, the off-grid continuation with its sharp uniform rate, the Appell polynomials of the Fabius law, and a digit-sparse Appell expansion at an arbitrary argument with exact residual; it also **corrected** a remark this monograph had adopted one merge earlier, on the admissible per-block shifts in the dyadic numerator. The 1106-line survey, `q_pochhammer_and_q_binomial_coefficients/`, was absorbed first and deleted last, once the two items deferred from it — the terminating ${}_2\phi_1$ reversal lemma and the classical limit of a nonterminating ${}_r\phi_{r-1}$ — had been integrated in corrected form. That third merge is the one that shows why the deduplication has to be re-run against the *current* monograph rather than the state the drafts were surveyed against: **15 of its 33 candidate results turned out to be already present**, nearly all of them in Chapter 24, which had not existed when those drafts were first examined. Of the rest, 1 was a duplicate of its own sibling, 10 overlapped an existing result and now replace it in strengthened form (notably the inverse-power value theorem, generalized from base 2 to every `0 < q < 1` **with the sharp threshold `q ≤ 1/2`** and strictness above it — a sharpness the monograph did not previously record), and 7 were independent. git history is the archive. (The first book-class sibling, `q_pochhammer_q_binomial_monograph_bundle/`, was **fully merged and deleted** on 2026-08-28: it was the closest pair in the whole `drafts/` tree by a wide margin — 0.942 combined label/section/theorem-name overlap with the filed monograph against 0.691 for the next pair — and after its bridge part was adopted, a residue audit found zero labels, sections, chapters, or atlas rows left in it, with the only remaining prose differences being places where the filed monograph is now strictly better. Its four genuinely unique paragraphs, the bridge reading-route signpost, the ProveIt/Zhong–Zhao/Eberl source-map paragraph, and the abstract's bridge clause, were carried across first.) | arrived through `drafts/incoming/` as six `.zip` archives and one bare `.tex`; the six archives were unpacked and deleted, the bare source was filed directly, and all seven sibling directories were deleted after absorption |

The old directory names, page counts, and uses of “current monograph” in the
preceding sibling-consolidation row describe its 2026-08-29 historical
checkpoint. That forward content now lives in
`q_pochhammer_q_binomial_monograph/` as part of the canonical synthesis listed
above.

## lambert-w — `lambert-w/`

The Lambert W function enters the corpus through the two-scale endpoint asymptotics and the phase-locked chain from `LambertPhaseLockedRichardson.lean` to the fixed-order analytic extractor `FabiusLambertPhaseExtraction.lean`; four independently written article packages on the function itself arrived on 2026-08-28 and were **merged editorially** into one volume.

The current compiled Lean crosswalk includes raw branch-point and full-domain continuity (`principalLambertW_continuousWithinAt_branchPoint`, `principalLambertW_continuousOn_Ici`, `lowerLambertW_continuousWithinAt_branchPoint`, `lowerLambertW_continuousOn_Ico`); the exact raw second-derivative formula, `W₀''(0) = -2`, full-domain principal strict concavity, and the lower branch's unique inflection at `-2 exp(-2)` with strict convexity through the branch point and inflection and strict concavity thereafter on the lower domain open at zero, all in `LambertWCurvature.lean`; generic phase continuity and exact interior second derivatives in `PowerExponentialLambertCalculus.lean` and `PowerExponentialLambertCurvature.lean`; the exact nonnegative-root iff `powerExponentialSaddle_eq_iff_eq_principal_or_eq_lower` with strict-interior distinctness `principalPowerExponentialPhase_ne_lowerPowerExponentialPhase`; and `PowerExponentialLambertAsymptotics.lean`, whose present scope is the principal-root equivalence, lower-phase divergence, and the intrinsic-epsilon two-term lower expansion.  The Fabius specialization also supplies the lower phase's exact inflection `2 exp(-2)/log 2`, strict convex/concave split, and the principal phase's strict convexity on the whole half-line ending at the peak through `PowerExponentialLambertFabiusCurvature.lean`.

`LambertWBranchPointGeometry.lean` has the exhaustive eight-theorem surface `tendsto_deriv_principalLambertW_branchPoint_atTop`, `tendsto_deriv_lowerLambertW_branchPoint_atBot`, `tendsto_principalLambertW_secantSlope_branchPoint_atTop`, `tendsto_lowerLambertW_secantSlope_branchPoint_atBot`, `principalLambertW_not_differentiableWithinAt_branchPoint`, `lowerLambertW_not_differentiableWithinAt_branchPoint`, `principalLambertW_not_differentiableAt_branchPoint`, and `lowerLambertW_not_differentiableAt_branchPoint`.  From the right of `-exp(-1)`, the principal derivative and endpoint secant slope tend to `+∞`, the lower counterparts tend to `-∞`, and neither branch has a finite right derivative or is differentiable there.

`LambertWBranchPointAsymptotics.lean` has the exhaustive one-definition/eight-theorem surface `lambertWBranchPointScale`, `lambertWBranchPointScale_pos`, `lambertWBranchPointScale_sq`, `tendsto_principalLambertW_add_one_sq_div_branchPoint`, `tendsto_lowerLambertW_add_one_sq_div_branchPoint`, `principalLambertW_add_one_sq_isEquivalent_branchPoint`, `lowerLambertW_add_one_sq_isEquivalent_branchPoint`, `principalLambertW_add_one_isEquivalent_branchPoint`, and `lowerLambertW_add_one_isEquivalent_branchPoint`.  The scale is `sqrt(2 exp(1) (z + exp(-1)))`, positive to the right of the branch point with square exactly `2 exp(1) (z + exp(-1))`; both squared ratios tend to `2 exp(1)`, both squared displacements have the corresponding asymptotic equivalence, and the signed leading laws are `W₀+1 ~ scale` and `W₋₁+1 ~ -scale`.

No finite endpoint derivative is asserted.  An `O(z + exp(-1))` remainder after the signed leading term, a convergent signed Puiseux expansion and its higher coefficients, named generic/Fabius phase wrappers for the derivative, secant, and square-root endpoint laws, the generic square-root threshold/strict-shape corollaries, a cleaned `L = log(A/x)` normalization, and the full generic asymptotic series remain open.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Lambert_W_Guide/` | *The Lambert W Function: A Real-Variable Guide* (62 A4 pp, consolidated edition, 2026-08-28) — editorial merge of the four independent treatments: the spine is the most complete article (branches, identities, exact branch-pair parametrization with Bernoulli gap expansions, derivative polynomials, integral calculus with all polynomial moments and Mellin integrals on both unbounded ends, local Taylor, Maclaurin with proved Lagrange–Bürmann, tree function/Cayley, signed Puiseux at the branch point with recurrences, unified Stirling-number logarithmic asymptotics for both branches, rigorous elementary bounds incl. Chatzigeorgiou's W₋₁ bracket, Padé and Euler continued fractions, Kalugin–Jeffrey–Corless cut integrals with complete monotonicity of W₀′, residual-certified branch-safe logarithmic Newton with monotone global starts, transcendental-equation catalogue, applications, Wright omega, complex-branch guide, problems with solutions, formula sheet); a complements section preserves the other three treatments' unique layers — the complete power-tower convergence theorem (exact interval e^{−e} ≤ a ≤ e^{1/e} with two-cycle exclusion and neutral endpoints), x^y = y^x, inverse-Taylor/Schröder corrections with branch-aware seeds, the logarithmic fixed-point iteration criterion (attracting iff \|W\|>1), branch-exchange involution, scaling identities, fixed points 2πin, unwinding-integer logarithm identity, closed Lagrange form of the Puiseux coefficients, square-root monodromy, the transcendence theorem (W_k(algebraic ≠ 0) is transcendental), a practitioner's toolkit (parameter gradients with the (1+w)^{−1} factor, differentiate-in-w, parametrize-by-w, floating-point hazards), further applications (patch residence via W₋₁, Wien displacement, linear-drag fall time, Schwarzschild tortoise inversion, π(x) < x/W₀(x)), and the r-Lambert/generalized-Lambert outlook; plus a corpus-role section and a four-way concordance appendix (all shared constants verified identical); the packages' figures/data/scripts live under `assets/` (absorbed article .tex sources deleted after merging; SHA-256 provenance in the document) | absorbed member packages deleted; git history is the archive |

The six polynomial-logarithmic transseries packages filed here on 2026-09-01
moved to
[`series-and-transseries/polynomial-logarithmic-transseries/`](series-and-transseries/polynomial-logarithmic-transseries/)
on 2026-09-02; their receipts are in that group's section below.

## series-and-transseries — `series-and-transseries/`

Packages whose subject is the formal-series calculus itself rather than a
single special function.  The group was split off from `lambert-w/` on
2026-09-02 in commit `85e3bca654ddcd9df92b12ec80ff29093790d9a8`: the six
polynomial-logarithmic transseries arrivals develop the algebra, division,
composition, and reversion of polynomial-logarithmic transseries and use
Lambert W only as their guiding example, so they are filed by that subject,
leaving `lambert-w/` to the articles about the function itself.  That move was
verbatim: no source, checksum ledger, or PDF changed.

The group now has four subgroups.  `polynomial-logarithmic-transseries/` holds
the operational treatment of one scale, consolidated into the single canonical
volume recorded below; `lambert-inverse-transseries/` holds three articles that
invert `x + W(x)`; `transseries-tutorials/` holds four general expositions; and
`special-function-inversion/` holds three articles that apply the Lambert-core
technique to several different special functions.  The first two overlap enough
that a later consolidation may merge them, but that comparison has not been
made, and neither has the comparison between the second and the fourth.

| Directory | Document | Previous path |
| --- | --- | --- |
| `polynomial-logarithmic-transseries/Polynomial_Logarithmic_Transseries/` | **Canonical, consolidation complete:** *Polynomial--Logarithmic Transseries: Algebra, Composition, Series Reversal, and the Lambert W Archetype* — 36{,}033-line/1{,}834{,}190-byte source (`2d57052c…5952c7`) and the 412-page A4 PDF built from it in the same three-pass run (4{,}504{,}362 bytes, `9d3dd9ad…06e1d5`) | Editorial merge (2026-09-02) of the six 2026-09-01 arrivals `Polynomial-Logarithmic-Transseries-1/`, `-2/`, `-4/` and `Polynomial_Logarithmic_Transseries-3/`, `-5/`, `-6/`, all from direct-arrival commit `730e1763…95ab4f`; absorbed sources deleted, git history is the archive, per-source receipts in the volume's provenance appendix |

The consolidation is complete.  The six arrival packages and their
retained historical PDFs were deleted once every source was absorbed and
a residue audit found nothing of substance outside the volume; git
history is the archive, and the volume's provenance appendix records
each source's intake and absorbed receipts, what it uniquely contributed,
and every convention reconciled against the notation catalogue.  The
canonical volume is A4 with Libertinus, which also clears the styling
debt recorded against the arrivals.  Lean crosswalking remains open and
is scoped in the volume's formalization register.

A second subgroup, `lambert-inverse-transseries/`, received three
independently written articles on 2026-09-02 that invert `f(x) = x + W(x)`
at infinity and develop logarithmic-transseries calculus around that example.
They are filed here rather than under `lambert-w/` for the same reason as the
first subgroup: the subject is the transseries method, with Lambert W as the
worked case.  Quick intake only; no comparison or review yet.

| Directory | Document | Supporting evidence | Previous path / provenance |
| --- | --- | --- | --- |
| `lambert-inverse-transseries/lambert_inverse_transseries/` | *Asymptotic Reversion of x + W(x) and a Calculus for Logarithmic Transseries* (1,846-line/61,003-byte source, 24-page/667,582-byte PDF) | none | `drafts/incoming/lambert_inverse_transseries.zip` (outer SHA-256 `8bef8fbbe36688daca7631bff16354dc486496cf49ce016e090fef64e86bf879`), filed 2026-09-02 |
| `lambert-inverse-transseries/lambert_inverse_transseries_bundle/` | *Reversing x + W(x): Exact Reduction and Logarithmic Transseries* (1,378-line/48,108-byte source, 21-page/299,709-byte PDF) | none | `drafts/incoming/lambert_inverse_transseries_bundle.zip` (outer SHA-256 `9c4ea8f8b2e7d0129aa95afaea5715cf629704e6c025bcc78729d38798756654`), filed 2026-09-02 |
| `lambert-inverse-transseries/reversing_x_plus_lambert_w_transseries/` | *Reversing x+W(x): Exact Reduction, All-Orders Asymptotics, and Logarithmic Transseries* (1,871-line/64,213-byte source, 28-page/332,829-byte PDF) | none | `drafts/incoming/reversing_x_plus_lambert_w_transseries.zip` (outer SHA-256 `4a628a31c4f95a1bafb85206ced18e341af7257afb53cf232dfe1489e237a867`), filed 2026-09-02 |

A third subgroup, `transseries-tutorials/`, was filed on 2026-09-02 from the
direct-arrival commit `e23bad1bb0ab91fea6df5a1cfd2525eea28dcb16`.  Its four
packages are general expositions of transseries rather than treatments of one
scale, so they are kept apart from both subgroups above.
No archive or checksum ledger was submitted; the receipts below are
repository-generated.  None of the four loads `docs/fabius-notation.tex`, so
all four are free of the notation-migration defect classes recorded against
their neighbours.  Comparison, deduplication, canonical selection, and
consolidation are deferred; see
[`series-and-transseries/transseries-tutorials/README.md`](series-and-transseries/transseries-tutorials/README.md).

| Directory | Document | Previous path / provenance |
| --- | --- | --- |
| `transseries-tutorials/Transseries_Tutorial-1/` | *Transseries Tutorial* — 5,159-line/188,639-byte source (`75f427b8…0fcd324`) and 143-page/793,390-byte Letter PDF (`81e6c8b0…f10b841a`) | bare arrival; direct-arrival commit `e23bad1b…28dcb16` |
| `transseries-tutorials/Transseries_Tutorial-2/` | *Transseries Tutorial* (second treatment) — 7,749-line/250,478-byte source (`50da0899…8d95ffb2`) and 164-page/817,544-byte Letter PDF (`4bc99417…39b26453`) | bare arrival; direct-arrival commit `e23bad1b…28dcb16` |
| `transseries-tutorials/Transseries_Tutorial-3/` | *Transseries for Mere Mortals* — 4,410-line/134,470-byte source (`26fb3f4a…5412c348`) and 121-page/656,187-byte Letter PDF (`8d34824a…5477bbf7`) | bare arrival; direct-arrival commit `e23bad1b…28dcb16` |
| `transseries-tutorials/Transseries_Tutorial-4/` | *Transseries Tutorial* (fourth treatment) — 8,781-line/344,893-byte source (`f00fe3aa…c1779105`) and 217-page/893,129-byte custom 522-by-738-point PDF (`6e2065d4…401fe4ba`) | bare arrival; direct-arrival commit `e23bad1b…28dcb16` |

All four tutorial PDFs are readable and unencrypted, every font row is embedded,
and none is Type 3 or Libertinus; three are Letter and one is custom
522-by-738-point, so canonical restyling is post-publication debt here too.

A fourth subgroup, `special-function-inversion/`, was filed on 2026-09-03 from
nine ZIP arrivals in two batches: the three of commit `5a453e1dc`, and six more
that arrived while that batch was being published and were taken in the next
quick-intake commit, as the gate requires.  Its articles invert a rapidly
growing special function at infinity to all orders: the map's dominant phase is
power-logarithmic, so ordinary reversion does not apply, and the first step is
to invert that phase exactly with the Lambert `W`-function, above which the
Stirling-type corrections generate a finer grid of transseries blocks.  They
are kept apart from `lambert-inverse-transseries/` because that subgroup treats
the single map `x + W(x)` in depth whereas this one applies the shared technique
across different functions; each of the three also extracts a general reversion
calculus, and whether those calculi coincide with each other or with the second
subgroup's is an open comparison, deliberately not made at intake.

All nine sources are LF with a final newline, so no normalization was applied
and the filed bytes are the submitted bytes.  Every archive passed a CRC check
and carried no absolute path, parent-directory traversal, or symlink entry; all
were deleted after unpacking, and git history is the archive.  All nine PDFs
are readable and unencrypted, produced by pdfTeX-1.40.26, with every font row
embedded and no Type 3 font.  Eight are A4, the canonical page size; one,
`inverse_subfactorial_transseries-3/`, is Letter.  Five carry Libertinus faces
and four do not, which together with that one page size are the subgroup's only
styling debts.  None of the nine loads `docs/fabius-notation.tex`, so all nine
are outside the notation migration.  The nine fall into three subjects — Gamma
and Barnes `G`, the hyperfactorial `K`-function, and the subfactorial — with
three independently written articles each; that grouping was recorded at intake
as provenance, and no comparison among them has been made.  A third batch of
three, filed 2026-09-03 in the same quick-intake mode, adds a fourth subject:
the inverse of a real-argument continuation of the Fibonacci function, whose
transseries is log-periodic (the golden-ratio phase) rather than Lambert-cored.
A fourth batch of twelve, filed 2026-09-03 the same evening, doubles the
subgroup to twenty-four members and adds four more subjects, again three
independently written articles each: the Butcher--Pólya rooted-tree numbers
(A000081), the double factorial, the partition numbers (A000041), and the
swing factorial (A056040).  Three of the four leave the single-gamma setting
that unified the first four subjects — the tree numbers are inverted through a
Pólya-tree singularity analysis, the partition numbers through Rademacher's
root-of-unity sectors, and the double and swing factorials only after a parity
split into two gamma-ratio branches, since neither sequence is the restriction
of one smooth interpolation.  All twelve nevertheless end at a Lambert-`W`
reversion of a power--logarithmic or exponential-power phase, which is why they
are filed here.  Every archive passed a CRC check with no absolute path,
parent-directory traversal, or symlink entry, and each held exactly one `.tex`
and one `.pdf` with no wrapping directory; the three Butcher archives ship
identical inner filenames and two double-factorial archives ship inner names
differing only in case, so distinct destination directories were created
explicitly and the pre-existing members verified intact.  All twelve sources
are LF with a final newline and were filed byte-for-byte, with no normalization
reported at staging; all twelve PDFs are readable, unencrypted, pdfTeX-1.40.26,
fully subset-embedded and Type-3-free; eleven are A4 and one is Letter; eight
carry Libertinus faces; two are `book` class.  Longest filed path 228
characters from the repository root.

Comparison, deduplication, proof checking, numerical reproduction and Lean
crosswalking are deferred; see
[`series-and-transseries/special-function-inversion/README.md`](series-and-transseries/special-function-inversion/README.md).

| Directory | Document | Previous path / provenance |
| --- | --- | --- |
| `special-function-inversion/Asymptotic_Inversion_Gamma_Barnes_G/` | *Asymptotic Inversion of the Gamma and Barnes `G`-Functions: Lambert-Core Transseries and a General Reversion Calculus* — 2,376-line/83,252-byte source and 29-page A4/646,225-byte PDF | `drafts/incoming/Asymptotic_Inversion_Gamma_Barnes_G.zip`, arrival commit `5a453e1dc`, filed 2026-09-03 |
| `special-function-inversion/inverse_k_function_transseries/` | *Inverting the K-Function at Infinity: Lambert--W Normalization, All-Orders Transseries, and a General Theory of Power--Logarithmic Reversion* — 2,259-line/66,867-byte source and 29-page A4/349,822-byte PDF | `drafts/incoming/inverse_k_function_transseries.zip`, arrival commit `5a453e1dc`, filed 2026-09-03 |
| `special-function-inversion/inverse_subfactorial_transseries/` | *Inverting the Subfactorial at Infinity: Bell-Sector Transseries, Inverse-Gamma Geometry, and a General Reversion Calculus for Rapid Cores with Tiny Oscillatory Tails* — 2,631-line/95,404-byte source and 38-page A4/688,626-byte PDF | `drafts/incoming/inverse_subfactorial_transseries.zip`, arrival commit `5a453e1dc`, filed 2026-09-03 |
| `special-function-inversion/inverse_gamma_barnesG_transseries/` | *Asymptotic Transseries for the Inverses of the Gamma and Barnes `G`-Functions: Lambert--`W` Normal Forms, All-Orders Reversion, and Residual Certification* — 1,655-line/72,966-byte source and 28-page A4/663,480-byte PDF | `drafts/incoming/inverse_gamma_barnesG_transseries.zip`, second batch, filed 2026-09-03 |
| `special-function-inversion/inverse_gamma_barnes_transseries/` | *Asymptotic Inversion of the Gamma and Barnes `G` Functions: Lambert-Normalized Transseries, Explicit Coefficients, and a General Power--Logarithmic Reversion Calculus* — 1,827-line/60,596-byte source and 25-page A4/324,795-byte PDF | `drafts/incoming/inverse_gamma_barnes_transseries.zip`, second batch, filed 2026-09-03 |
| `special-function-inversion/K_Function_Inverse_Transseries/` | *Asymptotic Inversion of the Generalized Hyperfactorial `K`-Function: Lambert and `r`-Lambert Anchors, Centered Bernoulli Structure, and a General Calculus for Power--Logarithmic Transseries* — 2,644-line/90,380-byte source and 33-page A4/724,630-byte PDF | `drafts/incoming/K_Function_Inverse_Transseries_LaTeX_and_PDF.zip`, second batch, filed 2026-09-03; **directory renamed from the archive stem** because the archive name pushed the PDF path to 263 characters, past the Windows `MAX_PATH` limit of 260, after which tools report a missing file that exists |
| `special-function-inversion/K_function_inverse_transseries_article/` | *Asymptotic Inversion of the Kinkelin--Bendersky `K`-Function: Lambert-Anchored Transseries for the Generalized Hyperfactorial and a General Theory of `x^p log x` Reversion* — 2,581-line/84,722-byte source and 30-page A4/743,783-byte PDF | `drafts/incoming/K_function_inverse_transseries_article.zip`, second batch, filed 2026-09-03 |
| `special-function-inversion/inverse_subfactorial_transseries-2/` | *Asymptotic Inversion of the Subfactorial: Bell-Number Tails, Inverse-Gamma Anchoring, and a Calculus for Exponentially Separated Transseries* — 2,188-line/73,742-byte source and 27-page A4/725,870-byte PDF; inner files are plain `inverse_subfactorial_transseries.*`, kept as submitted | `drafts/incoming/inverse_subfactorial_transseries-2.zip`, second batch, filed 2026-09-03 |
| `special-function-inversion/inverse_subfactorial_transseries-3/` | *Inverse Subfactorials at Infinity: Lambert--`W` Carriers, Bell-Number Sectors, and a General Calculus of Gamma-Dominant Transseries* — 1,878-line/81,203-byte source and 35-page **Letter**/530,302-byte PDF; inner files kept as submitted | `drafts/incoming/inverse_subfactorial_transseries-3.zip`, second batch, filed 2026-09-03 |
| `special-function-inversion/Fibonacci_Inverse_LogPeriodic_Transseries/` | *Inverting a Real-Argument Fibonacci Function: Log-Periodic Transseries, Exact Coefficients, and a General Product-Reversion Calculus* — 2,554-line/89,365-byte source and 33-page A4/787,646-byte PDF | `drafts/incoming/Fibonacci_Inverse_LogPeriodic_Transseries.zip`, third batch, filed 2026-09-03 |
| `special-function-inversion/fibonacci_inverse_transseries_article/` | *Log-Periodic Transseries for the Inverse of a Real Fibonacci Continuation* — 2,857-line/98,788-byte source and 36-page A4/797,090-byte PDF; inner files are plain `fibonacci_inverse_transseries.*`, kept as submitted | `drafts/incoming/fibonacci_inverse_transseries_article.zip`, third batch, filed 2026-09-03 |
| `special-function-inversion/fibonacci_inverse_transseries_article-2/` | *Inverse Asymptotics for a Real-Argument Fibonacci Function* — 1,884-line/64,334-byte source and 24-page A4/759,845-byte PDF; inner files are plain `fibonacci_inverse_transseries.*`, kept as submitted | `drafts/incoming/fibonacci_inverse_transseries_article-2.zip`, third batch, filed 2026-09-03 |
| `special-function-inversion/Butcher_Tree_Transseries/` | *All-Orders Asymptotic Transseries for the Butcher--Pólya Tree Numbers and Their Inverses* — 1,674-line/55,275-byte source and 21-page A4/593,560-byte PDF | `drafts/incoming/Butcher_Tree_Transseries.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Butcher_Tree_Transseries-2/` | *The Butcher-Tree Counting Transseries: All-Order Pólya-Tree Asymptotics, Lambert--`W` Reversion, and the Asymptotic Inverse of A000081* — 2,853-line/100,576-byte source and 62-page A4/763,748-byte PDF; `book` class; inner files are plain `Butcher_Tree_Transseries.*`, kept as submitted | `drafts/incoming/Butcher_Tree_Transseries-2.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Butcher_Tree_Transseries-3/` | *Asymptotic Transseries of the Butcher--Pólya Rooted-Tree Numbers: Bell-Polynomial Coefficients, Lambert--`W` Reversion, and Exponentially Small Singularity Sectors* — 2,382-line/91,654-byte source and 35-page A4/697,611-byte PDF; inner files are plain `Butcher_Tree_Transseries.*`, kept as submitted | `drafts/incoming/Butcher_Tree_Transseries-3.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Double_Factorial_Transseries/` | *Complete Asymptotic Transseries for the Double Factorial and Its Inverses: Bernoulli--Bell coefficient formulae, Lambert-`W` reversion, parity branches, and the periodic OEIS interpolation* — 1,552-line/52,202-byte source and 18-page A4/632,400-byte PDF | `drafts/incoming/Double_Factorial_Transseries.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Double_Factorial_Transseries-3/` | *The Double Factorial and Its Inverse: Complete Asymptotic Transseries, Borel Summation, and General Coefficient Formulae* — 2,287-line/79,355-byte source and 28-page A4/662,997-byte PDF; inner files are plain `Double_Factorial_Transseries.*`, kept as submitted | `drafts/incoming/Double_Factorial_Transseries-3.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/double_factorial_transseries-2/` | *Double-Factorial Transseries and Their Inversion: Bernoulli--Bell Coefficients, Lambert-`W` Cores, Parity Sectors, Borel Structure, and Discrete Inverses* — 2,138-line/63,319-byte source and 44-page A4/622,907-byte PDF; `book` class; inner files are lowercase `double_factorial_transseries.*`, kept as submitted | `drafts/incoming/double_factorial_transseries-2.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Partition_Number_Transseries_and_Asymptotic_Inverse/` | *Arithmetic Rademacher Transseries for the Partition Numbers: Exact Exponential Sectors, All-Order Coefficients, and Asymptotic Inversion* — 1,901-line/83,252-byte source and 32-page A4/369,259-byte PDF | `drafts/incoming/Partition_Number_Transseries_and_Asymptotic_Inverse.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Partition_Number_Transseries_and_Inverse/` | *Rademacher Transseries for the Partition Numbers and Their Inverse: All-order arithmetic sectors, coefficient formulae, Lambert--Lagrange reversion, and phase-locked inversion* — 2,020-line/72,533-byte source and 27-page A4/354,685-byte PDF | `drafts/incoming/Partition_Number_Transseries_and_Inverse.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Partition_Numbers_Transseries_and_Inverse/` | *Rademacher Towers and the Asymptotic Inverse of the Partition Numbers: Exact root-of-unity sectors, all-order coefficient formulae, Lambert--`W` reversion, and the discrete staircase* — 1,905-line/78,298-byte source and 33-page **Letter**/553,908-byte PDF | `drafts/incoming/Partition_Numbers_Transseries_and_Inverse.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Swing_Factorial_Transseries/` | *All-Orders Asymptotic Transseries for the Swing Factorial and Its Two Inverse Branches: Bernoulli--Bell coefficient calculus, Lambert--`W` normal forms, logarithmic reversion, and beyond-all-orders control* — 1,885-line/75,057-byte source and 28-page A4/688,586-byte PDF | `drafts/incoming/Swing_Factorial_Transseries.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Swing_Factorial_Transseries_Article/` | *The Full Asymptotic Transseries of the Swing Factorial and Its Inverse: Gamma-Ratio Normal Forms, Bernoulli--Bell Coefficient Calculus, Borel Geometry, and Lambert-Normalized Reversion* — 1,824-line/62,179-byte source and 25-page A4/666,609-byte PDF; inner files are lowercase `swing_factorial_transseries.*`, kept as submitted | `drafts/incoming/Swing_Factorial_Transseries_Article.zip`, fourth batch, filed 2026-09-03 |
| `special-function-inversion/Swing_Factorial_Transseries_and_Inverse/` | *Parity-Resolved Transseries for the Swing Factorial and Its Inverse: Exact Borel normal form, Bell-polynomial coefficient formulae, Lambert-`W` cores, and all-orders reversion* — 1,389-line/56,138-byte source and 22-page A4/326,626-byte PDF | `drafts/incoming/Swing_Factorial_Transseries_and_Inverse.zip`, fourth batch, filed 2026-09-03 |

## spectra-and-arithmetic — `spectra-and-arithmetic/`

A fifth subgroup, `sequence-transseries/`, was filed on 2026-09-03 from five
ZIP arrivals. Its articles derive the complete asymptotic transseries of a
classical integer sequence *forwards* from its exponential generating
function — two on the Bell numbers (saddle-point transseries about
`r = W_0(n)`) and three on the Fubini numbers (the vertical pole lattice of
`1/(2 − e^z)`) — so they are not inversions and are kept apart from
`special-function-inversion/`. Each archive held one `.tex` and one `.pdf`
with no wrapping directory; two shipped the same inner file name, and the
distinct archive stems name the directories. Longest filed path 252
characters. All sources LF with a final newline; all PDFs fully embedded,
Type-3-free, pdfTeX-1.40.26. None loads `docs/fabius-notation.tex`. Quick
intake only; see
[`series-and-transseries/sequence-transseries/README.md`](series-and-transseries/sequence-transseries/README.md).

| Directory | Document | Previous path |
| --- | --- | --- |
| `sequence-transseries/Bell_Number_Asymptotic_Transseries/` | *The Full Asymptotic Transseries of the Bell Numbers* — 2,211-line/78,882-byte source, 32-page A4/724,026-byte PDF; 6 theorems, 2 propositions, 2 lemmas, 1 corollary, 2 definitions in 18 sections | `incoming/Bell_Number_Asymptotic_Transseries.zip` |
| `sequence-transseries/Bell_Number_Transseries_Article/` | *The Full Saddle–Transseries Expansion of the Bell Numbers* — 1,714-line/60,076-byte source, 23-page A4/665,924-byte PDF; 7 theorems, 2 propositions, 2 lemmas, 2 corollaries in 17 sections | `incoming/Bell_Number_Transseries_Article.zip` |
| `sequence-transseries/Fubini_Number_Full_Transseries/` | *The Full Asymptotic Transseries of the Fubini Numbers* — 2,465-line/86,507-byte source, 33-page A4/741,812-byte PDF; 17 theorems, 2 propositions, 5 corollaries, 1 definition in 18 sections | `incoming/Fubini_Number_Full_Transseries.zip` |
| `sequence-transseries/Fubini_Number_Transseries/` | *The Complete Asymptotic Transseries of the Fubini Numbers* — 1,881-line/64,271-byte source, 25-page A4/699,100-byte PDF; 10 theorems, 2 propositions, 1 lemma, 3 corollaries in 16 sections | `incoming/Fubini_Number_Transseries.zip` |
| `sequence-transseries/Fubini_Number_Transseries_Article/` | untitled in source (exact identity `F_n = Γ(N)/2 · Σ_k ρ_k^{−N}`) — 1,472-line/57,681-byte source, 25-page Letter/490,186-byte PDF; 8 theorems, 1 proposition, 1 definition in 14 sections | `incoming/Fubini_Number_Transseries_Article.zip` |

Current source counts for unaffected rows still supersede their older intake
figures below: Dyadic Radon Profiles has 2,050 lines and a 29-page main PDF;
Fabius Pascal Frontiers has 1,926 lines and a 26-page main PDF; Carleman
Frontiers has 1,934 lines; and Gamma Duality has 1,297 lines.

The notation-source checkpoint for the affected rows is exact: Digital
Spectral Geometry has 1,940 lines, 61,049 bytes, and SHA-256
`92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`;
Automatic Scale Factorizations has 1,682 lines, 62,490 bytes, and SHA-256
`3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`;
Holonomic Frontiers has 2,251 lines, 85,256 bytes, and SHA-256
`75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`;
Reciprocal-Integer Convolution Divisors has 2,307 lines, 90,871 bytes, and
SHA-256
`e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e`;
Total Positivity has 1,060 lines, 58,362 bytes, and SHA-256
`e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`;
and the consolidated Spectra and Arithmetic source has 8,183 lines, 349,076
bytes, and SHA-256
`683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`.
No PDF was rebuilt for these notation edits.  Their retained publication PDFs
remain historical build artifacts, and this checkpoint supersedes contrary
source counts, obsolete checksum-parity language, or synchronization implications in
the long provenance rows below; arrival fingerprints remain unchanged.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Digital_Spectral_Geometry_and_Log_Periodic_Saddles/` | *Digital Spectral Geometry and Log-Periodic Saddles* (24 A4 pp and 1,963 source lines at arrival; retained historical 24-page A4 PDF; current notation-source TeX: 1,940 lines, 61,049 bytes, SHA-256 `92d98914722f98b37f84a19283536c8b3925584d0729920b6346a4f572c735b1`; with a 490-line arbitrary-precision numerical program, a generated TeX fragment and summary, three generated PNG figures, and a reproducible 161-line repository-audit program). Landed 2026-08-30 from the rootless `drafts/incoming/Fabius_Rvachev_Frontier_Report_Package.zip` (outer SHA-256 `0028cb4f47134574ba7cd698bfc0ec11f08776b320cbc82b8467bea20d865f6d`) under a collision-safe title directory: the generic report stem is already occupied by the unrelated q-series member. The delivered manifest's TeX/PDF size and hash entries verified, but its repository audit had read **zero** TeX files and its numerical generation had failed. Intake repair preserved those arrival records, made the script compatible with current mpmath, regenerated all requested outputs at 80 digits and completed a recursive screen of 188 prior TeX files, 390,119 lines, and 16,813,357 bytes excluding this package directory (raw corpus digest `bb8a7de4c16a960f8d640d99797085b4f17cd0cdcc38b38caa4014536806b4d3`; cluster hits 43/88/36/24/75/37; `repository_audit.md` SHA-256 `70e66ec477a46666b3acfe5d81123ebf50576b92b4f9d25deb6cf6a93d27b5fb`). No theorem-level novelty is accepted on intake: the divisor/zeta/count/heat/cumulant spine specializes Exponents I and Frontier Compilations II/VII; the exact `K`/Lambert/base-b layer occurs in Exponents VI; Appell reproduction/first defect occurs in Exponents VI and `Up_Polynomial_Synthesis`; Legendre--Bessel occurs in `Representation_Frontiers`; sub-Gaussianity occurs in Frontier Compilations V; and the endpoint/inverse program has a stronger inverse synthesis. Only minor corollary-level residue remains to assess. The report's all-orders saddle and inverse statements were downgraded for a missing uniform remainder, global Strang--Fix sharpness was restricted to the proved canonical Appell defect, and the false strict-curvature range was corrected using the `b=2` center flatness and `b>2` plateau. Report labels convey no Lean status. `BaseDigitMultiplicity.lean`, `WeightedScaleMultiplicity.lean`, and `SpectralZetaWeighted.lean` now provide an exact seven-declaration finite arithmetic crosswalk, without proving the analytic zero multiplicities, canonical product, or complex spectral-zeta identity. The rebuilt PDF uses the current primary document's canonical A4 package, theorem, macro, boxed-environment, and listing-style block verbatim apart from permitted PDF metadata and running-head text; four required local notation commands follow it. Its Libertinus fonts are embedded and subset, with no Type 3 fonts. The retained historical 24-page A4 PDF is 852,061 bytes (SHA-256 `a87074c73f97d7040dbc1e5cd665e5214fcefecec64426441152caf306201dba`), and its build-source TeX was 60,274 bytes (SHA-256 `6612eaca5ba7f1a29c863cf4faf24904d0a991056dee747388c39a40fde14880`). Historical intake recorded ten arrival hashes and a later 18-payload validation receipt (SHA-256 `35fc6b627c4ef6a0bad20636747954b4ddad01a28d9b9a6a98957735663410d8`); the subsequent source-only merge makes no operational checksum-verification claim | arrived through `drafts/incoming/`; archive unpacked here and deleted after validation |
| `Automatic_Scale_Factorizations_Rvachev_2026-08-30/` | *Automatic Scale Factorizations of the Rvachev Law* (retained historical 22-page PDF; current notation-source TeX: 1,682 lines, 62,490 bytes, SHA-256 `3e40fef5247ed3d7263ff885dc97159b456f26347614817fc18e087af647de90`; with experiment, data, figures, and audits), committed directly to the inbox by `8a184546747082cbd92ad4675fb61981c6b8c3b6`. The 21 historical payload hashes reflect six CSV LF-normalization changes and the repaired JSON final newline. It remains standalone pending comparison with the scale-factorization and spectral material already in the corpus; report labels do not imply Lean proofs | `drafts/incoming/Automatic_Scale_Factorizations_Rvachev_2026-08-30/`; filed here |
| `Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/` | *Dyadic Radon Profiles in the Fabius--Rvachev Web* (31 pp with experiment, data, figures, and audit), direct arrival `03b2f61889674f7d64ac86d3233236f5fa7ce660`. Its 26 historical payload hashes record nine CSV CRLF-to-LF normalization changes. The zero-profile, Pascal, and digital-sign strands await claim-level comparison and Lean crosswalk | `drafts/incoming/Dyadic_Radon_Profiles_Fabius_Rvachev_2026-08-30/`; filed here |
| `Fabius_Pascal_Frontiers_Report/` | *Automatic Spectra, Exact Dyadic Cubature, and Probabilistic Duals in the Pascal--Rvachev Hierarchy* (27 pp plus experiment/output payload), direct arrival `8a184546747082cbd92ad4675fb61981c6b8c3b6`. No checksum file was supplied; historical intake recorded hashes for all nine delivered files. Its substantial overlap with the consolidated Pascal--Rvachev hierarchy is deferred to the required second phase; manuscript claims are not Lean status | `drafts/incoming/Fabius_Pascal_Frontiers_Report/`; filed here |
| `fabius_holonomic_frontiers_report/` | *Holonomic Rank, Exact Overlaps, and Non-P-Recursiveness* (retained historical 30-page PDF; current notation-source TeX: 2,251 lines, 85,256 bytes, SHA-256 `75f2a36ee0ae4b68e17030536cd7aa2cd922fea8941ed023afb272fafd29b20f`; with certificates, experiments, and figures), direct arrival `6d6737530ec541196c506f95ec20a701a29872b3`. The 26 historical payload hashes reflect six CSV LF-normalization changes. Non-D-finiteness and non-P-recursiveness claims overlap the existing frontier corpus and remain unassessed at this intake stage | `drafts/incoming/fabius_holonomic_frontiers_report/`; filed here |
| `Fabius_Rvachev_Carleman_Frontiers_2026-08-30/` | *Critical Ultradifferentiable Geometry of the Fabius--Rvachev System* (24 pp with exact/high-precision experiment and figures), direct arrival `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. The 21 historical payload hashes reflect four CSV LF-normalization changes. Its derivative-growth and Carleman layers overlap the consolidated derivative-norm spectrum and same-batch q reports; comparison and formalization remain pending | `drafts/incoming/Fabius_Rvachev_Carleman_Frontiers_2026-08-30/`; filed here |
| `Dyadic_Spectral_Divisors_and_Gamma_Duality/` | *Dyadic Spectral Divisors and Gamma Duality* (22 pp with experiments, generated tables, and figures), direct arrival `d4605275f58f648ebcdeb74bc2ef5e4983abb6f0` under generic wrapper `Fabius_Rvachev_Frontier_Report-F/`. Its historically submitted three-entry inventory covered four payloads, while repository intake recorded hashes for all twenty delivered files. Zero-divisor, Laguerre--Polya, holonomicity, and moment claims remain separate pending semantic deduplication and Lean crosswalk | `drafts/incoming/Fabius_Rvachev_Frontier_Report-F/`; renamed and filed here |
| `Fabius_Rvachev_Reciprocal_Integer_Convolution_Divisors/` | *Reciprocal-Integer Convolution Divisors of the Rvachev Law* (retained historical 35-page A4 PDF; current notation-source TeX: 2,307 lines, 90,871 bytes, SHA-256 `e6e3d6df88efc3e50f7180b3853fdc6e4c9072f4e56192655bb76e195b282c4e`; with a 352-line exact/numerical experiment, six data files, four PNG figures, and a README). Landed 2026-08-30 from the rootless 14-file archive `drafts/incoming/fabius_rvachev_frontier_report_2026-08-30-B.zip` (outer SHA-256 `cfae82f303c3740bd76673fed772b1f69b9fedb0a911505360c930db7cc5a13f`). The repaired package has a title-derived pair, canonical A4/27 mm/Libertinus styling, deterministic LF CSV output, an exact three-pass build, with historical hashes recorded for its 14 payloads; all fonts are embedded/subset, no Type 3 font or overfull box remains, and key pages and figures were inspected. Its reciprocal-integer characteristic quotients, scale classification, digit cocycle, parity theorem, transport and inverse bounds, arithmetic zero divisor, spectral zeta, Thue--Morse quotient, and Stern/hyperbinary specialization form a distinct arithmetic/spectral layer. Adjacent `GeneralizedZeroDivisor` and `ReciprocalIntegerGammaZeros` APIs are crosswalked without upgrading the quotient family to Lean status. A temp-isolated unpinned Python replay reproduced four CSVs byte-identically, the summary modulo EOL, and the endpoint CSV within `1.1102230246251565e-16`; Matplotlib layout drift is recorded. The package remains standalone pending claim-by-claim integration; manuscript theorem labels do not imply Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Total_Positivity_Frontier_Report/` | *Total Positivity and Cartwright Geometry in the Fabius--Rvachev Dyadic Sinc Product* (retained historical 24-page PDF; current notation-source TeX: 1,060 lines, 58,362 bytes, SHA-256 `e7f05ac66a92284e82886bfe8b3376715ca0f71493a217d5a1adab6c17171475`; with a 153-line numerical/symbolic experiment script, three generated PNG figures, one generated TeX table, and four CSV evidence tables). Landed 2026-08-30 as the bare three-file directory `drafts/incoming/Fabius_Total_Positivity_Frontier_Report/`; it shipped no README, checksum inventory, environment pin, captured run output, or generated inputs. Arrival SHA-256 values are TeX `efea26060e6de63e97d00b982ca9e618f2234c88b8fd02f4ae9a8d63b7beecdd`, PDF `8f087969eaeb5eea349d64f6857f97356592c3464b9c3ecabcc9e5feec07630a`, and script `6674fa59e44fead9d41fb887e0634d8c363f816d1d2cceaf7886007db22d55fa`. The repository repair regenerated all eight missing outputs with the bundled script, normalized the source to A4/Libertinus, rebuilt it in exactly three passes with no Type 3 or overfull box, and added a README; historical hashes record the 12 payloads. Its imaginary-square-root transform, Laguerre--Polya/PF-infinity and multiplier-sequence program, exact zero divisor and Thue--Morse sign interpolation, Cartwright geometry, and geometric-scale deformation belong to the arithmetic/spectral Fourier-product theme. Its novelty screen is materially stale even at its pinned snapshot: `Frontier_Compilations/` Part V already contains the matching Laguerre--Polya/PF-infinity/shifted-Jensen layer, with zero-count and sign material elsewhere in that volume; the source now records that correction and the exact finite general-base digit-count crosswalk, without promoting its analytic zero-order or sign claims. It therefore remains separate pending claim-by-claim crosswalk and deliberate deduplication; report theorem labels record paper-level status, not current Lean proof status | arrived through `drafts/incoming/`; bare directory filed and normalized here |
| `Spectra_and_Arithmetic_Frontiers/` | *Spectral Arithmetic Frontiers of the Fabius–Rvachev System* (current notation-source consolidated TeX: 8,183 lines, 349,076 bytes, SHA-256 `683a560044772216980b05c4dd26957c6bbfb6c34019cc8d4cae815d9cff8df1`; retained PDF predates it, so no render parity is claimed) — consolidation (2026-08-28) of the former `Fabius_Half_Integer_Spectral_Frontier_Report/` (*Half-Integer Spectral Arithmetic*), `Fabius_Arithmetic_Rays_Frontier_Report/` (*Arithmetic Dyadic Rays*), `Spectral_Arithmetic_Pascal_Rvachev_Hierarchy/` (*Spectral Arithmetic and the Pascal–Rvachev Hierarchy*), and `Fabius_Derivative_Norm_Spectrum_bundle/` (*Derivative Norm Spectra and Dual Moment Geometries*); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## integration-and-transforms — `integration-and-transforms/`

| Directory | Document | Previous path |
| --- | --- | --- |
| `Integration_and_Transform_Frontiers/` | *Integration and Transform Frontiers for the Fabius–Rvachev System* (retained historical 377 pp, 12 parts) — consolidation (2026-08-28) of the former `Fabius_Antiderivatives_Report/`, `Fabius_Monomial_Antiderivatives_Report/`, `fabius_monomial_antiderivatives_report-2/`, `Fabius_Integral_Transforms_Report/`, `Fabius_Integral_and_Transform_Frontiers/`, `fabius_integral_frontiers_bundle/`, `Fabius_Rvachev_Integral_Frontiers/`, `Fabius_Integral_Transform_Fractional_Frontiers/`, `Fabius_Rvachev_Fractional_Integral_Report/`, `Fabius_Fractional_Integral_Transform_Frontiers/`, and `fabius_fractional_transform_frontiers_bundle/`, plus (folded in later on 2026-08-28 as Part XII by the same mechanical per-part step) the second-wave `Fabius_Integral_Transforms_Report/` (*Integral and Transform Calculus for the Fabius–Rvachev–Quantile System*: order-statistic spacings, beta–quantile lattices, dyadic resolvents, sinc energies, beyond-all-orders localization — an independent report sharing its directory name with Part IV's 2026-08-27 source); part order and former titles in the group README; assets under `assets/` (second-wave member under `assets/Fabius_Integral_Transforms_Report_second_wave/`), provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |

## inverse-and-sampling — `inverse-and-sampling/`

The canonical inverse synthesis and the information-geometry intake live
directly in this group; the comb synthesis lives under `comb-interpolation/`.
The former `analyticity-and-elementarity/` and
`inverse-asymptotics-and-computability/` layouts survive only through the
pinned pre-retirement snapshot and the canonical provenance ledger.

`Inverse_Fabius_Analyticity_Asymptotics_and_Computability/` is now the
canonical-source synthesis of five retired inputs pinned at
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`. Its master TeX inputs nine
chapter files. The reproducible raw source-result inventory passes 194/194
rows (projection SHA-256
`ff123825f7516adb1edfd9e738f9021d38c03960f0ea134554ede9e14cd8459f`),
and the reviewed `theorem_concordance.csv` preserves those ten immutable
source fields for all 194 rows. The structural validator passes with 748
labels and 593 references. Its current dispositions are 50 Lean-proved,
95 human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows. In particular, the centered Appell deconvolution,
positive-degree Appell mean-zero, and arbitrarily phased
polynomial-deconvolution rows have exact named Lean counterparts. The two
newest promotions are `is:p3:cor:forced-superconvergence` and
`is:p3:thm:Appell-lattice-reproduction`. The one-definition, eight-theorem
`RvachevSuperconvergentSynthesis.lean` module proves the parity-selected extra
degree for arbitrary nonzero natural meshes, its physical-coordinate
quadrature, deconvolved-polynomial synthesis, and the explicit
Rvachev--Appell specialization. Nine inverse-computability rows are now exact
as well: the main combined
theorem, the three tolerant-comparison certificates, fixed-depth bisection,
restricted sequential inversion, computable clamping, and the totalized
sequential corollary. `FabiusFunction.EffectiveGapInverse` closes the abstract
inversion row by deriving the reciprocal modulus from computable positive
rational forward gaps and proving subset sequential computability plus
effective uniform continuity; its companion theorem packages the clamped total
inverse.
`ASSET_DISPOSITION.csv` accounts for 88 source-group files, and the deduplicated
asset tree contains the 63 retained payloads. No operational checksum verification is claimed. The retained 134-page, 2,027,726-byte A4 PDF
has SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`.
It is a fully reviewed historical checkpoint, not a rendering of the current
23-input source closure; a fresh three-pass build is still required before the
publication gate or source/PDF synchronization can be called complete. PDFs
from the five retired source packages or migrated as evidence are likewise
historical/source assets.

The comb row below is superseded in its publication receipt. The unchanged
driver SHA-256 is
`63fb8372dbcb6c0b27eb7dea19e387dea27af23811df9fcfbe9313d37c8180a4`,
but the later canonical-notation edit in `chapters/03_additive_dyadic.tex`
postdates the retained three-pass 158-page, 2,456,105-byte A4 PDF with SHA-256
`81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`.
That artifact passed the log, A4/page, text, metadata, font, render, and visual
gates for its recorded source graph. The updated source and retained PDF remain distinct payloads; a fresh three-pass render
is pending, and full numerical replay remains separate reproducibility work.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Inverse_Fabius_Analyticity_Asymptotics_and_Computability/` | *Inverse Fabius Theory: Analyticity, Asymptotics, Computability, and Dyadic Sampling* — canonical editorial synthesis of five peer inputs. Its immutable extractor pin is `0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`; all 194 source-result rows are dispositioned (50 Lean-proved, 95 human-proved frontier results, 10 conjectures, 15 open problems, and 24 non-applicable environments). The newest exact rows include abstract effective inversion, `is:p3:cor:forced-superconvergence`, and `is:p3:thm:Appell-lattice-reproduction`. `ASSET_DISPOSITION.csv` accounts for all 88 source-subgroup files, while the deduplicated asset inventory lists 63 retained payloads. Five post-snapshot results are classified separately in `LEAN_CROSSWALK.md`. The retained, fully reviewed PDF checkpoint has 134 A4 pages and 2,027,726 bytes (SHA-256 `22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`). Its historical three-pass page, font, text, and visual gates and the independently checked current 23-input source closure are recorded separately in canonical `VALIDATION.md`; the source changed after that render, so a fresh build is required before synchronization is claimed. | At pre-retirement revision `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`: `analyticity-and-elementarity/Non_Elementarity_of_the_Fabius_Function/`; `analyticity-and-elementarity/inverse_fabius_iterates_nowhere_analytic/`; `inverse-asymptotics-and-computability/Inverse_and_Sampling_Frontiers/`; `inverse-asymptotics-and-computability/Inverse_Endpoint_All_Orders/`; `inverse-asymptotics-and-computability/Inverse_Fabius_Computability_Report/`. Nested predecessors and arrival archives are recorded in canonical `PROVENANCE.md`; Git history is the byte-level archive. |
| `comb-interpolation/comb_interpolation_synthesis/` | *Comb Interpolation and Sampling Frontiers: Additive and Geometric Combs in the Fabius--Rvachev System* — canonical editorial synthesis of the former additive-dyadic volume and the three geometric-comb manuscripts. Shared Gaussian--Pascal, Jackson--Newton, Lagrange, stability, Fabius-boundary, quadrature, interpolation, modal, Mellin, regular-variation, spline, reciprocal-product, Euler--Maclaurin, Ruffa, and Thue--Morse material is deduplicated or preserved according to its exact source disposition. Its 180-file inventory and the historical 151-row and current 138-row package inventories are recorded. The retained 158-page, 2,456,105-byte A4 PDF (SHA-256 `81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`) is a validated historical checkpoint; the current chapter-03 notation edit requires a fresh three-pass render before source/PDF synchronization is claimed. Full numerical replay remains separate reproducibility work. | Replaces `Dyadic_Comb_Frontiers/`, `geometric_comb_q_fabius_report/`, `geometric_comb_interpolation_report/`, and `geometric_comb_interpolation_report-3/`; original bytes remain in Git history. |
| `fabius_information_frontier/` | *Exact Information Geometry and New Frontiers for the Fabius--Rvachev System* (retained submitted 30-page A4 PDF; current 2,139-line TeX; a 601-line experiment, five data products, and three PDF/PNG figure pairs). Its 18 arrival hashes and 19 later payload hashes distinguish the submitted PDF from subsequent source changes. The information-geometry, entropy, Fisher-information, prefix-code, Thue--Morse, and endpoint layers remain archival manuscript claims pending hostile audit, numerical replay, an exact Lean crosswalk, canonical normalization, and rebuild; manuscript theorem labels do not establish formal verification. | `frontier-compilations/fabius_information_frontier/`; moved here by the thematic reorganization. |

The subgroup `dyadic-up-extraction/` received six reports on 2026-09-02, all
proving the same theorem — that at a dyadic point the finite sinc-product
spline is, after the point's depth, *exactly* the up-function value plus
finitely many geometric modes of ratio 4⁻¹, 4⁻², … — and all deriving the
same quarter-base Gaussian-binomial extraction row from it, under six
normalizations.  They were merged editorially on 2026-09-03 into one
canonical volume: one statement of each result, every proof completed, the
four index letters and three coefficient normalizations reconciled once, and
every rational number checked against the packages' captured verification
outputs.  The consolidation also proved what the packages had only
verified: the defect at the last level before the onset is a Thue-Morse
sign times a Bernoulli number, -eps_k 2^(-C(s,2)) B_s/s!, so the onset is
exact at even depth and improves by exactly one level at odd depth.  The
six directories and their retained arrival PDFs were deleted
after a residue audit; git history is the archive.  The volume's
formalization register records that the extraction row's algebra and the
exact cell identity at x = 1/4 are kernel-verified in Lean while the general
dyadic-depth theorem is not.  A byte-identical reship of
`rvachev_q_extrapolation_bundle.zip` had arrived alongside and was deleted
at intake.

| Directory | Document | Supporting evidence | Previous path / provenance |
| --- | --- | --- | --- |
| `dyadic-up-extraction/Dyadic_Up_Extraction/` | **Canonical, consolidation complete:** *Exact Dyadic Extraction of Rvachev's Up-Function from Finite Sinc-Product Splines* — 6{,}491-line/334{,}375-byte source (`1f3d0f03…86e582`) and the 77-page A4 PDF built from it in the same three-pass run (1{,}429{,}227 bytes, `26b967e4…72ede7`) | `verify_dyadic_up_extraction.py` (646 lines, `11f52767…44a322`): exact-arithmetic verifier adapted from the sixth arrival's, opt-in outputs, five added checks; every reduced dyadic point of depth ≤ 7 | Editorial merge (2026-09-03) of the six 2026-09-02 arrivals `Dyadic-Up-Extraction/`, `Exact_Dyadic_Up_Extraction/`, `Exact_Geometric_Tails_Rvachev_Up/`, `dyadic_up_extraction_package/`, `rvachev_q_extrapolation/`, `rvachev_up_dyadic_extrapolation_package/` from intake commit `8f822212d`; absorbed directories deleted, git history is the archive, per-source receipts in the volume's provenance appendix |

## representations — `representations/`

Series and orthogonal-expansion representations of the up-function.
Current source counts for the unaffected documentation rows are 1,542 lines
for forward iterates, 1,913 for Stein--Koopman, and 1,318 for Noncommutative
Frontiers.  The exact notation-source checkpoint for the affected rows is:
Dyadic Chaos, 3,153 lines, 112,391 bytes, SHA-256
`34241042a005ea529219aca0761c121760a2574324bbb2300c365012cc1435c2`;
Zero Bias, 1,926 lines, 72,231 bytes, SHA-256
`5b0eb2cf61123d5c9a6bd7ec5fdef5f7f09b2130ea02e3437d54f6dac2e27e42`;
New Frontiers-2, 2,978 lines, 122,235 bytes, SHA-256
`e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`;
and Shape/Divisibility/Stein, 2,057 lines, 83,124 bytes, SHA-256
`975ec7078562d88ba76c870ef1d90363380cbe422507762c305695b61f1c9bec`.
No PDF was rebuilt for these notation edits.  The associated PDFs remain
historical build artifacts; these fingerprints and that source-only boundary
supersede older counts and synchronization language embedded below, while all
arrival and historical build hashes remain unchanged.

| Directory | Document | Previous path |
| --- | --- | --- |
| `fabius_dyadic_chaos_frontier/` | *Dyadic Sensitivity and Polynomial-Chaos Frontiers for the Fabius--Rvachev Law* (34 pp at arrival; retained historical 40-page A4 PDF; current notation-source TeX: 3,153 lines, 112,391 bytes, SHA-256 `34241042a005ea529219aca0761c121760a2574324bbb2300c365012cc1435c2`; with a 672-line deterministic experiment, ten CSV/text products, six PDF/PNG figure pairs, and four audit files). Filed 2026-08-30 from `fabius_dyadic_chaos_frontier.zip` (1,351,045 bytes; SHA-256 `d57fd01c3991a6a7ecd6ba6e745729c745745d3265cb3cfd414aac1991b11b86`). The 30 immutable submitted payload hashes are retained as historical receipts; nine CSVs were normalized from CRLF to LF, and the historical checksum inventory recorded all 33 payload rows. Post-intake review repaired the zero-field, infinite-product, Mellin-continuation, phase-limit, mode-set, Thue--Morse-domain, and Lambert-cutoff statements; replayed the deterministic experiment in two compatible environments; and rebuilt the 40-page report plus six one-page vector figures with embedded fonts and no Type 3 fonts. Its label-complete crosswalk inventories all 36 nonconjectural results. None is Lean-formalized exactly as stated, but `ThueMorseSymmetricDifference.lean` supplies the exact two-definition and eleven-theorem Boolean-cube, polynomial, dyadic-sign, and report-grid algebraic boundary of `thm:TM-corner`; the repeated `C^N` integral clause and final report-shaped wrapper remain open. The orthogonal-chaos report remains standalone pending broader comparison and deliberate integration; manuscript result labels do not establish Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Zero_Bias_Frontier_Report/` | *Zero-Bias Towers and Spectral Peeling for the Fabius--Rvachev Law* (retained historical 26-page A4 PDF; current notation-source TeX: 1,926 lines, 72,231 bytes, SHA-256 `5b0eb2cf61123d5c9a6bd7ec5fdef5f7f09b2130ea02e3437d54f6dac2e27e42`; with an 839-line reproducible experiment, six CSV tables, and five dual-format figures). Filed 2026-08-30 from `Fabius_Zero_Bias_Frontier_Report.zip` (1,300,870 bytes; SHA-256 `fb8bbf8e34a2f5eb4e5bbe7b06b22566502be7583696f01960a6e41d25b518ee`); its 21 arrival hashes and later 23-payload hashes are retained as historical receipts. Hostile intake review separates existing moment/Fourier/shape infrastructure from the paper-level zero-bias tower, collision-free occupancy, spectral peeling, and limiting claims. The canonical A4/27 mm/Libertinus report and regenerated figures contain no Type 3 fonts and were rebuilt in exactly three strict passes | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `common_digit_fabius_zonoids_frontier_report/` | *Common-Digit Fabius Zonoids: Exact Volumes, Hyperbolic-Secant Geometry, Bernoulli Gaussianization, and Parameter Jets* (36 pp with code and generated assets), direct arrival `fef364bfd162f80919cd77b808530dd0734f1cb1`. Its 24 historical payload hashes reflect six CSV LF-normalization updates. The multivariate/zonoid layer remains standalone pending comparison and a Lean crosswalk | `drafts/incoming/common_digit_fabius_zonoids_frontier_report/`; filed here |
| `Jacobi_Digit_Fabius_Rvachev_Frontier_Report/` | *Jacobi-Digit Deformations of the Fabius--Rvachev Law* (32 pp with experiment, data, and figures), direct arrival `92c9909242ed6a2ab51d68ed816d1aa2a5339719`. All 38 submitted non-ledger hashes verify exactly. This distinct representation family remains standalone pending mathematical assessment and Lean formalization | `drafts/incoming/Jacobi_Digit_Fabius_Rvachev_Frontier_Report/`; filed here |
| `Matrix_Dilated_Fabius_Rvachev_Frontier_Report/` | *Matrix-Dilated Fabius--Rvachev Laws* (29 pp with experiment, data, figures, and audits), direct arrival `8a184546747082cbd92ad4675fb61981c6b8c3b6`. Its 27 historical payload hashes reflect seven CSV LF-normalization updates. The self-affine box-spline/zonoid layer remains separate from the common-digit report pending a claim-level crosswalk; manuscript claims do not establish Lean status | `drafts/incoming/Matrix_Dilated_Fabius_Rvachev_Frontier_Report/`; filed here |
| `Fabius_Rvachev_Noncommutative_Frontiers/` | *Noncommutative Cumulant Frontiers for the Fabius--Rvachev Law* (26 A4 pp, 1336 source lines; with a 681-line exact/high-precision experiment, ten result files, three dual-format figures, a README, and minimum-version requirements). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Noncommutative_Frontiers.zip` (outer SHA-256 `55f780d0780a693f2450fe6a4c8a63ba964b3d0e6fcea6d985040c6cb29e25cc`); all 21 payload checksums verified on arrival. The repository repair renamed the generic document stems, normalized four CSV writers and payloads to deterministic LF, selected PNG plot companions, adopted canonical A4/27 mm/Libertinus styling, and rebuilt the PDF in exactly three passes with all fonts embedded/subset and no Type 3 font; historical hashes record its 21 payloads. Its free and Boolean moment transforms, exact non-free-infinite-divisibility certificates, q-parametric Hankel obstruction, Jacobi stripping and increment program, finite-sinc cumulant transfer, and inverse-Fabius/Legendre/endpoint interfaces form a distinct noncommutative representation layer, with spectral-arithmetic cross-links. No exact or semantic duplicate of that layer was found. It remains standalone pending a claim-by-claim Lean crosswalk and deliberate consolidation; report theorem labels record paper-level status, not current Lean proof status | arrived through `drafts/incoming/`; archive unpacked, deleted, and package normalized here |
| `Fabius_Rvachev_New_Frontiers-2/` | *Fabius--Rvachev New Frontiers: Log-concavity, Native Orthogonal Polynomials, Christoffel Reconstruction, Rational Products for Pi, Gauss--Pade Structure, and Legendre--Gaunt Determinants* (current source with a retained pre-update 41-page A4 artifact; with a 580-line exact/high-precision experiment, three CSV tables, five clean vector figures and five supplemental PNG companions, a corpus audit, publication log, and PDF preflight). Filed 2026-08-30 from `Fabius_Rvachev_New_Frontiers-2.zip` (SHA-256 `9e27257d8b2808c6f24c754e61fbf5ce7b997233d78d33a28536600665508108`); all 15 arrival payloads verified and the fixed historical checksum scope was 20 payloads. The current crosswalk inventories all 129 declarations in eleven Gram, rational-Jacobi, determinant, rational-value, finite-Gaunt, and zero-row-square modules while retaining Nevai, J-fraction, Hankel, and Gauss--Padé material as inherited overlap. Lean proves executable rational Gaunt integrals, exact Legendre product linearization over `ℚ` and `ℝ`, the total integer-index zero-row square datum with central-binomial and factorial forms, sharp parity/triangle support and positivity, and finite rational and real Wigner-square Gram sums. It does not define a signed/general Wigner symbol or phase. Roots, Christoffel reconstruction/products, quadrature, Padé identification, infinite Jacobi products, and asymptotics remain paper-only. The current notation-source TeX has 2,978 lines, 122,235 bytes, and SHA-256 `e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`. The retained PDF was built from the former frozen source with SHA-256 `4eeea1a1cbe5497e6db3424a0c185f3a3be750f5816b22be5e7baed091753455`; exactly three strict passes (39/41/41 pages) produced the 780,141-byte PDF with SHA-256 `9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901`. Its 35 font rows are embedded/subset, five are Libertinus, and it contains no Type 3 font or raster image. Extraction retains the historical 99 public names, including all 25 predecessor Gaunt names; the current source adds 30 closed-form/wrapper declarations not rendered there. Targeted visuals and all five vector figures pass; the 20 source/artifact hashes are retained as historical receipts. The earlier 39-page cleaned-vector and 41-page local Gaunt checkpoints remain documented as history | arrived through `drafts/incoming/`; archive unpacked here and deleted; current source/retained PDF pair intentionally unsynchronized pending rebuild; historical hashes retained |
| `fabius_iterates_nowhere_analytic/` | *Nowhere Analyticity of Every Positive Compositional Iterate of the Fabius Function* (22 A4 pp, 1,566-line TeX; with a 469-line numerical diagnostic, four PNG figures mirrored between report/output directories, one CSV, metadata, README, and audit). Filed 2026-08-30 from `fabius_iterates_nowhere_analytic.zip` (SHA-256 `a1fbd4cf0a0fdd9479a2955bde0e7bcf5d4146032e4466916307826cfbe3bf0d`); all 14 arrival payload hashes and the later 15-payload hashes are retained. The semantic union retains 15 nonconjectural results, two numbered warning quarantines, and one live defect-spectral-gap conjecture. `PartitionDefect.lean` formalizes three definitions and 33 finite list-arithmetic theorems, but the set-partition, weighted Bell/spine, tie, and n≥2 iterate layers remain manuscript-only. The canonical A4/27 mm/Libertinus PDF was rebuilt in exactly three strict passes with every font embedded/subset and no Type 3 fonts | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Rvachev_Shape_Divisibility_Stein_Geometry/` | *Shape, Divisibility, and Stein Geometry of the Fabius--Rvachev Law* (retained historical 34-page A4 PDF; current notation-source TeX: 2,057 lines, 83,124 bytes, SHA-256 `975ec7078562d88ba76c870ef1d90363380cbe422507762c305695b61f1c9bec`; with a 466-line numerical experiment, three CSV tables, four retained vector-PDF figures plus four PNG companions, readable diagnostics, Makefile, requirements, and README). Landed 2026-08-30 from `drafts/incoming/Fabius_Rvachev_Frontier_Report_2026-08-30-C.zip` (outer SHA-256 `200e65588b824d05f863ec0dae50b983408af3a7a2cf000c55556560e8e49d2e`); all 14 submitted hashes verified. The repaired title-derived pair uses canonical A4/27 mm/Libertinus styling and embeds PNG companions; three `pdflatex` passes produced a 34-page PDF with all fonts embedded/subset, no Type 3 font or overfull box, and historical hashes for its 18 payloads. Its strict log-concavity, rootlessness, diffusion, and Legendre-jet strands remain paper-only and distinct, while scalar Stein-kernel, Bell-moment, shape, and endpoint material overlaps `Fabius_Stein_Koopman_Frontier_Report/`. The report now crosswalks the exact existing `rvachev_not_analyticAt` inputs separately from its prospective APIs and imports the stronger two-term endpoint theorem honestly. It remains standalone pending editorial integration; manuscript labels do not establish Lean status. The original 50-page Letter/Latin-Modern/Type-3 artifact is recoverable from history | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Fabius_Stein_Koopman_Frontier_Report/` | *Dyadic Stein--Koopman and q-Oscillator Calculus for the Fabius--Rvachev Law* (32 pp, 1929 source lines; with exact-symbolic and numerical experiments, five generated data files, two dual-format figures, a corpus audit, build/preflight records, and reproducibility metadata). Landed 2026-08-30 from `drafts/incoming/Fabius_Stein_Koopman_Frontier_Report.zip`; all 20 payload checksums verified. The report develops Appell Koopman eigenmodes, finite and Fock-space transfer determinants, q-Weyl calculus, Poisson/Stein resolvents, martingales and nonreversibility, an exact scalar Stein kernel in Fabius coordinates, and Lambert-periodic endpoint asymptotics. It remains a separate representation member pending claim-by-claim Lean crosswalk and deliberate consolidation; theorem labels record paper proofs, not current Lean status | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Representation_Frontiers/` | *Representation Frontiers for the Fabius–Rvachev System* (301 pp, 8 parts) — consolidation (2026-08-28) of all eight representation drafts. Parts I–III (first wave): `Fabius_Rvachev_Representation_Frontiers/` (*Fabius–Rvachev Representation Frontiers*: Jacobi coefficients, exact even moments, resolvent and logarithmic-derivative identities), `fabius_rvachev_representation_frontier/` (*Representation Atlas and New Analytic Bridges*), `Fabius_Rvachev_Multiresolution_Report/` (*Dyadic Multiresolution and Product–Series Representations*). Parts IV–VIII (second wave, folded in from the interim `Representation_Second_Wave/` volume on 2026-08-28): `fabius_rvachev_report_package/` (*Integral, Series, Product, and Operator Representations*), `Fabius_Rvachev_Polyphase_Representation_Report/` (*Polyphase, Operator, and Jump-Measure Representations*), `Fabius_Rvachev_Thue_Morse_Representation_Frontiers/` (*Sampling, Padé, Mellin, Resolvent, and Product–Integral Representations*), `rvachev_fabius_representations_2026/` (*Unit-Circle, Bessel, and Spectral–Monodromy Representations*), `Fabius_Rvachev_Multiresolution_Representations/` (*Dyadic Multiresolution and Sampling Frontiers*). The fold restored per-part arabic section numbering (the standalone second-wave volume let `\appendix` lettering run across part boundaries), restored the members' full part titles, and deduplicated colliding macros (all edits marked `% ed.:`); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts and the interim second-wave volume deleted; git history is the archive |
| `Up_Polynomial_Synthesis/` | *Exact Rvachev Up-Function Polynomial Synthesis* (60-page retained A4 PDF; 5,278 current source lines across a driver and three chapters; 80 theorem-like assertions, 80 proofs, and 80 one-to-one crosswalk rows: 25 + 16 + 17 + 22). Canonical editorial consolidation (2026-08-30) of three exact-polynomial, six Lagrange--Rvachev, and four Legendre--Rvachev packages, with repeated foundations deduplicated, exact Sturm evidence retained, and Lean anchors scoped claim by claim. The three earlier package payloads are under `assets/`; all 113 selected later-report payloads have canonical destinations and live hashes under `assets/companion-evidence/`, `assets/evidence/`, and `assets/provenance/COMPANION_PAYLOADS.csv`. The ten individual report directories were retired on 2026-08-31 after the exact gate passed; their source bytes remain recoverable at immutable commit `443793e846934e7363e314ea01129b9f50197a58`. | canonical volume; ten individual reports retired; current master plus three chapter sources are not yet recompiled; the current inventory lists every payload, including the retained 60-page PDF as a historical artifact |

Final post-union status for `Fabius_Rvachev_New_Frontiers-2/`: the row above
records the repaired package, whose filed TeX crosswalks the generic and
up-law determinant transports, executable rational Legendre coefficients and
Gram data, the exact low-order values leaf, and the generic/up-law finite Gaunt
modules.  The generic layer proves the
change-of-basis chain `G = Cᵀ H C`, upper-triangular `det C`, and the resulting
Gram/Hankel and Jacobi determinant ratios.  Its cross-ratio has no Hankel
nonvanishing premise only because division is total: a singular middle
determinant makes both sides zero, not a genuine nonsingular recurrence.  For
arbitrary `F : BoundedFabius`, the specialization proves the Legendre
determinant product, the empty-`0×0` convention `D_0 = 1`, the
leading-coefficient quotient, and the zero-based real Gram formula
`beta_(n+1) = ((n+1)/(2*n+1))^2 D_(n+2)D_n/D_(n+1)^2`.  Entry-as-integral,
strict positivity, rational casts, and the three real low-order transports
require `IsFabius F`; the rational leaf evaluates
`H_4 = 26727424/55791736875` and `beta_4 = 835232/4640643` exactly.  The new
Gaunt layer formalizes executable rational triple sums and their real-integral
casts, exact finite product linearization, parity/triangle-support zeros, and
finite up-law Gram-entry sums.  The downstream closed-form leaves define the
total integer-index zero-row square datum and prove its central-binomial and
factorial forms, all-degree Gaunt equality, sharp support/positivity, and finite
Wigner-square Gram sums.  Signed/general Wigner symbols and phase remain open,
as do Christoffel reconstruction, roots,
quadrature, Padé identification, infinite Jacobi products, and asymptotics;
`rvachevTranslateGram` is the separate unweighted shifted-up atom kernel.  Two
validated checkpoints remain historical evidence: the upstream 2,827-line,
39-page cleaned-vector build (35 embedded/subset font rows, five Libertinus,
no Type 3) and the local 2,864-line, 41-page Gaunt build (all 76 focused names,
including all 25 Gaunt names, with 20 historical payload hashes).  The
retained PDF's post-union source checkpoint was frozen at 2,863 lines with SHA-256
`4eeea1a1cbe5497e6db3424a0c185f3a3be750f5816b22be5e7baed091753455`.
That historical PDF has 41 A4 pages, 780,141 bytes, and SHA-256
`9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901`.
Its strict 39/41/41-page build, font/extraction gates, visual review, and
preflight all passed at that checkpoint.  The current 2,978-line,
122,235-byte source has SHA-256
`e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98`;
it and the later 20-row payload inventory are newer.  No rebuilt PDF is claimed,
and the two still older PDFs are historical only.

The CRLF/LF mismatch descriptions in the three rows above record the landing
state.  Their historical payload hashes record the repository-normalized LF bytes;
the original arrival bytes remain recoverable from git history.

## frontier-compilations — `frontier-compilations/`

Broad multi-topic "collected new results" reports, kept together as a
series even where a single title leans toward another group.

| Directory | Document | Previous path |
| --- | --- | --- |
| `Geometric_Uniform_Frontier_Directions/` | *Frontier Directions for Geometric-Uniform and Fabius--Rvachev Analysis* (30 A4 pp, 1,641-line TeX; with an 874-line reproducible experiment, ten CSV/text data products, eight dual-format figures, a hostile corpus audit, and validation records). Filed 2026-08-30 from `fabius_frontier_report_bundle-D.zip` (1,508,514 bytes; SHA-256 `39f3638f52f19955b88b7a865a60b76d9ce31154d98967d1400a6ad97396fa9a`); the 34 arrival hashes and later 36-payload hashes are retained as historical receipts. Exact tables replayed; floating outputs agree within the documented last-place/platform tolerances. The corpus crosswalk distinguishes existing geometric-uniform, q-moment, and Fabius infrastructure from the paper-level asymptotic, large-deviation, Edgeworth, zero-count, and periodic claims. The canonical A4/27 mm/Libertinus report and all vector figures contain no Type 3 fonts and were rebuilt in exactly three strict passes | arrived through `drafts/incoming/`; archive unpacked here and deleted |
| `Geometric_Uniform_Convolutions_and_New_Frontiers/` | *Geometric Uniform Convolutions and New Frontiers around the Fabius--Rvachev System* (1,656 source lines), delivered as one LF TeX source under the generic wrapper `fabius-frontier-report-H/` in direct-arrival commit `8a184546747082cbd92ad4675fb61981c6b8c3b6`. No PDF, README, code, data, figures, output, archive, metadata, or checksum file was supplied. Intake repaired three form-feed-corrupted `\frac` tokens and recorded the source hash. Its abstract says Python code accompanies the report, but none is present. Its broad q/Edgeworth, Thue--Morse, Bell--Bernoulli, valuation-zero, Fourier-zero, derivative-growth, non-Gevrey, and Lambert strands remain standalone pending compilation, claim comparison, and a Lean crosswalk; the package still has no PDF, the source has not yet been shown to compile, and manuscript labels do not establish Lean verification | `drafts/incoming/fabius-frontier-report-H/`; renamed and filed here |
| `Frontier_Compilations/` | *Collected Frontier Reports for the Fabius–Rvachev System* (retained 274-page PDF; current source not recompiled; ten absorbed reports; ten rendered parts) — consolidation (2026-08-28) of the former `Fabius_Rvachev_Frontier_Report/`, `-2/`, `-3/`, `Fabius_Rvachev_Frontier_Report_2026-08-27/`, `Fabius_Rvachev_New_Frontiers/`, `fabius_frontier_report_bundle/`, `fabius_frontier_results_bundle/`, `fabius_frontier_new_results/`, `fabius_frontier_spectral_endpoint_report_bundle/`, and `beyond_dyadic_fabius_web_report/` (source reports I–X render one-to-one as Parts I–X; former titles in the group README); assets under `assets/`, provenance with SHA-256 in the document | absorbed drafts deleted; git history is the archive |
