# Validation of the unified manuscript

Research checkpoint, October 9, 2026. The broader research and integration
goal remains active. Six new packages have been preserved and replayed;
audited results are integrated below, while CM, Lerch and angular material
is still being reconciled. This validation is for the current artifact.
 Authorship is **ProveIt Contributors** on the title
page and in the PDF metadata. The canonical [PDF](polylogarithms.pdf) has **298
pages, twelve chapters**, a literature appendix with 94 distinct historical
question leads, and 79 bibliography entries. It incorporates the original
39 drafts and all eleven nested continuation packages in the requested tree.
The recursive [inventory](source-inventory.json) contains **248 textual source
files**, including assembled/fragment versions and correction registers.
Their overlap is reconciled in the [editorial ledger](EDITORIAL-LEDGER.md).

The reviewed PDF SHA-256 is:

```
da36e67251d6e82ea73f2902c0b1a34ad2cf9c30365ab88fa5df95c42794d200
```

## Source reconciliation and evidence integrity

All 248 source digests match; no textual source is unlisted or uncovered.
The static audit finds no duplicate labels or bibliography keys, missing
references/citations, missing TeX inputs or missing figures. See
[document-integrity.json](verification/document-integrity.json).

[source-sha256.json](verification/source-sha256.json) pins LF-normalized
canonical TeX and verification scripts. The
[dependency manifest](verification/dependency-sha256.json) pins the immutable
continuation code, data and figure dependencies and the fresh check receipts.
Its text hashes are LF-normalized and binary artifacts use raw SHA-256.
[receipt-integrity.json](verification/receipt-integrity.json) verifies these
hashes, successful recorded checks and agreement of the PDF with its build
and raster receipts. Integrity is distinct from rerunning a computation.

## Fresh mathematical checks

The following core receipts were produced during the preceding consolidation
and remain valid for the unchanged identities and inputs; they were not all
rerun in this incoming-report pass. The five new packages and native supplement
were freshly replayed below. The numerical and exact evidence have different scopes; their counts are
reported separately rather than combined into a theorem count.

| Replay | Fresh evidence | Arithmetic and scope |
|---|---|---|
| Native Wolfram core | **31/31** | 70-digit working precision; residual gate `1e-45` |
| Independent mpmath core | **67/67** | 65 digits; gates `1e-48`, high Stieltjes derivatives `1e-43` |
| Additional corrections | **5/5** | 65 digits; q=5 log-gamma, half-point Herglotz derivative, HPL endpoint, discarded Li0, corrected P4 display (printed 30-digit value uses `1e-29`) |
| Nielsen inversion | **4/4** | 55 digits; defining-integral checks for (n,p)=(1,1),(1,2),(2,2),(3,2), gate `1e-45` |
| Inverse-color double reduction | **64** partial-fraction identities, **18** mixed reductions, **4** survivor replacements, **5** Euler sums, **6** generator checks, **3** residue diagnostics | Exact coefficient identities plus 60-digit diagnostics; equality gate `1e-40`, maximum residual about `1.40e-60` |
| Uniform distribution ranks and bridges | **594** exact finite rank cases; **12** bridge cases | q through 20: 162 distribution, 108 anchored, 216 reflected, 108 divisor comparisons; numerical bridges through order 3 at 65 digits |
| Harmonic reflection and transition | **156** consistency checks plus **12** transition diagnostics | 63 exact composition identities, 40 exact envelope intersections, 8 rational intervals, 9 numerical odd formulas, 36 numerical reflections; numerical precision 65 digits |
| Stieltjes zero certificates | **30** outward integer interval evaluations | Scale `10^90`: 14 base signs for n=1..4 at k=1; 16 endpoints isolating n=1 roots at eight derivative orders through k=200, interval width `1e-20` |
| Spectral Stieltjes replay | **44** rational certificates, **40** exact recurrence comparisons, **40** positive signs; **16** tail diagnostics | Numerical tail checks at 55 digits; maximum observed error/bound ratio about 0.01122 |
| Cyclotomic symbols | Exact elimination for q=1..40; rank and J criteria through q=1000 | Integer regular representations; exact zero-conductor list and the version-specific preprint counterexample |
| Herglotz J evaluations | **25/25** | Independent direct quadrature at 65 digits, gate `1e-57`, maximum residual about `2.75e-64` |
| Herglotz intervals | **4** exact rational certificates | F(2), F(4), F(8), F(16); final interval width at most `1.11e-46` |
| Herglotz optimal truncation | **3** transition, **4** remainder, **2** independent gamma-quadrature diagnostics | 55-digit floating point with stated analytic tail bounds; bounded quick configuration |
| Modular rows and CM jets | **18/18** | 4 row identities, 10 CM cases, 4 tail checks; 65-digit arithmetic, 36 rows |
| Cubic class numbers | **5/5** finite arithmetic certificates | Exact integers: Dedekind/index/splitting/generator-norm premises for the stated Minkowski proof |

Individual configurations, residuals and endpoints are retained in
`verification/`; [REPRODUCTION.md](verification/REPRODUCTION.md) gives commands.
The core checks include all seven displayed golden ladders at weights 5–9,
all five Gaussian weight-six reductions, harmonic sums, rational polygamma
grids, Herglotz families and derivatives, corrected Gamma1(1/3), negative-order
polygamma and the signed regulator candidate. The native high-weight g51
`MultiplePolyLog` attempt exceeded its 90-second limit; the accepted native
check uses an independent iterated integral.

The independent checks rejected an initially proposed editorial change to
W(12). The source coefficient was restored and derived explicitly:
`W(12) = 11 sqrt(3) Cl2(pi/3)/9`.

The manuscript also supplies analytic proofs of the all-weight inverse-color
reductions, uniform character normal form, complete Stieltjes zero expansions,
cyclotomic symbol kernel and optimal Herglotz cutoff. A newly derived Nielsen
inversion formula repairs the draft's unsupported nonclosure inference;
its finite polynomial endpoint data and branch domain are explicit.
The q=5 log-gamma correction retains the required L'(-1,chi5) term. Formal
five-term reduction, exact relation-system ranks, numerical period dimensions
and conjectural Stark predictions are kept distinct.

## Gaussian continuation and collective authorship

The subsequently merged sixth package contains four overlapping deliveries,
14–17. Their shared parity/shuffle reductions are presented once with proofs;
stronger triples, algebraic ladder certificates, log-gamma moment analysis and
certified evaluators are integrated in Chapters 3, 4 and 7. Six additional
literature references are integrated; the key analytic attributions were
checked against primary author sources.

Fresh replays in `verification/gaussian-replay/` include:

- **511** exact word re-expansions and **45** bigraded sectors through weight 9.
- **35** exact algebraic ladder substitutions and row/log-tail checks; numerical
  ladder diagnostics at 100 and 200 digits.
- **64** independent double/one-two quadratures at 65 digits, maximum residual
  about `1.08e-64`, plus exact symbolic checks of five doubles and three triples.
- Exact reproduction of the cubic-moment certificate at Taylor order 360 and
  integer scale `10^130`: width below `2.387e-113`, **112** common decimal places.
- **89** Chebyshev interval checks: 66 parity identities, 4 odd-weight shuffle
  instances, 18 resonant stuffle instances and 1 conjectural S4 residual. Also
  5,760 rational partial-fraction equalities (640 polynomial instances),
  82 Chebyshev polynomial/norm checks, and 8 independent quadratures.
- **6** exact rational midpoint rectangles with widths below `1e-70`;
  separate symbolic partial-fraction and matrix certificates.

That historical S4 residual enclosure is numerical evidence only. The later
rigidity package supplies the exact proof now integrated in Chapter 4;
the enclosure is not used as a proof step. The kernel-rate theorem
concerns uniform polynomial approximation, not a lower bound for every
possible polylogarithm algorithm. The published cubic Tornheim evaluation
and fixed-order moment expansion are attributed rather than claimed as new.

## Signed kernels, one-two closure and Holder certificates

The final synchronization added deliveries 18 and 19 to the Gaussian package.
Their shared formulas are fused with the earlier proofs. The new Chapter 5
organizes the signed density, unique angular zero, uniform four-term zero
asymptotic, one-sided Euler certificates, sharp logarithmic error, bounded
S4 obstruction and exact Holder computation. The all-odd-weight pattern was conjectural at that earlier checkpoint.
The current Chapter 5 now proves both original matrix ranks and the
Gaussian-supported saturation uniformly; the separately specified
product quotient retains its own proof and scope.

Part 18 freshly passes **588** exact/interval check cases at 400 Euler terms:
39 shuffle inverses, 56 kernel recurrences, 8 base derivatives, 384 Euler
weight/sign cases, 64 parity intervals, 15 finite formal ranks and the stated
coefficient/obstruction checks. Separate floating-point diagnostics cover
16 Euler-asymptotic cases, 9 zero-asymptotic cases, 9 illustrative root values
and 1 S4 comparison. Its interval for the S4 difference lies within
`[-1e-118,1e-118]`; this does not establish equality.

Part 19 constructs **75** rational Holder value certificates at 384-bit atom
precision. All 75 exact centers and tail budgets are reproduced by a separate
finite nested-sum implementation. The 58 formula residual enclosures are
compatibility checks alongside the independent written proofs. Its strictly
positive mixed-color antisymmetry certificate supports the corrected color
exchange rule. The homogeneous weight-six diagonal, the order-one logarithm
exception and the known shifted-polygamma parity component are also repaired.

Part 19b freshly generates **24** exact one-two coefficient rows and compares
them with defining integrals; checks **112** general closed-form cases; and
checks **56** sixth-root position/conjugation cases plus **4** explicit examples
at 100 digits. Maximum closed-form/integral residuals are about `5.14e-100`
and `6.59e-100`, respectively. These numerical comparisons are separate from
exact outward-rounded certificates. The top-two series-depth layers, signed
binomial coefficients modulo stated products, and sixth-root closure retain
their explicit branch and quotient hypotheses.

## Five incoming packages and fresh replay

The full original conductor-descent, distribution-jets, complementary-depth,
rigidity-and-reflected-moments and reflection-euler-tornheim packages are
preserved byte for byte: **174 archive members**, pinned in
[incoming-archives.json](verification/incoming-archives.json). Upstream's
flattened placement supplies twenty additional duplicate editorial fragments;
all twenty match originals after LF normalization. The archive bytes are
recoverable at the recorded immutable Git revision after upstream retired
the arrival ZIPs. The textual inventory includes these copies and the five
updated overview notes, for 179 provenance files at that checkpoint.
The current six-package research intake brings the census to 248.

All five isolated replay suites exit successfully; their commands, exact
parameters, original code digests and freshly produced result filenames are
in `verification/incoming-replay/*/replay-summary.json`. Originals are read
only; each run operates in an ignored scratch copy.

| New evidence | Fresh result and scope |
|---|---|
| S4 proof certificate | One convergent octahedral duality and **911** regenerated rational rows: 713 convergent double shuffle, 181 single-divergence regularized double shuffle, 17 lifted convergent distribution; **zero residual terms**. Written branch/convergence/regularization proofs justify the analytic schemas. |
| Complement rigidity/plastic ladders | **2,012** checks including four numerical diagnostics; **435** exact trinomial quotient irreducibility checks, degree census through 12, exact plastic substitutions and count identities. Universal classification follows from the cited trinomial theorem and the written proof. |
| Reflected moments and harmonic saddle | **119** exact reflected/Appell assertions; **16** late-coefficient, **9** moment-bound, **3** independent reflected quadrature and **24** saddle quadrature diagnostics. |
| Distribution and conductor descent | Distribution: **295** exact rank and **295** normal-form cases through q=60. Conductor: **295** exact ranks, **29** all-divisor and **18** symbolic jet cases, level-12 normal form, six principal next-jet coefficient calculations and the twisted level-260 leading coefficient. |
| Complementary depth | **511** exact trailing-zero re-expansions, **66** one-zero and **10** two-zero independent formulas, **142** catalogue entries (5,763 terms), **1,023** Lyndon checks, rank-7 triple matrix and three printed triple substitutions; **153** independent 75-digit diagnostics. An independent standard-library replay checks all 142 catalogue entries and six rational component widths. |
| Restricted cyclotomic quotients | **30** exact finite matrix checks at levels 3 and 4 through weight 16 corroborate the separate all-weight formal quotient proofs; evaluated-period independence is not claimed. |
| S6 candidate | **900** Euler terms, exact integer/fraction arithmetic and outward decimal endpoints enclose the frozen integer-vector residual below **1e-260**. Independent 220-digit Mellin and 300-digit Euler diagnostics support compatibility. **The identity remains unproved.** |
| Sharp moments, Herglotz jets and Tornheim evaluation | Six least-term moment diagnostics at 180 digits; **40** finite Herglotz derivative checks, 12 exact sample formulas, three arithmetic-sector comparisons, large-order/oscillatory diagnostics; independent Tornheim/log-gamma quadrature with analytic truncation budgets at 80 digits. These floating-point comparisons are separate from exact certificates. |
| Native Wolfram supplement | **5/5** at 70 digits, gate 1e-40: S4 defining integrals, principal level-30 trace orders 0/1/2, and the M11 reflected/Appell identity. No license-seat process termination was needed. |
| Cross-report sharp reflected remainder | **9/9** diagnostics at 180 digits for n=20,40,60 and m=1,2,3. The corresponding Chapter 8 corollary is proved for every fixed m by composition with the slit-disk inverse, cut-contour transfer and gamma concentration. No growing-m uniformity is inferred. |

The inspected June 27, 2012 CARMA author copy of Bailey–Borwein–Borwein
has an incorrect sign on the positive auxiliary Tornheim sum in equations
63 and 65. The canonical derivation uses the correct positive sign. This
audit does not assert that the same error occurs in the journal version or
the later author copy. The 2010 Amdeberhan et al. author preprint's log-sine
coefficient claim has an unconditional formal-polynomial proof here; no
unconditional uniqueness of numerical zeta/logarithm representations is
claimed. The even modified-polylogarithm assertion and the zeta(0) coefficient
label are also repaired.

Historical receipts and delivered script status strings can still call S4
conjectural: those strings describe the earlier report's scope. The current
canonical S4 statement is proved by the later exact certificate. The S6
status has not been promoted.

## Current research milestone: six further continuations

All **267** members of the six new packages are byte-preserved; their raw
hashes and arrival revision are in research-incoming-archives.json. All six
isolated replay suites pass. Their claims retain distinct proof scopes, and
a passing packaged suite does not promote every general theorem or imply
that all six packages have been fully integrated. The editorial ledger lists
the remaining analytic reconciliation explicitly.

The canonical additions are:

- The original specified-matrix rank conjecture is now proved by two
  polynomial reflection blocks, with full rational kernel, Gaussian-supported
  saturation, a membership certificate and an even-weight compiler. Fresh
  checks cover **40** weights (2-41), **210** even formulas, **816** affine
  row checks and **420** Gaussian membership checks. The kernel vectors have
  integer coordinates; no saturated integer-lattice basis is inferred.
- The S2 identity has its complete **25-row** certificate (23 double shuffle
  plus two convergent octahedral rows), independently replayed by two word
  implementations. Native Wolfram defining integrals check both its double
  and classical half-point forms at **80 digits**, gate **1e-45**.
- The complete fifth-index zero transition is integrated with its **22**
  endpoint and **8** whole critical-interval signs. The new sixth/seventh-index
  theorem proves counts **4,4,4,6,...** and **5,5,5,5,7,...**, all zeros simple.
  Both implementations pass **90** endpoint and **36** whole critical-interval
  enclosures. One uses scale 1e80 and 24 initial Hurwitz terms; the independent
  coefficient engine uses scale 1e100 and 32 terms. Their analytic remainder
  proof, global multiplicity bound and critical-point descent establish the
  global result. Numerical bracket proposals are never accepted as signs.
- The affine signed-moment error theorem is extended from integer to real
  outer order a >= 1 by the same Gamma-density variation proof. The rational
  implementation remains restricted to integer indices.
- Two convergent weight-seven shuffle rows give an exact Gaussian coordinate
  identity and prove equivalence of the earlier and Cayley S6 candidates.
  The rational coefficient check has zero residual, and a third native
  Wolfram check corroborates the identity at 80 digits. **S6 remains unproved.**
- The frozen S8 search vector is rigorously rejected by a rational residual
  interval lying near -1.3274179020580458e-86 and excluding zero. The N=1000
  replay recomputes all atom/residual endpoints exactly; its interval width
  is below 2.080e-290. This rejects only the explicit vector, not all possible
  relations or period independence.

Two half-unit proof errors (the duplicated endpoint phrase and P1/Q1
confusion) are corrected. The inherited profile figure is regenerated with
Q_n notation, and its previously undefined Gamma-expectation profile is now
specified. Its original source and plot remain intact; the new drawing and
package versions are recorded in zero-profile-redraw.json.

The 248-source inventory includes all new supporting prose, including material
whose canonical integration remains pending. Source coverage is therefore
distinct from completing every research item. The current book has **298 pages,
twelve chapters, nine figures and 79 references**. The hourly incoming-report
watch is active; it is configured to stay quiet on an unchanged, non-actionable
state.

## Build and rendered review

Three serial LuaLaTeX passes exit successfully and have identical final
auxiliary/reference state. The final log contains zero unresolved references
or citations, duplicate-label warnings, overfull boxes, missing glyphs or
rerun requirements. See [build-results.json](verification/build-results.json).

The PDF text/bounds audit passes on all 298 pages. All pages were rasterized
and visually reviewed in nineteen contact sheets. Full-size review of the current artifact covered the exact S6 coordinate
identity/reconciliation, real-order signed-moment proof, corrected Q_n profile
figure/caption, new fifth-index plot and sixth/seventh-index theorem, tables
and proof. The unchanged other figures retain their previous full-size review
and were checked again in the current sheets. No clipping, overlap or
illegible layout defects were found. The current collective title was checked
in the sheets and the PDF metadata. [visual-review.json](verification/visual-review.json)
records the actual current full-page scope;
[pdf-inspection.json](verification/pdf-inspection.json) records static checks
and all rendered candidates. The manuscript PDF is unchanged after that review.

## Limits of the evidence

These are ordinary mathematical proofs, exact finite computations and focused
numerical checks; no proof-assistant formalization or remote CI run is claimed.
Historical Smithereens searches are provenance, not fresh replays. The general
theorems rely on their analytic/algebraic proofs, not on finite checked ranges.
Floating-point checks and plots are not outward-rounded interval certificates.
Numerical candidates remain candidates where no proof is given. Unsuccessful
searches do not prove independence, non-elementarity or minimal depth.
Rohrlich completeness and Stark predictions retain their conjectural boundaries.
The external counterexample applies to the inspected 2020 author preprint;
the separately published 2023 version was not audited in this check.
