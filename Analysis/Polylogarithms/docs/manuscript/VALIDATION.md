# Validation of the unified manuscript

Research checkpoint, October 10, 2026. The broader research and integration
goal remains active. Authorship is **ProveIt Contributors** on the title
and in PDF metadata. The canonical [PDF](polylogarithms.pdf) has **375 pages,
twelve chapters, thirteen figures and 98 references**, with a literature appendix
preserving 94 distinct historical question leads.

The recursive [inventory](source-inventory.json) accounts for **381 textual
source files**, including assembled/fragment versions and correction registers.
The [editorial ledger](EDITORIAL-LEDGER.md) distinguishes integrated proofs
from incoming analytic claims still awaiting reconciliation. Twenty-one
incoming archives are preserved as **865 byte-identical members**. All 21
isolated package replay suites pass. The original drafts and initial
continuation evidence remain preserved too.
The imported arrival ZIPs have been retired from `docs/incoming` under
section 7 of its README. The last sixteen packages' 691 members were checked
against their original placement commits before their explicit Git removal.
[incoming-retirement.json](verification/incoming-retirement.json) records
each arrival, placement, destination and recovery path. Archive-preservation
validation now reads all twenty-one ZIPs from their pinned arrival commits.

The reviewed PDF SHA-256 is:

```
41c1ee04ffc80352d3d007a4779596fb9e1a7c46d5a2852945cf93ac65623d49
```

## New real-order proofs and fresh evidence

Chapter 5 now integrates the three overlapping real-order report cores into
one dependency chain: the finite signed-measure classification, positive
double kernel, complementary positive difference measure, global nonvanishing
and angular uniqueness, radial/Cartesian motion, Gaussian monotonicity,
critical defects, local signs and turning points, atomic edges, quantitative
mass concentration, and Euler certificates. The new written proofs establish:

- Nonvanishing on the principal slit plane away from the double origin for
  every a>=0,b>0, including orders below the finite signed-measure threshold.
- Positive Hausdorff differences and Bernstein interpolation precisely for
  a=0 or a+b<=1; strict normalized-radius increase throughout that domain.
- Strict Gaussian magnitude decrease in outer order and at every fixed total
  order; a unique nondegenerate axis maximum with exact bracket 1<b*<2.
- The sharp uniform Euler constant pi/4+log(2)/2 on the positive triangle
  a+b<=1. The rational budget 57/50 is valid there; the full-axis b=3/2
  comparison independently uses 5/4. General supercritical bounds have their
  stated separate scope.

The standard-library certifier checks **616** strictly positive difference
signs, **112** negative Euler increments, **3064** integer-root inequalities
and **seven** rational Gaussian enclosures at 192 Euler terms. The axis
case b=3/2 proves C(3/2)>227/200, used in the exact maximum bracket.
All seven independent native Wolfram evaluations at **100 working digits**
lie within those enclosures. Native quadrature remains a numerical diagnostic,
not interval quadrature. The 55-digit stationary-point solver and 180-point
plot are diagnostics; the displayed maximum's digits are not certified.

Three fresh isolated real-order replay suites pass. Their threshold replay
checks **nine** symbolic identities, **eight** exact Euler cases, **twelve**
exact angular brackets and **7430** integer-root inequalities. Geometry
diagnostics include nine independent kernel comparisons and sixteen zero
arcs; boundary diagnostics include twenty-one crossing rows at 90 digits.
Original code, figures, data and conjectural report wording remain unchanged.
The finite checks support the written proofs and do not replace them.

## Source reconciliation and evidence integrity

All 381 source digests match; no textual source is unlisted or uncovered.
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
The six-package intake brought that historical census to 248; the subsequent ten packages bring the current census to 381.

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

The 381-source inventory includes all new supporting prose, including material
whose canonical integration remains pending. Source coverage is therefore
distinct from completing every research item. The current book has **375 pages,
twelve chapters, thirteen figures and 98 references**. The hourly incoming-report
watch is active; it is configured to stay quiet on an unchanged, non-actionable
state.

## Build and rendered review

Three serial LuaLaTeX passes exit successfully and have matching final two
auxiliary/reference states. The final log contains zero unresolved references
or citations, duplicate-label warnings, overfull boxes, missing glyphs or
rerun requirements. See [build-results.json](verification/build-results.json).

The PDF text/bounds audit passes on all 375 pages. Every page was rasterized
and visually reviewed in twenty-four contact sheets. Full-size review covered
23 new proof, figure and research-programme pages, including the positive
difference measure, slit-plane factorization, endpoint Fatou argument,
Euler continuation, Gamma/Beta monotonicity, Mellin maximum proof, Cartesian
motion, critical defects, fractional turning points and two-scale boundary law.
The three added figures and their captions were reviewed at full size; ten
unchanged figures retain earlier full-size reviews and were checked in the
current sheets. No clipping, overlap or illegible layout defects were found.
[visual-review.json](verification/visual-review.json) records the actual
full-page scope; [pdf-inspection.json](verification/pdf-inspection.json)
records static checks and rendered candidates. The old 340-page whitespace
raster-equivalence receipt remains historical evidence and is explicitly
excluded from establishing review of the current expanded PDF.

## CM proofs, new conjectural vector and two additional incoming batches

The CM product and genus theorems now have written normalization proofs,
with positive roots, conductor corrections, unit counts and boundary phases
specified. Five Hilbert class polynomials and three labeled genus
factorizations have directed mpmath.iv coefficient enclosures combined with
CM integrality. These are interval certificates with stated analytic tail
bounds, not integer-relation fits. Eleven modular polynomials through weight
24 have exact rational q-expansion/Sturm certificates. Six seed radical
identities and positive-root choices have independent Fraction arithmetic.

New exact receipts establish two rational principal-lattice caps (yielding
|G_w(tau_D)| > 7/20), five additional lattice caps for all-weight quadratic
degree, and nine explicit weight-12/16/18 genus evaluations. The general
nonvanishing, norm, degree and cluster-set statements depend on their written
analytic and CM arguments. Non-elliptic CM nonvanishing is classical; the
explicit quantitative principal bound and ensuing genus extensions are the
additional development here. Two further interval certificates cover class
number one at discriminants -8 and -16. The discriminant -23 Weber resultant
is exact; an independent standard-library Frobenius/gcd certificate proves
irreducibility modulo five at discriminant -39, giving the degree-twelve
cube-root obstruction. See the `CM-*.json` receipts.

All **25 native Wolfram checks** pass at 90 working digits with a `1e-60`
relative residual gate: ten absolute class products, nine new genus ratios,
four individual values and two phase projections. This is independent
Fourier/gamma numerical corroboration, separate from the written proofs and
exact or directed-interval arithmetic.

The distinct new S8 vector has an exact primitive-coordinate check. The
signed/zero package independently reconstructs both its S6 and S8 rational
proximity certificates; the 1200-term direct scheme proves normalized
residuals below `1e-355`. Both intervals contain zero. **S6 and the new S8
identity remain conjectural.** The previously rejected S8 vector remains
rigorously rejected; these are different vectors and baskets.

The five third-batch replay suites (197 immutable members) all pass:
Herglotz, global Lerch phase, uniform transition, Lerch boundary and signed
continuation. The five fourth-batch suites (227 immutable members) also
pass: integral reflection jets, integral distributions, fractional Cayley
scaling, real-order threshold and golden/uniform continuation. The latter
includes independent raw-row verification, Smith calculations, binary
resolutions, fractional turning signs, real-order integer-root intervals,
golden seed/depth certificates and separately labeled notation diagnostics.
Their fresh outputs live in `third-replay/` and `fourth-replay/`.

Focused incoming corrections are integrated: Clausen index versus character
parity; failed numerical reduction searches versus nonreduction; the
published 1987 plastic-field sequel; exact reconstruction of L12; omission
of negative-factorial tail summands; and numerical versus proved ladder
status. The integral distribution/reflection proofs are now integrated as described
below. Real-order, Lerch, uniform, golden-seed and Herglotz theorem integration
is still explicitly pending. Finite replay does
not substitute for auditing and incorporating those proofs.

## Integral-distribution completion and multivariable research

Chapter 9 now reconciles the two incoming integral reports into one full
proof chain. It proves a fixed original-point basis and determinant-one
minor over the polynomial weight ring, arbitrary-ring base change,
a finite weighted resolution, the exact scalar reflection two-torsion,
all-field reflected dimensions, the characteristic-two Koszul model and
universal support, and the complete one-parameter Smith law. The integral
finite-jet torsion theorem and its torsion-module refinement are included,
with an explicit counterexample to jet-ring freeness of the torsion-free
reflected quotient. Endpoint conventions and the two-prime active parameter
A2(A2-1) are explicit. The complete level-twelve normal form and short
level-12/15/30 raw certificates give all-order polylogarithm, spectral-jet
and Hurwitz-Stieltjes identities, retaining the pole-cancellation term.

Further research gives a closed separable multivariable law. If the active
Koszul parameters are coordinate powers up to units, the reflected binary
dimension is n*product(L_i)+2^(r-1)*product(min(d_i,L_i)). Both integral
signs have free abelian rank n*product(L_i) and that second term as their
two-torsion multiplicity; the torsion modules themselves are specified.
The proof uses field Kunneth and the integral parity sums. It resolves this
separable family and does not assert a minimum-valuation formula for
arbitrary multivariable parameters or a splitting over the jet ring.

The independent `check_multivariable_distribution.py` constructs the
original prime and reflection rows in point/monomial coordinates without
importing an incoming normal-form or Koszul implementation. All **210**
finite binary matrix cases pass, including unequal lengths, zero powers,
both two-prime branches and a three-prime level. One corruption control
rejects omission of reflection rows. These finite checks test consequences;
the all-level theorem rests on the written proof. The two earlier incoming
integral suites and their independent Smith/resolution/product checks
remain valid for their unchanged byte-pinned code and data; they were not
rerun merely because the canonical prose was integrated.

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
