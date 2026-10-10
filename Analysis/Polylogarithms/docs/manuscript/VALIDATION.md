# Validation of the unified manuscript

Completed October 9, 2026. Authorship is **ProveIt Contributors** on the title
page and in the PDF metadata. The canonical [PDF](polylogarithms.pdf) has **228
pages, twelve chapters**, a literature appendix with 94 distinct historical
question leads, and 65 bibliography entries. It incorporates the original
39 drafts and all six nested continuation packages in the requested tree.
The recursive [inventory](source-inventory.json) contains **109 textual source
files**, including assembled/fragment versions and correction registers.
Their overlap is reconciled in the [editorial ledger](EDITORIAL-LEDGER.md).

The reviewed PDF SHA-256 is:

```
25769461206dcab29e42c584e3f15ed74c5bd638afdad044b36b390ca99f447c
```

## Source reconciliation and evidence integrity

All 109 source digests match; no textual source is unlisted or uncovered.
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

The numerical and exact evidence have different scopes; their counts are
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

The residual enclosure for S4 remains numerical evidence for a conjecture.
It is expressly excluded from the proved identities. The kernel-rate theorem
concerns uniform polynomial approximation, not a lower bound for every
possible polylogarithm algorithm. The published cubic Tornheim evaluation
and fixed-order moment expansion are attributed rather than claimed as new.

## Signed kernels, one-two closure and Holder certificates

The final synchronization added deliveries 18 and 19 to the Gaussian package.
Their shared formulas are fused with the earlier proofs. The new Chapter 5
organizes the signed density, unique angular zero, uniform four-term zero
asymptotic, one-sided Euler certificates, sharp logarithmic error, bounded
S4 obstruction and exact Holder computation. The all-odd-weight rank pattern
remains conjectural despite its finite exact census.

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

## Build and rendered review

Three serial LuaLaTeX passes exit successfully and have identical final
auxiliary/reference state. The final log contains zero unresolved references
or citations, duplicate-label warnings, overfull boxes, missing glyphs or
rerun requirements. See [build-results.json](verification/build-results.json).

The PDF text/bounds audit passes on all 228 pages. All pages were rasterized
and visually reviewed in fifteen contact sheets. Full-size review of selected
pages covered the Nielsen formula, mixed reductions, harmonic transition,
q=5 correction, uniform rank proof, normalized jets, zero expansions and
certificates, all five scientific figures, cubic certificate table,
version-specific external counterexample and bibliography. The collective author credit was checked on the rendered title and in
metadata. No clipping,
overlap or illegible layout defects were found. See
[pdf-inspection.json](verification/pdf-inspection.json); its full-page list
records rendered candidates, while this paragraph states the actual review
scope. The manuscript PDF is unchanged after that review.

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
