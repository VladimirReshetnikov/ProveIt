# Polytopes at Surreal Scales

**Lifting compression, truncation histories, affine residues, lattice counts, invisible extension complexity, mixed-volume tomography and realization, contact depth, omnific integer hulls, and infinite presentations**

This is a research report dated 30 September 2026, built from twelve
manuscripts in two write phases. The six manuscripts of batch 58, written
independently on that day in answer to one question about finite polytopes
over the surreal numbers, are Parts I–V (batch-58 write phase). Six further
manuscripts of the same day, batch 59, each continuing a theorem or
question of Parts I–IV, are Parts VI–X (batch-59 write phase). Each author
line reads "research manuscript", "research article" or "research draft"
prepared for Vladimir Reshetnikov, or (source 10) "for the ProveIt research
program"; batch-58 manuscript 04 adds "Developed with ChatGPT; independent
review and formalization pending", and source 13 reads "Prepared for
Vladimir Reshetnikov with ChatGPT".

Batch-58 manuscripts are called by their batch numbers 02–07, which equal
their file prefixes. Batch-59 manuscripts 01–06 would collide with those
numbers, so the report calls them by their file prefixes, **sources 08–13**.

| Source | Batch, manuscript | Archive (inner directory, main file; delivered PDF): title | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 05 | 58, manuscript 05, base | `surreal_liftings_research` (`surreal_liftings/article.tex`; 25 pp. A4): *Finite-Scale Geometry of Surreal Liftings* | `5e0f4e050` | `b30441a8c` | Part I, whole: Sections 2, 4, 6, 8–10, 13, 15–18, 20–25 |
| 02 | 58, manuscript 02 | `surreal_polytopes_research` (`surreal_polytopes/article.tex`; 28 pp. Letter): *Surreal Polytopes at Finite and Transfinite Scales* | `6996fee43` | `b30441a8c` | merged into Part I (Sections 3, 5, 7, 11, 12, 14, 19, parts of 13, 18, 21); Part II (Sections 26–31) |
| 06 | 58, manuscript 06 | `Surreal_Polytopes_Research_Package` (`Surreal_Polytopes/article.tex`; 27 pp. A4): *Surreal Polytopes: Affine Residues, Mixed-Volume Scales, and Simultaneous Segment Models* | `6996fee43` | `b30441a8c` | Part III, whole: Sections 32–45 |
| 03 | 58, manuscript 03 | `surreal_polytope_research` (`surreal_polytopes/surreal_polytopes.tex`; 28 pp. Letter): *Infinitesimal Boundary Geometry of Surreal Polytopes* | `6996fee43` | `b30441a8c` | Part IV, whole: Sections 46–61 |
| 07 | 58, manuscript 07, base of Part V | `surreal_polytopes` (`surreal_polytopes/surreal_polytopes.tex`; 26 pp. A4): *Invisible Complexity in Surreal Polytopes* | `6996fee43` | `b30441a8c` | Part V, whole (Sections 62–82) |
| 04 | 58, manuscript 04 | `surreal_polytopes_beyond_all_orders` (same name, `article.tex`; 26 pp. A4): *Beyond-All-Orders Extension Complexity in Surreal Polygon Geometry* | `6996fee43` | `b30441a8c` | merged into Part V (its own Sections 70, 71, 76, 77, 80, 81, the rest distributed) |
| 08 | 59, manuscript 01 | `surreal_mixed_volume_tomography` (same name, `article.tex`; 24 pp. Letter): *Mixed-Volume Tomography of Surreal Polytopes* | `6996fee43` | `f2cb2034e` | Part VI, whole: Sections 84–98 (two results printed once in Part III, Theorems 39.1 and 39.2) |
| 10 | 59, manuscript 03, base of Part VII | `surreal_mixed_volumes_research` (`surreal_mixed_volumes/article.tex`; 25 pp. A4): *Tropical Mixed Volumes of Surreal Polytopes* | `6996fee43` | `f2cb2034e` | Part VII, whole (Sections 99–119) |
| 09 | 59, manuscript 02 | `surreal_mixed_volumes` (`surreal_mixed_volumes/article.tex`; 28 pp. A4): *Finite Models and Real Degenerations of Surreal Mixed Volumes* | `b2b626d85` | `f2cb2034e` | merged into Part VII (subsections and sections marked "source 09", Sections 111, 113, 118, 119) |
| 11 | 59, manuscript 04 | `surreal_polytopes_contact_depth` (same name, `surreal_polytopes_contact_depth.tex`; 24 pp. A4): *Exponential Contact Depth in Surreal Polytopes* | `6996fee43` | `f2cb2034e` | Part VIII, whole: Sections 120–134 |
| 12 | 59, manuscript 05 | `Omnific_Integer_Hulls_Research` (`omnific-integer-hulls/article.tex`; 28 pp. Letter): *A Rational-Normal Dichotomy for Omnific Integer Hulls* | `6996fee43` | `f2cb2034e` | Part IX, whole: Sections 135–151 |
| 13 | 59, manuscript 06 | `Beyond_Finite_Surreal_Polytopes` (same name, `article.tex`; 26 pp. Letter): *Beyond Finite Surreal Polytopes* | `6996fee43` | `f2cb2034e` | Part X, whole: Sections 152–168 |

The batch-58 archives arrived in `b2b626d85`, the batch-59 archives in
`ed80eba06`. `6996fee43` is the commit of 30 September 2026, 16:07:39 UTC;
`5e0f4e050` is its second parent, and `b2b626d85` (17:24:44 UTC, the
batch-58 arrival) is its child. Archives 02, 03 and 07 of batch 58 wrap
inner directories of the same name, `surreal_polytopes/`, and sources 09
and 10 both wrap `surreal_mixed_volumes/`; they are different packages.
Manuscript 01 of batch 58 (on a Keller map) went to another report. No
batch-59 manuscript saw this report (it was placed after all six pins);
source 11 cites batch-58 manuscript 05 by title. The formalization roadmaps
of 05, 02, 06, 03 and 07 are printed together in Section 83; Parts VI–X
follow that chapter, so that no number of Parts I–V changed, and keep their
own formalization proposals inside the Parts.

**Status.** Twelve AI-assisted, unrefereed research manuscripts. Every
theorem has a written conventional proof in its source, and the programs
check finite examples only. **Nothing in this report is formalized**; no
independent proof review has been done; no manuscript claims literature-wide
priority or the solution of a named published problem.

```
README.md                                                     this guide
article.tex                                                   the report: standalone LaTeX, internal bibliography
article.pdf                                                   the compiled report, 353 pages (unnumbered title page,
                                                              contents pages 1-7, then pages 8-352)
02-transfinite-scales-proof_audit.md                          02's proof audit (delivered as notes/proof_audit.md)
02-transfinite-scales-sources.md                              02's source notes (delivered as notes/sources.md)
05-finite-scale-liftings-PROOF_REVIEW.md                      05's proof review
05-finite-scale-liftings-SOURCES.md                           05's source provenance
06-affine-residues-PROVENANCE.md                              06's provenance note
07-invisible-complexity-SOURCE_AUDIT.md                       07's source audit
07-invisible-complexity-verification-README.md                07's notes on its checks (delivered as verification/README.md)
08-mixed-volume-tomography-PROOF_AUDIT.md                     08's proof audit
08-mixed-volume-tomography-SOURCE_AUDIT.md                    08's source audit
09-finite-mixed-volume-models-SOURCE_AUDIT.md                 09's source audit
10-tropical-mixed-volumes-source_audit.md                     10's source audit
12-omnific-hulls-PROOF_AUDIT.md                               12's proof audit
12-omnific-hulls-SOURCES_AND_SCOPE.md                         12's sources and scope
13-beyond-finite-BUILD_REPORT.md                              13's build report (delivered as notes/BUILD_REPORT.md)
13-beyond-finite-PROOF_AUDIT.md                               13's proof audit (delivered as notes/PROOF_AUDIT.md)
13-beyond-finite-SOURCES_AND_SCOPE.md                         13's sources and scope (delivered as notes/SOURCES_AND_SCOPE.md)
code/02-transfinite-scales-Makefile                           02's build file (delivery paths; do not run here)
code/02-transfinite-scales-verify.py                          02's exact checks (standard library)
code/03-boundary-geometry-verify.py                           03's exact checks (standard library)
code/04-beyond-all-orders-build.sh                            04's PDF build script (delivery paths; do not run here)
code/04-beyond-all-orders-verify.py                           04's exact checks (SymPy)
code/05-finite-scale-liftings-verify.py                       05's exact checks (standard library)
code/06-affine-residues-Makefile                              06's build file (delivery paths; do not run here)
code/06-affine-residues-verify.py                             06's exact checks (standard library)
code/07-invisible-complexity-build.sh                         07's build script (delivery paths; do not run here)
code/07-invisible-complexity-verify.py                        07's exact checks, SymPy (delivered as verification/verify.py)
code/08-mixed-volume-tomography-build.ps1                     08's PowerShell PDF build (delivery paths; do not run here)
code/08-mixed-volume-tomography-build.sh                      08's PDF build (delivery paths; do not run here)
code/08-mixed-volume-tomography-verify.py                     08's exact checks in Q(t), SymPy (delivered as code/verify.py)
code/09-finite-mixed-volume-models-Makefile                   09's build file (delivery paths; do not run here)
code/09-finite-mixed-volume-models-verify.py                  09's exact checks, SymPy
code/10-tropical-mixed-volumes-build.sh                       10's build script (delivery paths; do not run here)
code/10-tropical-mixed-volumes-verify.py                      10's exact checks, SymPy
code/11-contact-depth-build.sh                                11's PDF build (delivery paths; do not run here)
code/11-contact-depth-verify.py                               11's exact checks (SymPy only for the reconstruction test)
code/12-omnific-hulls-Makefile                                12's build file (delivery paths; do not run here)
code/12-omnific-hulls-verify.py                               12's exact checks (standard library)
code/13-beyond-finite-Makefile                                13's build file (delivery paths; do not run here)
code/13-beyond-finite-verify.py                               13's exact checks (standard library; delivered as code/verify.py)
data/02-transfinite-scales-hexagon_example.json               02's hexagon: height rows and marked cells
data/02-transfinite-scales-universal_history_example.json     02's prescribed binary history and its jets
data/02-transfinite-scales-validation.json                    02's build and PDF-inspection record (notes/validation.json)
data/02-transfinite-scales-verification.json                  02's recorded run: 163,914 exact assertions
data/02-transfinite-scales-verification_run.txt               02's captured console output of that run
data/03-boundary-geometry-counts.csv                          03's lattice counts for n = 0..100 (CRLF, kept byte for byte)
data/03-boundary-geometry-verification.json                   03's recorded run
data/04-beyond-all-orders-requirements.txt                    04's pin, sympy==1.14.0
data/04-beyond-all-orders-verification.json                   04's recorded run: 114 of 114 checks
data/05-finite-scale-liftings-certificates.json               05's certificates and test results
data/05-finite-scale-liftings-verification_report.txt         05's run summary: 53 cases
data/06-affine-residues-verification.json                     06's recorded run
data/07-invisible-complexity-requirements.txt                 07's pin, sympy==1.14.0
data/07-invisible-complexity-results.json                     07's recorded run (delivered as verification/results.json)
data/08-mixed-volume-tomography-build_report.json             08's build record (describes the delivered 24-page PDF)
data/08-mixed-volume-tomography-requirements.txt              08's pin, sympy==1.14.0
data/08-mixed-volume-tomography-verification.json             08's recorded run: PASS, 3,196 assertions, seed 2026093017
data/09-finite-mixed-volume-models-requirements.txt           09's pin, sympy==1.14.0
data/09-finite-mixed-volume-models-verification_results.json  09's recorded run
data/10-tropical-mixed-volumes-fano_coefficients.csv          10's 84 Fano coefficients (CRLF, kept byte for byte)
data/10-tropical-mixed-volumes-rank_two_example.txt           10's rank-two realization example
data/10-tropical-mixed-volumes-requirements.txt               10's pin, sympy==1.14.0
data/10-tropical-mixed-volumes-verification.json              10's recorded run
data/10-tropical-mixed-volumes-verification.txt               the same JSON, captured by 10's build.sh with tee
data/11-contact-depth-requirements.txt                        11's pin, sympy==1.14.0
data/11-contact-depth-verification.json                       11's recorded run: 12,180 minors, k = 1..6
data/12-omnific-hulls-build_report.json                       12's build record (describes the delivered 28-page PDF)
data/12-omnific-hulls-verification_output.txt                 12's captured console output
data/12-omnific-hulls-verification_results.json               12's recorded run: all checks passed
data/13-beyond-finite-verification_results.json               13's recorded run: PASS, 28,890 checks
data/13-beyond-finite-verification_stdout.txt                 13's captured console output (the same JSON)
```

Not shipped: the manuscripts' own READMEs and PDFs; the member manuscripts
of batch 58 (02, 03, 04, 06, 07) and all six of batch 59, whose text is
printed in the article; and the checksum files (batch 58: 05
`SHA256SUMS.txt`, 06 `SHA256SUMS`, 07 `MANIFEST.sha256`; batch 59: 08, 12
and 13 `SHA256SUMS.txt`). They survive in the arrival commits `b2b626d85`
and `ed80eba06`. Manuscript 05's `article.tex` and `README.md` were staged as
delivered in `b30441a8c`; the merged `article.tex` and this README replace
them, and `article.pdf` is a build of `article.tex`. Delivery paths were
flattened at placement: 02's `notes/proof_audit.md`, `notes/sources.md` and
`notes/validation.json`; 07's `verification/README.md`,
`verification/verify.py` and `verification/results.json`; the top-level
`verify.py` and `verification.json` of 03 and 06; 08's `code/verify.py` and
`data/*`; 13's `notes/*.md`, `code/verify.py` and `data/*`; the top-level
scripts, Makefiles, outputs and audits of 09, 10, 11 and 12. Every file
received its manuscript's prefix.

## The report in brief

Three spines and ten Parts; Section 1 of the article is a guide, and its
Section 1.6 introduces Parts VI–X.

- **Part I, liftings of a fixed real configuration (05 base, with 02).** For
  a fixed real configuration of `n` labelled points of affine dimension `d`
  and surreal heights `h`, let `m` be the real rank of `c ↦ Σ c_i h_i` on
  the affine-dependence space (`m ≤ q = n−d−1`; 02 writes `p`). At most `m`
  monomial coefficient slices keep the leading term of every real
  dependence evaluation, for arbitrary set-sized Conway supports (05); the
  same selection agrees with every common initial normal-form cut (02). The
  complete sign type is an oriented partial flag of length `m`; its minimum
  polynomial germ degree is exactly `m−1`, or `m−r_0` with a prescribed
  standard part, while finite lifted data with the shadow need degree at
  most one, and the two can be arbitrarily far apart (05). Support-initial
  lifting histories are exactly the finite marked regular refinement
  chains, of length at most `n−d−1`, sharp for planar parabolic polygons
  (02). Also: explicit rational thresholds (both), toric initial ideals
  through Graver certificates and a halting-problem obstruction (05), a
  query-model bound, standard-part, polar and optimality-band identities
  and a finite Puiseux model (02), and corrections to a private draft (05).
- **Part II, coordinate-truncation histories (02).** Four bounded planar
  points with reciprocal convergent power series realize every prescribed
  triangle/quadrilateral history under common coordinate truncation from
  degree two on; `ω^{-ω}` selects either uniform final hull without changing
  any truncation; `f = (1+t)^{-1}`, `g = 1+t` already alternate forever.
- **Part III, affine residues and mixed-volume scales (06).** Over any
  set-sized real closed field `K ⊇ R` with its natural convex valuation (the
  surreal field only supplies examples): the scale lattice
  `L(P) = span_O(P − P)` and a full-dimensional affine residue `Res(P)` from
  a maximum vertex simplex, even when the standard part collapses `P`; for
  every finite family of polytopes, inner segments chosen on a finite
  rational grid preserve all mixed-volume valuations of distinct members at
  once, so pure mixed-volume valuation configurations are exactly the
  realizable determinant-valuation configurations; exchange-convexity of
  the full profile over any ordered value group; certificates with at most
  `d^d` determinants; probe classification and a `d+1`-measurement test
  (both also proved by source 08).
- **Part IV, real traces and lattice-point counting (03).** The real trace
  `Tr_R(P) = P ∩ R^d` has a finite lexicographic description with at most
  `d+1` levels per inequality; one-parameter algebraic descent keeps the
  trace, the shadow, the labelled face lattice and every lattice count;
  face implantation imports arbitrary lower-dimensional counting functions
  into a fixed rational shadow; for a lattice shadow, the second asymptotic
  coefficient and its full attainable interval (attained for simple
  shadows); a quadrilateral with the unit square's vertex shadows has
  `#(nP ∩ Z^2) = (n+1)^2 − ⌈αn⌉` for any irrational `0 < α < 1`, whose
  generating function has the unit circle as natural boundary and is not
  D-finite.
- **Part V, extension complexity beyond all orders (07 base, with 04).** For
  every `n ≥ 4`, two strictly convex `n`-gons with the same shadow, oriented
  matroid, all-order jets at `τ = ω^{-ω}` and leading slack data, one with
  linear and semidefinite extension complexity at most `2⌈log₂(n−2)⌉+2`, the
  other with `xc(xc−1) ≥ 2n` (07); on one circle, the regular `2^m`-gon and a
  cyclic `n`-gon agreeing below every power of `ε`, with
  `m ≤ xc(R_n) ≤ 2m` and `⌈√n⌉ ≤ xc(P°_n) ≤ min(n, ⌈24√n⌉)` (04). Such
  invisible gaps exist exactly when the jet scale's valuation is not an order
  unit (both); valuation rank two suffices and is necessary; residue maps
  can only lower complexity (07); real-algebraic transfer keeps it (04).
- **Part VI, mixed-volume tomography (08).** Source 08's displacement module
  is Part III's scale lattice, printed with Part III's letter `L(P)`. The
  valuation of a mixed volume is the least valuation of a colorful
  determinant of any finite generating lists (a form of Part III's
  determinant theorem with generator-count constants); one-body scale
  spectra are classified up to `GL_d(O)` and realized by boxes, and equal
  the valuations of the singular lengths; sharp partial and full stability;
  in the plane no fixed finite list of mixed-area probes recognizes every
  scale lattice, even with area, spectrum, shadow and full residue flag
  (Theorem 91.2), although Part III's reference-dependent `d+1` test does;
  for prescribed planar spectra the mixed-area values fill exactly
  `[a₁+b₁, min(a₁+b₂, a₂+b₁)]` (Theorem 92.1); a complementary-minor formula
  in higher dimension; polarity is module duality for symmetric bodies
  (Theorem 93.3).
- **Part VII, realization and obstruction of mixed-volume profiles (10
  base, with 09).** Parallelotope compression with at most `dm` generators,
  optimal (09); an exact realization criterion by canonical polarization and
  block mixing (Theorem 103.3); each weighted initial form is the real volume
  polynomial of a residue configuration, unique up to one element of
  `GL_d(R)` (Theorem 104.2, Proposition 104.5), so every exposed initial
  support is a real-representable polymatroid base set (Theorem 105.4); a
  matroid-type profile `γ(d − r_M(supp α))` is realizable exactly when the
  loopless matroid `M` is representable over `R` (Theorem 106.1); a strictly
  Lorentzian Fano cubic with 84 positive coefficients at three valuation
  levels has an unrealizable profile (Theorem 108.4); in the plane every
  finite-valued `M`-convex profile is realizable (Theorem 110.2); and a
  realizable profile need not have liftable leading coefficients, even up to
  a positive scalar (Theorem 109.2).
- **Part VIII, moving vertices and exponential contact depth (11).**
  Labelled Lawrence polytopes with `8k+16` vertices in dimension `4k+10`
  whose shadow keeps every vertex and the dimension, while every rational
  vertex arc preserving the labelled face lattice toward that shadow has
  homogeneous degree between `⌈2^k/(16k+48)⌉` and `2^k` (Theorem 120.3); the
  face lattice of any realization recovers cross-ratios with
  `x_{i+1} = x_i²` (Theorem 124.3); valuation and Puiseux-ramification
  identities; an addition-chain version (Theorem 128.2). Consistent with
  Part I's degree-one realization over a fixed real base, which it explains.
- **Part IX, omnific integer hulls and the rational-normal dichotomy (12).**
  For a fixed ordinary integer constraint matrix and arbitrary surreal
  right-hand sides, the omnific integer hull of a bounded polyhedron is
  generated by an explicit finite candidate set computed from one ordinary
  Graver test set (Theorem 141.2), for any integer part of any ordered field
  (Corollary 141.4); every such face lattice already occurs for an ordinary
  right-hand side with the same matrix (Theorem 142.4); finite generation and
  attainment for all boxed right-hand sides hold exactly when every nonzero
  row is proportional to a rational vector (Theorem 143.5); the 2–3
  knapsack hull in six residue classes (Theorem 144.2).
- **Part X, beyond finite presentations (13).** In a fixed NBG universe with
  global choice, "small" means set-indexed. Every face of a small hull is
  exposed (Theorem 155.3); faces of small halfspace classes are cut by at
  most `d` active rows (Theorem 156.2); a class that is both a small hull and
  a small halfspace class has finite subpresentations of both
  (Theorem 157.2), so definable small hulls are polytopes; polynomial
  exposure degree equals Martínez-Legaz's degree of non-exposedness
  (Theorem 159.2, credited) with a sharp family; the faces of the rational
  moment hull and of its vertex-free polar (Theorems 161.1, 161.2).

## Labels and numbering

Every label in `article.tex` carries the prefix `poly:`. Manuscript 05's 52
labels are `poly:` followed by the delivered name; the others carry a
sub-prefix before the delivered name: 02 `poly:ts:` (69 labels), 03
`poly:ehr:` (62), 04 `poly:bao:` (57), 06 `poly:mv:` (70), 07 `poly:ic:`
(75); 08 `poly:tom:` (78), 10 `poly:trop:` (77), 09 `poly:fmv:` (71 of 75),
11 `poly:cd:` (50), 12 `poly:oih:` (77), 13 `poly:bf:` (43). The batch-58
write kept all 385 delivered labels and added 46, for 431; **none of these
431 was renamed or deleted, and none changed its printed number** (checked
against the `.aux` of a build of the committed batch-58 text). The batch-59
write kept 396 of the 400 delivered labels and added 27, for **854** labels
in all, with no duplicate. Added:

- report: `poly:sec:batch59`, `poly:rem:degrees59`, and the Part labels
  `poly:part:tom`, `poly:part:trop`, `poly:part:cd`, `poly:part:oih`,
  `poly:part:bf`;
- Part VI: `poly:tom:rem:adaptive`, `poly:tom:rem:allprobes` (source 08's
  formulations of two results printed once in Part III);
- Part VII: `poly:trop:sec:reproduce` (10's unlabelled Appendix B), ten
  question labels `poly:trop:q:locus`, `q:cells`, `q:smallest`, `q:leading`,
  `q:quantitative`, `q:effective`, `q:compression`, `q:higher-rank`,
  `q:absolute`, `q:checker`, and `poly:fmv:rem:integer-mixing`,
  `poly:fmv:sec:degree-boundary`, `poly:fmv:q:hahn`, `poly:fmv:q:simultaneous`,
  `poly:fmv:q:general`;
- Part X: `poly:bf:app:notation`, `poly:bf:app:provenance` (13's unlabelled
  appendices).

**Dropped** (four equation labels of source 09 whose displays are printed
once under source 10's label; every reference was redirected, nothing else
cites them): `poly:fmv:eq:hessiancongruence` (→ `poly:trop:eq:hessian-congruence`),
`poly:fmv:eq:charpoly` (→ `poly:trop:eq:charpoly`), `poly:fmv:eq:block`
(= `poly:trop:eq:hessian-two-plane`), `poly:fmv:eq:fourpoint`
(= `poly:trop:eq:rank-two-plucker`).

A result printed once for two manuscripts carries both labels: in Part I
`poly:prop:stconv`/`poly:ts:prop:stconv` (with `poly:ts:eq:stconv`),
`poly:prop:slack`/`poly:ts:lem:slack`, `poly:thm:general`/`poly:ts:thm:transfer`
(and `poly:sec:general`/`poly:ts:sec:transfer`); in Part III
`poly:mv:thm:finite-probes`/`poly:tom:thm:adaptive` and
`poly:mv:thm:probe-classification`/`poly:tom:cor:allprobes` (source 08); in
Part V `poly:ic:lem:flat`/`poly:bao:lem:flat`, `poly:ic:thm:orderunit`/`poly:bao:prop:orderunit`,
`poly:ic:thm:residuenonnegative`/`poly:bao:prop:normalization`,
`poly:ic:thm:precision`/`poly:bao:thm:tolerances`,
`poly:ic:thm:conservativity`/`poly:bao:thm:algebraicrealization`,
`poly:ic:cor:scalar`/`poly:bao:prop:scalar` and
`poly:ic:sec:questions`/`poly:bao:sec:questions`; in Part VII the ten
section pairs, `poly:trop:thm:polarization`/`poly:fmv:thm:polarized`,
`poly:trop:cor:vertex-independent`/`poly:fmv:cor:sharp`,
`poly:trop:tab:fano`/`poly:fmv:tab:fano`,
`poly:trop:prop:fano-strict`/`poly:fmv:prop:fanoloren`,
`poly:trop:lem:fano-not-real`/`poly:fmv:lem:fanonoreal`,
`poly:trop:thm:fano`/`poly:fmv:thm:fano`,
`poly:fmv:lem:quadratic`/`poly:trop:lem:e2-not-volume`,
`poly:fmv:thm:quadratic`/`poly:trop:prop:amplitudes`,
`poly:trop:lem:rank-two`/`poly:fmv:lem:ranktwo`,
`poly:trop:thm:planar`/`poly:fmv:thm:quadraticprofiles`. Part VII's marked
pointer remarks to results printed in Part III carry the sources' labels
(`poly:trop:lem:positive`/`poly:fmv:lem:positive`, `poly:trop:lem:simplex-box`/`poly:trop:thm:compression`,
`poly:trop:lem:st-volume`/`poly:fmv:lem:shadow`, `poly:trop:lem:rado`/`poly:fmv:lem:rado`,
`poly:fmv:cor:allmconvex`), as do source 09's weaker forms kept as remarks
(`poly:fmv:lem:sandwich`/`poly:fmv:thm:compression`, `poly:fmv:thm:detmodel`,
`poly:fmv:rem:integer-mixing`). Citation keys carry the prefixes `fs:` (05),
`ts:` (02), `ehr:` (03), `bao:` (04), `mv:` (06), `ic:` (07), `tom:` (08),
`trop:` (10), `fmv:` (09), `cd:` (11), `oih:` (12) and `bf:` (13); 02's
Gonshor and Basu–Roy entries are printed under 05's keys, 04's Yannakakis,
Fiorini–Rothvoß–Tiwary and Kaibel–Pashkovich entries under 07's, and the
works cited by both 09 and 10 under 10's keys, with 09's own entry text
added (100 entries in nine lists, numbered consecutively).

Sections are numbered consecutively through the report: Section 1 is the
guide, Parts I–V are Sections 2–82, Section 83 collects the formalization
roadmaps of Parts I–V, Parts VI–X are Sections 84–168 (VI 84–98, VII
99–119, VIII 120–134, IX 135–151, X 152–168), and Appendix A is the
provenance. There is one theorem counter, numbered within sections
(cleveref types through `aliascnt`, as in 04), and equations are numbered
within sections, so no source number survives. Source appendices are
ordinary sections at the end of their Parts. Text added in either write
phase is marked `[write]`.

## Setting and notation

Each Part keeps its source's definitions and hypotheses and opens with a
paragraph "Notation in this Part"; Section 1.3 of the article has the
report-wide table of letters and words that change meaning between Parts,
with the reading to avoid. The conventions: every construction takes place
in a set-sized subfield `R ⊆ K ⊆ No` (real closed unless a Part says
otherwise); `ε = ω^{-1}` and `τ = ω^{-ω}` wherever a fixed surreal is meant,
except that Part III keeps 06's `η` for `ω^{-ω}`, because `τ_I` and `τ(α)`
are its mixed-volume profiles; `st` is the standard part on the one ring
`O` of finite elements (02 and 03 write `𝒪_K`); "affine residue" `Res(P)`
means only 06's renormalised residue, which is not the standard part; 03's
real trace `Tr_R(P) = P ∩ R^d` is not 07's matrix trace `tr`; 04's
"algebraic finite-accuracy shadows" are real-algebraic approximants, not
standard parts, and are printed as approximants.

In Parts VI–X (table rows marked `[write]` in Section 1.3): sources 08–10
write the natural valuation `ν`, the same valuation as Part III's `v`; in
Part VI `α(P)` is a one-body scale spectrum (elsewhere `α` is a
multi-index) and `τ = ν det B` the value of a reference volume; mixed-volume
profiles are Part III's `τ(α)`, 09's `h_P(α) = ν(c_α)` and 10's
`q_P(α) = ν(V_α(P))`; "compression" is 02's cut-compatible greedy
compression in Part I, Part III's one-parameter specialization, and Part
VII's parallelotope compression; Part VIII's `L(B)` is a Lawrence polytope,
its `m = 4k+8` a number of points, and its `τ` a Puiseux variable; Part IX's
`G_A` is the Graver set of `[A −I]` projected to `Z^d`, not Part I's Graver
basis of `ker_Z Ã`, and its `A` a constraint matrix; Part X's "small" means
set-indexed, and a small hull is in general a proper class. **Three
degrees** (Remark 1.4): Part I's least degree of a polynomial height vector,
Part VIII's homogeneous degree of a rational vertex arc, and Part X's degree
of non-exposedness; none bounds another, so Part VIII's exponential bound
does not contradict Part I's `m−1 ≤ n−d−1`.

**Three minimum degrees** (Remark 1.1). 05's "minimum degree `m−1`", 02's
"`r` layers" and 02's "one real vector" are three different invariants,
not three answers to one question: the complete real dependence sign type
(rank `m`, 02's `p`; germ degree `m−1`, or `m−r_0` with the shadow), the
strict geometric history along the cuts (`r ≤ m` strict steps, exactly `r`
layers), and the final finite data (one real height vector; degree at most
one with the shadow). Theorem 10.6 shows the first and the last can be
arbitrarily far apart; in 02's hexagon the first two both need three
layers, while the final triangulation needs one real vector.

**Valuation rank three and rank two** (Remark 1.2, Remarks 70.8 and 72.5).
07's single field of valuation rank three and 04's rank-two fields `K_n`
are consistent. An invisible gap needs rank at least two; 07's third
archimedean layer only keeps `ε = ω^{-1}` above its jet scale `ω^{-ω}`, for
its extra assertion that each polygon is flat-close to a fixed triangle, and
07's own rank-two variant (Corollary 72.4) drops that assertion. 04's
fields all lie in one rank-two field, the real closure of
`R(ω^{-1}, ω^{-ω√q} : q prime)`, whose value group is `Q + ω·span_Q{√q}`
(Remark 70.8). The dossier's form of this sentence ("the union over all
primes of these fields") was corrected in the write: 04 indexes its
monomials by vertex, and the real closure contains every `K_n` but is their
union only when the chosen primes are nested.

Symbols renamed from the sources (no normalization changed; Appendix A.4
and A.8 have the same tables):

| Part | Source | Delivered | Printed | Why |
|---|---|---|---|---|
| I | 02 | `t = ω^{-1}` | `ε` | in 02's material of Part I, where `t` is 05's real polynomial parameter; 02's introduction and Part II keep `t`, the power-series variable evaluated at `t = ε` |
| I | 05 | `ε_1 = ω^{-1}`, `ε_2 = ω^{-ω}` | `ε`, `τ` | report convention (one example) |
| III | 06 | macro `\Span` (plain span) | `\spanplain` | the base's `\Span` is `span_R`; printed output unchanged |
| V | 07 | `ρ = ω^{-ω}` (main construction), `V_ρ` | `τ`, `V_τ` | report convention; the re-chosen scale in Corollary 72.4 and Theorem 74.2 keeps `ρ` |
| V | 07 | auxiliary `τ` in the proof of Theorem 74.2 | `σ` | `τ` reserved |
| V | 04 | flat ideal `𝓘_ε`, valuation `v`, value group `Γ` | `𝔧_ε`, `ν`, `G` | one symbol each in Part V (07's) |
| V | 04 | monomials `ν_i` (proof of Theorem 74.1) | `μ'_i` | clash with the valuation |
| V | 04 | cyclic polygon `P_n`, `p_i`, `P_{n,M}` | `P°_n`, `p°_i`, `P°_{n,M}` | 07's `P_n` is a different polygon |
| V | 04 | tolerance set `𝒯 ∋ τ`, `c_τ`, `b_τ` | `𝒟 ∋ δ`, `c_δ`, `b_δ` | `τ` reserved |
| V | 04 | "algebraic finite-accuracy shadows" | "approximants" | not standard parts |
| VI | 08 | displacement module `𝓛(P)` | `L(P)` | it is Part III's scale lattice |
| VI | 08 | determinant ideal `𝔡` | `𝔇` | Part III's ideal |
| VI | 08 | macro `\val` (= `ν`) | `\nu` | the host's `\val` prints `v`; printed output unchanged |
| VII | 09 | macros `\vol` (= Vol), `\Span`; 10 `\Span` | `\Vol`, `\spanplain` | macro clashes; printed output unchanged |
| VII | 09 | "Research question" with its own counter | question | one theorem counter; its one textual reference redirected |
| VIII | 11 | macros `\br` (two arguments), `\ord` (= `ord_0`), `\Span` | `\brr`, `\ordz`, `\spanplain` | macro clashes with Part I; printed output unchanged |
| IX | 12 | macro `\argmax` (unused in its text) | `\Argmax` | clash with 02's macro |

Letters kept with a Part-local meaning, listed in the article's table: 02's
comparison rank `p` (= 05's `m`; in 02's blocks `m` is a stage index), 02's
space `L_A` (05's `L_h` is a map), `r` (02's history length, 05's `r_0`,
02's residuals `r_i(h)`, 06's affine dimensions), `L` (06's scale lattice
`L(P)`, 03's count `L_P(n)`, 11's Lawrence polytope `L(B)`), `V`, `S`, `T`,
`Z`, `B`, `ρ`, `η`, `q`, `m`, `t`; the general jet scale is `s` in 07's
statements and `ε` in 04's.

## What the report claims

Each Part states its own claims; this is a map with the article's numbers.

- **Part I.** Theorem 6.1 and Corollary 6.3 (05: at most `m ≤ n−d−1`
  monomial scales keep every real dependence leading term modulo affine
  heights; exactly `m` leading exponents occur) and Theorem 7.1 (02: the same
  selection is compatible with every common initial cut, with exactly `p+1`
  profiles); Theorem 8.2 (05: flag classification); Theorems 9.1 and 9.2
  (05: exact germ degrees `m−1` and `m−r_0`) and Proposition 9.4 (05, also
  02: no single real parameter when `m ≥ 2`); Proposition 10.2 (05 and 02:
  slack certificate; 02's form is Remark 11.1), Lemma 10.3 (05: explicit
  threshold), Theorem 10.4 (05: linear realization with the exact shadow),
  Theorem 10.6 (05: arbitrary separation of the degrees); Theorems 11.2,
  11.4, 12.2 and 12.3 (02: comparison rank with cut clauses, stage
  threshold, classification of support-initial histories, sharp parabolic
  family with the hexagon of Table 2); Proposition 13.1 (05 and 02:
  `st conv = conv st`); the polar identity, lost face and optimality band
  (02, Section 14); Theorem 17.2 (05: toric initial ideals); Theorem 18.1
  (05, with 02's covector form and second proof: transfer and shadow arcs);
  Theorem 19.1 (02: finite Puiseux model); Section 20 (05: corrections to
  the private draft, as standalone statements); Propositions 21.1 (05:
  halting-problem obstruction) and 21.2 (02: query-model bound).
- **Part II.** Lemma 26.1, Theorems 26.2, 26.3 and 26.6, Proposition 26.7
  (02: four-point test, rational alternation, universal histories,
  independent transfinite endpoint, finite determinacy for uniform ordinary
  series), the tail-truncation caveat, and the exact recursion (Section 30).
- **Part III.** Theorems 35.1 and 35.3 (normalization, affine residue),
  Theorem 36.3 and Proposition 36.4 (determinant certificates), Theorem 37.2
  and Corollary 37.3 (simultaneous inner segments, valued Grassmannian),
  Theorems 38.1 and 38.4 (clones, exchange-convexity), Theorems 39.1 and
  39.2 and Proposition 39.3 (probes; 39.1 and 39.2 also proved by source 08),
  Corollary 40.1 (full characterization), Theorem 41.2 (finite-support
  specialization).
- **Part IV.** Theorem 49.2 (at most `d+1` lexicographic levels), Theorem
  50.1 (descent), Theorem 51.1 (face implantation), Theorem 52.1 and
  Corollary 52.2 (the natural-boundary quadrilateral), Theorem 53.3 (surface
  coefficient), Theorems 54.1 and 54.3 (attainable interval), Theorem 55.2
  and Corollary 55.5 (rationality criterion, dichotomy).
- **Part V.** Theorem 64.1 (07: the separation for every `n ≥ 4`), Theorems
  67.1 and 67.4 (07: generic linear and semidefinite lower bounds), Theorem
  69.1 (07: identical initial slack matrices), Theorem 70.1 and Proposition
  70.4 (04: the same-circle family and its upper bound), Theorem 71.2 (04:
  failure of lifting finite-order factorizations), Proposition 72.1 (07:
  one field of rank three), Theorem 72.2 (07 and 04: order-unit criterion
  for the jet kernel), Corollary 72.4 (07: rank two is sharp), Theorem 72.7
  and Corollary 72.9 (04: the scale-general criterion, two scales), Theorems
  73.2, 73.4 and 73.5 (07: residue descent; 73.2 also 04), Theorem 74.1 (04:
  rank one), Theorem 74.2 (07 and 04: prescribed precision and tolerances),
  Theorem 74.3 (07, also 04: finite conservativity), Corollary 74.6 (04:
  approximants), Corollary 75.2 (07: every fixed dimension), Theorem 76.1
  (04: rational charts), Proposition 77.1 (04: decision procedure), Table 6
  (07's bounds).
- **Part VI (08).** Theorem 87.2 and Corollary 87.3 (colorful determinant
  formula, module factorization), Theorem 88.4 (classification and
  realization of spectra), Proposition 88.7 (residue flag), Theorem 89.1
  (singular lengths), Theorems 89.2 and 89.3 (stability), Remark 90.3 (08's
  form of the adaptive test, Theorem 39.2), Theorem 91.2 (nonadaptive
  obstruction), Theorem 92.1 (two-body interval), Theorem 93.1
  (complementary minors), Theorem 93.3 (polarity), Remark 94.3 (08's form of
  Theorem 39.1).
- **Part VII (10 and 09).** Corollary 101.3 (witness size `dm`, optimal by
  09), Theorem 103.3 (exact realization criterion), Theorem 104.2 and
  Theorem 104.4 with Proposition 104.5 (initial polynomials; 09's
  canonicity), Theorem 105.4, Theorem 105.7 and Corollary 105.8 (initial
  supports, 09's rank recovery), Proposition 105.9 (affine gauge), Theorem
  106.1 and Corollary 107.2 (matroid profiles), Proposition 108.2 and
  Theorem 108.4 (the Fano cubic), Theorem 109.2 (coefficient obstruction,
  09's form with 10's witness), Lemma 110.1 and Theorem 110.2 (planar
  sufficiency, finite-valued profiles).
- **Part VIII (11).** Theorem 120.3 and Corollary 120.4 (exponential
  rational shadow degree), Theorem 124.3 (Lawrence recovery), Theorem 126.3
  (local bound), Theorems 127.1 and 127.2 (valuations, ramification after
  normalization), Theorem 128.2 (addition chains).
- **Part IX (12).** Theorem 135.1 (main theorem), Theorems 139.4, 140.2 and
  140.3 (augmentation, finite hull, normal fan), Theorem 141.2 and Corollary
  141.4 (candidate formula, any integer part), Theorems 142.1 and 142.4
  (compiler, same-matrix descent), Theorems 143.3 and 143.5 and Proposition
  143.6 (irrational obstruction, dichotomy, omnific right-hand sides),
  Theorems 144.1 and 144.2 (total unimodularity, knapsack).
- **Part X (13).** Theorem 153.2 (saturation), Theorems 155.1 and 155.3
  (separation, exposed faces), Theorem 156.2 (active rows), Theorem 157.2
  and Corollaries 157.3–157.4 (rigidity, definable classes), Theorem 158.1
  (polarity), Theorems 159.2 and 160.2 (degree of non-exposedness, sharp
  family), Theorems 161.1 and 161.2 (moment hull and its polar), Theorem
  163.1 and Proposition 163.2 (saturated fields, cuts).

Statements added in the batch-58 merge, each marked `[write]`: Remark 1.1
and 1.2; the threshold comparison before Theorem 11.4 (both thresholds,
recomputed over all basis slacks and augmented determinants, give
`η = 1/34` for the hexagon and `η₀ = 1/10` for 05's three-scale example);
Remark 50.3 (03's descent lands in a rank-one field, where Part V's jet
kernel vanishes; 03 makes no valuation claim, so no conflict); Remark 68.2
(recomputed from Table 6's formulas: the first strict linear gap is at
`n = 121`, 17 > 16; there is none for `131 ≤ n ≤ 153`, and one for every
`n ≥ 154`; the table's `n = 258` row is a linear but not a semidefinite gap,
as its caption says); Remark 70.7 (07's proof applied to 04's circle gives
`xc(P°_n)(xc(P°_n)−1) ≥ n`, a write-phase observation that neither
manuscript states); Remark 70.8 (one rank-two field); Remark 71.3 (04's
hypothesis `m ≥ 10` in Theorem 71.2 is conservative: the needed
`⌈√n⌉ > 2m` already holds at `m = 9`); Remarks 72.5, 72.8 and 74.5 (rank
three against rank two; 04's criterion and 07's order-unit theorem are one
theorem; residue descent lowers complexity while real-algebraic transfer
keeps it).

Statements added in the batch-59 merge, each marked `[write]`: Remark 1.4
(three degrees); after Theorem 92.1, that the union of the two-body
intervals over spectra with fixed sums `A`, `B` is `{μ ≤ (A+B)/2} ∩ Γ` (the
value group is divisible), which is the two-body case of Theorem 110.2; in
Part VII the dictionary between the two Fano labellings (they differ by
exchanging 3 and 4) and the translation of 09's compression constants to
`2^d ∏ δ^α` and `4^d`.

**Answered or re-scoped questions of Parts I–V** (`[write]` notes at the
questions): Part I's "Moving-base determinant degenerations" is answered
negatively for rational arcs by Part VIII (Puiseux arcs only through the
normalized ramification bound); Part II's "Effective controlled
specialization" and Part IV's "Effective algebraic descent" get a
lower-bound family from Part VIII, no upper bound; Part III's "Intrinsic
full-profile realization", "Leading coefficients above a fixed scale
profile" and "Joint residue data" are partly answered by Part VII (dimension
three with three or four colours, compatibility across weights and the
higher-rank flag part stay open); its "Minimal probe systems" (reference-free
case, the plane), "Dual geometric invariants" (symmetric coarse case) and
the question left open after Theorem 39.1 are answered by Part VI; its
"Beyond finite vertex sets" is partly answered by Part X (the volume half is
untouched); Part IV's "Other integer parts and unbounded geometry" is partly
answered for hulls by Part IX (the counting half stays open).

## What the report does not claim

Every limitation, disclaimer and priority caveat of the twelve manuscripts
is printed in its Part; the non-claim passages the placement dossiers listed
(batch 58: 11 of 05, 8 of 02, 13 of 06, 8 of 03, 8 of 04, 10 of 07; batch
59: 21 of 08, 21 of 09, 19 of 10, 9 of 11, 18 of 12, 19 of 13) were each
located in the merged text, and each source's README status paragraph is
printed in its Part's opening. Three delivered sentences are printed with a
`[write]` correction beside them: 08's "The planar relative-position problem
is completely solved at the valuation level" (true for two bodies with
prescribed individual spectra; the many-body planar profile problem is
Theorem 110.2, for finite-valued profiles); 11's bibliography entry naming
the file `surreal_liftings_article.tex`, which does not exist (the
manuscript is this report's Part I base, delivered as
`surreal_liftings/article.tex`); and 12's "These are proposed mathematical
contracts, not names of declarations asserted to exist in the repository",
an under-claim (see the formal status below). 09's "first degree" statement
is printed with the scope "finite-valued (equivalently full-support)" and
09's caveat that zero coefficients are not covered. In brief:

- **No new finite combinatorics.** A finite surreal polytope has an
  ordinary real (even real algebraic) realization of its labelled face
  lattice; transfer is classical and is not claimed as new (Part IX's
  descent theorem is its integer-hull instance).
- **Classical ingredients.** Conway normal forms, real-closed-field transfer
  and curve selection, lexicographic models of ordered vector spaces,
  secondary polytopes and regular subdivisions, Graver bases, mixed volumes
  and valuated matroids, Ehrhart theory and the Pólya–Carlson/Fatou–Kronecker
  facts (cited, not proved, in Part IV), and the extension-complexity
  toolbox (Yannakakis, Fiorini–Rothvoß–Tiwary, Kaibel–Pashkovich,
  Kwan–Sauermann–Zhao) are attributed in each Part. 05 does not claim the
  first higher-rank secondary theory (Chirivì–Costa Cesari–Fang–Littelmann,
  September 2026, is discussed) or new higher-rank degenerations. In Parts
  VI–X: valuation-ring diagonalization, the singular-value connection
  (Kaveh–Makhnatch) and Alexandrov–Fenchel theory (08); Lorentzian
  polynomials (Brändén–Huh, whose Remark 4.3 already has the Fano support
  and four-variable quadratic obstructions), Menges, Averkov et al. (09,
  10; Huh's Example 3.4 is not answered); von Staudt constructions, Lawrence
  polytopes and intrinsic spread (11); Graver bases, Presburger arithmetic
  and total unimodularity (12); Martínez-Legaz's lexicographic separation
  and degree of non-exposedness (13).
- **Scope.** The lifting results need a fixed real base; polynomial models
  keep dependence signs, not surreal exponents; a single real specialization
  cannot keep every sign when `m ≥ 2`; coefficient support is not assumed
  computably extractable (Propositions 21.1, 21.2); the Puiseux model keeps
  only finitely many observations; universal truncation histories start at
  degree two, with four generators that need not be four vertices. Part III
  treats finite vertex sets in fixed dimension with the natural convex
  valuation and does not solve the full real mixed-volume configuration
  problem. Part IV's counting statements concern integer dilations of
  polytopes bounded by a real box. Part V does not determine the exact
  extension complexity of its hard polygons (07 gives no upper bound beyond
  `n` for its `P_n`), and its finite checks compute no nonnegative or
  semidefinite rank. Part VI's obstruction concerns fixed finite families of
  mixed-area valuations, not all measurements, and the optimality of `d+1`
  is open; its complementary-minor formula is a reduction, not a
  higher-dimensional realization theorem; polarity does not touch Mahler's
  conjecture. Part VII's sufficiency is for finite-valued profiles in the
  plane; dimension three is open. Part VIII's bounds are not sharp (a factor
  `16k+48` apart), use labelled face lattices and shadows, grow in dimension
  with `k`, and cover algebraic arcs only through normalized ramification.
  Part IX's positive theorems need rational normals, and its obstruction
  theorems use the surreal splitting `Oz = Π ⊕ Z`. Part X's "small" is
  set-indexed in a fixed NBG universe; its degree invariant is
  Martínez-Legaz's.
- **Evidence.** The programs test finite exact examples; they are not
  proofs of the universal, transfinite or class-sized statements, not
  implementations of surreal arithmetic, and not formal verification.
- **Priority.** No manuscript establishes literature-wide priority, and none
  claims to solve a named published open problem; the research questions
  are proposed directions. The external versions Huh arXiv:2601.13249v4
  (Example 3.4) and Averkov et al. v3 (Part III cites v2) could not be checked
  offline; no `[write]` text relies on them.

## Formal status and relation to the collection

**Nothing in this report is formalized.** Placement beside the collection's
Lean development confers no formal status. The Lean declarations the
manuscripts name (checked with `rg` at the writes):

- `Surreal.Foundations.SignSequence.omnific_bounded_iff`
  (`Surreal/Foundations/OmnificUnits.lean:65`: a real bound on an omnific
  integer is equivalent to its being an ordinary integer), with
  `omnific_isFinite_iff` (`:55`) and `omnific_eq_intConstant_of_finite`
  (`:42`). Manuscript 03 uses `omnific_bounded_iff` as an input in Part IV;
  it is the only declaration any of Parts I–V relies on. The file's blob,
  `c9ce3771`, is the one 03 inspected.
- Part IX's integer-part interface (the first row of its formalization
  table, and the first sentence of its Lemma "finite", which is Part IV's
  bounded-element property) is already proved in Lean for the actual omnific
  ring: `omnific_bounded_iff` and `omnific_least_positive`
  (`OmnificUnits.lean:65`, `:104`), `omnificFloor_spec` and
  `existsUnique_omnific_integerPart` (`Surreal/Foundations/OmnificFloor.lean:112`,
  `:138`), `existsUnique_omnific_division` (`OmnificDivision.lean:62`) and
  `omnificQuotientZModEquiv` (`OmnificResidues.lean:81`), all in
  `Surreal.Foundations.SignSequence`. 12 stated these as "proposed
  contracts"; a `[write]` note after its table names them. Its Presburger
  bridge and every later row are not formalized.
- Source 10 names, as the repository's versions of its basic objects,
  `valuation` (`Surreal/Foundations/SignSequenceValuation.lean:54`),
  `valuation_mul` (`:84`), `valuation_antitone_nonneg` (`:103`), `tMonomial`
  (`:119`), `valuation_tMonomial` (`:130`), `standardPartHom`
  (`Surreal/Foundations/SignSequenceStandardPart.lean:142`),
  `standardPartHom_surjective` (`:168`), `mem_ker_standardPartHom` (`:173`)
  and `standardPartQuotientEquiv` (`:192`); the blobs `222abd29` and
  `78e7c0a6` it records are those at the pin and now. No Part VII statement
  depends on them formally.
- `Surreal.Complexify.dot`, `cross`, `cross_def`, `cross_swap`,
  `dot_sq_add_cross_sq`, `ptolemy_identity`, `ptolemy`, `triangleArea`,
  `heron_factorization` and `heron` (`Surreal/Algebra/Geometry.lean`; blob
  `450fd4b` at both pins and now). Manuscripts 05 and 02, and source 11,
  inspected this file as background; no result uses it.
- Related, but neither cited nor used: `Surreal.Surcomplex.RegularPolygon`
  (`vertex`, `vertex_radius`, `side_length`, `area_eq` in
  `Surreal/Surcomplex/RegularPolygon.lean`; regular polygons at surreal
  radius, close to 04's regular `R_n`) and
  `critical_point_mem_convexHull_roots`
  (`Surreal/Surcomplex/PolynomialGeometry.lean`, a surcomplex convex hull).

No theorem of this report duplicates a Lean declaration, and none of its
labels has an entry in the collection's formalization ledger. Section 83
collects the Lean roadmaps of 05, 02, 06, 03 and 07 as proposals; 04 has no
roadmap section (its "Formalization milestones" question is merged with
07's last question). The formalization proposals of sources 08–13 stay in
Parts VI–X; none has been carried out.

**Neighbouring reports.** No other report of the collection treats
polytopes, lifting subdivisions, mixed volumes, Ehrhart functions,
extension complexity or integer hulls, so this report continues none and
answers no named question elsewhere. 04's remark that the repository never
mentions "extension complexity" was true at its pin and outside this
directory still is. There are passing contacts:
[surcomplex/trigonometry](../../surcomplex/trigonometry/) (regular polygons
at surreal radius, `trigonometry:cor:polygon`, close to 04's `R_n`),
[surcomplex/polynomial-algebra](../../surcomplex/polynomial-algebra/) (the
surreal convex hull of root sets), and
[set-sized-quotients-of-omnific-integers](../set-sized-quotients-of-omnific-integers/)
(rational polyhedral cones). Part III takes the positive grading it uses
from the transseries report
[Reversion Beyond Archimedean Valuations](../../../../../Analysis/Transseries/docs/series-and-transseries/Reversion_Beyond_Archimedean_Valuations/)
(its `thm:separator`, "Finite supports admit a positive rational
grading"). 04's description of
[computer-algebra](../../foundations-and-computation/computer-algebra/) is
accurate. Part IX is the linear-inequality counterpart of
[omnific-groups-and-lattices](../omnific-groups-and-lattices/), Part III
(closest points, `ogl:lat:thm:closestflag`, `ogl:lat:thm:alltargets`: a
quadratic analogue with a rational-flag criterion), which 12 cites as
related prior work; it answers none of that report's questions. Part IX
also lists the collection's other treatments of irrationality obstructing
omnific extrema:
[hahn-tate-uniformization](../../surcomplex/hahn-tate-uniformization/)
(`tate:theta:thm:flag`, the Pell example `tate:theta:ex:irrational`),
set-sized-quotients-of-omnific-integers (`osq:prop:conservative`),
[exponential-relations-over-omnific-integers](../../foundations-and-computation/exponential-relations-over-omnific-integers/)
(`exr:thm:rational`, the model-theoretic base of 12's localization lemma)
and [omnific-diophantine-geometry](../omnific-diophantine-geometry/)
(`odg:thm:linear`, equations only). Part X's cut criterion cites
[surreal-fields-across-universes](../../foundations-and-computation/surreal-fields-across-universes/)
accurately. None of these shares a theorem with this report.

**The private draft.** Manuscripts 05 (Section 20) and 07 (Section 62)
correct statements of *Finite Convexity and Exact Lexicographic
Optimization over the Surreals* (22 September 2026), a draft that was
supplied privately to their authors. It is not part of ProveIt (no tracked
file contains its title) and could not be checked. The article prints the
note "The draft corrected here … was supplied privately to the authors of
manuscripts 05 and 07; it is not part of ProveIt and could not be checked.
The statements below are printed as standalone results." at both places,
and its bibliography entries `fs:PriorDraft` and `ic:previous` say the same.

## Build

TeX Live or MiKTeX with pdfTeX and the packages in the preamble (newpx,
amsmath/amsthm, mathtools, microtype, bm, booktabs, array, longtable,
tabularx, float, enumitem, xcolor, TikZ, tcolorbox, fancyhdr, needspace,
etoolbox, aliascnt, xurl, hyperref, bookmark, cleveref). `float` is loaded
before `hyperref`; loaded after it, it duplicates PDF destinations. No
external figures, bibliography database or downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX 26.2, pdfTeX, from a clean directory) has 353
pages. It has no errors, undefined references or citations, multiply
defined labels, duplicate destinations, LaTeX or package warnings, or
overfull boxes; it has 20 underfull boxes (10 of them already in the
batch-58 build). A check of every "Theorem~\ref"-style reference against
the label's type found no mismatch. The title page is wrapped in
`\hypersetup{pageanchor=false}` … `pageanchor=true`. Pages were rendered
and inspected, among them the title page, the guide's notation table and
Section 1.6, the Part openings, the hexagon table and fan figure, 02's
four-point figure, 06's thin-triangle figure, 07's bounds table, the Fano
dictionary and table (Part VII), 12's knapsack table and figure, 13's two
figures, and the provenance tables.

## Rerunning the verification programs

Every delivered program writes its outputs under its **delivery names**,
into its own directory, into `data/` beside its parent, or into the working
directory, so a run in place would add unprefixed files to this report: 02
and 04 would both write `data/verification.json`, 03 and 06 would both
write `code/verification.json` (03 also `code/counts.csv`), 05 would write
`data/certificates.json` and `data/verification_report.txt`, 02 also
`data/hexagon_example.json` and `data/universal_history_example.json`, 07
`code/results.json`, 08 `data/verification.json`, 10 `code/fano_coefficients.csv`,
`code/rank_two_example.txt` and `code/verification.json`; 09, 11 and 12
write `verification_results.json` or `verification.json` in the working
directory unless `--output` is given, and 13 writes only with `--output`.
Run them only on copies laid out as delivered, or with an explicit output
path outside this directory, from this directory:

```sh
W=/path/to/scratch
# 05 and 02 write <parent>/data/<delivery name>; standard library only
for s in 05-finite-scale-liftings 02-transfinite-scales; do
  mkdir -p "$W/$s/code" "$W/$s/data"
  cp "code/$s-verify.py" "$W/$s/code/verify.py"
  (cd "$W/$s" && python3 code/verify.py)
done
# 03 writes next to itself unless --out-dir is given; standard library only
python3 code/03-boundary-geometry-verify.py --out-dir "$W/03"
# 04 writes <parent>/data/verification.json; SymPy
mkdir -p "$W/04/code" "$W/04/data"
cp code/04-beyond-all-orders-verify.py "$W/04/code/verify.py"
(cd "$W/04" && uv run --no-project --with sympy==1.14.0 python code/verify.py)
# 06 writes next to itself unless --output is given; standard library only
python3 code/06-affine-residues-verify.py --output "$W/06-verification.json"
# 07 writes results.json next to itself; SymPy
mkdir -p "$W/07"
cp code/07-invisible-complexity-verify.py "$W/07/verify.py"
uv run --no-project --with sympy==1.14.0 python "$W/07/verify.py"
# 08 writes <parent>/data/verification.json; SymPy
mkdir -p "$W/08/code" "$W/08/data"
cp code/08-mixed-volume-tomography-verify.py "$W/08/code/verify.py"
(cd "$W/08" && uv run --no-project --with sympy==1.14.0 python code/verify.py)
# 09: explicit output; SymPy
uv run --no-project --with sympy==1.14.0 python code/09-finite-mixed-volume-models-verify.py --output "$W/09-verification_results.json"
# 10 writes three files next to itself; SymPy; never with -O (bare asserts)
mkdir -p "$W/10"
cp code/10-tropical-mixed-volumes-verify.py "$W/10/verify.py"
uv run --no-project --with sympy==1.14.0 python "$W/10/verify.py" > "$W/10/verification.txt"
# 11: explicit output; SymPy only for the reconstruction test
uv run --no-project --with sympy==1.14.0 python code/11-contact-depth-verify.py --max-k 6 --output "$W/11-verification.json"
# 12 and 13: explicit output; standard library only
python3 code/12-omnific-hulls-verify.py --output "$W/12-verification_results.json" > "$W/12-verification_output.txt"
python3 code/13-beyond-finite-verify.py --output "$W/13-verification_results.json" > "$W/13-verification_stdout.txt"
```

(On Windows use `py` for `python3`.) Runs on copies at the batch-58
placement, 30 September 2026: 05 passed its 53 cases (7 named, 6 sharpness,
40 random with seed 20260930; 60 extra dependence vectors each) in about
10 s; 02 passed 163,914 exact assertions in about 32 s; 03 passed in about
24 s and regenerated `counts.csv` byte for byte; 04 passed 114 of 114
checks in about 4 s; 06 passed in about 26 s; 07 passed in about 6 s. Runs
of the batch-59 commands above, on copies, at the batch-59 write (30
September 2026): 08 PASS with 3,196 assertions (68 s in the placement audit); 09, 10, 11
(12,180 minors), 12 and 13 (PASS, 28,890 checks) exited 0 in a few seconds
each, and 10 regenerated `fano_coefficients.csv` byte for byte. Every
regenerated JSON or text file equals the shipped one apart from line
endings (Python's `write_text` and redirected output write CRLF on Windows)
and, for 04 and 07, the recorded Python and SymPy versions (the shipped
runs record Python 3.13.5 and SymPy 1.14.0). Compare modulo CR. Do not use
Python's `-O` switch: the programs check by assertions (11 refuses to run
without them; 10's bare asserts would pass vacuously).

Hazards:

- **Two CSV files have CRLF line endings**, as delivered, because
  `csv.writer` writes CRLF on every platform:
  `data/03-boundary-geometry-counts.csv` (102 lines) and
  `data/10-tropical-mixed-volumes-fano_coefficients.csv` (85 lines). `-text`
  lines in `Algebra/SurrealNumbers/.gitattributes` keep the bytes. Never
  re-save them.
- **The build files name delivery paths** and must not be run in this
  directory. `code/02-transfinite-scales-Makefile` runs
  `python3 code/verify.py` and `pdflatex` three times on `article.tex` in the
  working directory, and its `clean` target removes `article.aux`,
  `article.log` and the like there: run from this directory it would rebuild
  or clean *this* report. The same holds for `code/09-finite-mixed-volume-models-Makefile`
  (`latexmk` on `article.tex`, `latexmk -c`, `python verify.py`),
  `code/12-omnific-hulls-Makefile` (`pdflatex` three times on `article.tex`,
  `rm -f article.aux article.log article.out article.toc`, `python3 verify.py`)
  and `code/13-beyond-finite-Makefile` (`latexmk` on `article.tex`,
  `latexmk -c`, `python3 code/verify.py --output data/verification_results.json`).
  `code/06-affine-residues-Makefile` runs `latexmk` on `article.tex` and
  `python3 verify.py` in the working directory.
  `code/04-beyond-all-orders-build.sh` changes into `code/`, creates
  `code/build/` and fails on the missing `article.tex`.
  `code/07-invisible-complexity-build.sh` changes into `code/` and runs
  `python verification/verify.py` and `latexmk` on the missing
  `surreal_polytopes.tex`. `code/08-mixed-volume-tomography-build.sh` and
  `.ps1` change into `code/`, create `code/build/` and fail on the missing
  `article.tex`; `code/10-tropical-mixed-volumes-build.sh` changes into
  `code/`, runs `latexmk` on the missing `article.tex` and would then run
  `python verify.py | tee verification.txt` there;
  `code/11-contact-depth-build.sh` changes into `code/` and fails on the
  missing `surreal_polytopes_contact_depth.tex`.

## Delivery names in shipped files

The delivered code, data, audit and provenance files are byte-identical to
the delivery, so their text still uses delivery names:

- `02-transfinite-scales-sources.md` and `02-transfinite-scales-proof_audit.md`
  (delivered as `notes/sources.md` and `notes/proof_audit.md`): "the article"
  is manuscript 02, printed here as Part II and part of Part I.
- `05-finite-scale-liftings-PROOF_REVIEW.md` says `python3 code/verify.py`
  (shipped as `code/05-finite-scale-liftings-verify.py`).
  `05-finite-scale-liftings-SOURCES.md` (lines 32–43) describes the private
  draft and names its research-library file `article(20260923-000126).pdf`,
  which ProveIt does not contain.
- `06-affine-residues-PROVENANCE.md` names `verification.json` (shipped as
  `data/06-affine-residues-verification.json`) and its PDF build and page
  images, which are not shipped. 06's program and its recorded run call
  `ω^{-ω}` `eta`, as Part III does.
- `07-invisible-complexity-SOURCE_AUDIT.md` (lines 24–35) describes the same
  private draft and file name; the `README.md` in its source list (line 15)
  is the repository's root README, not a delivered file.
- `07-invisible-complexity-verification-README.md` (delivered as
  `verification/README.md`) says "Run `python verification/verify.py` from
  the package root" and that the program "writes `results.json` next to
  itself" (shipped as `code/07-invisible-complexity-verify.py` and
  `data/07-invisible-complexity-results.json`; run it only on a copy, as
  above).
- The `README.md` files named in `08-mixed-volume-tomography-SOURCE_AUDIT.md`
  and in 12's and 13's source notes are the repository's READMEs, which
  exist. `09-finite-mixed-volume-models-SOURCE_AUDIT.md` names `article.tex`,
  `README.md` and `verify.py` (not shipped, not shipped, and
  `code/09-finite-mixed-volume-models-verify.py`).
  `10-tropical-mixed-volumes-source_audit.md` names `verify.py`,
  `verification.json` and `verification.txt` (shipped under the `10-`
  prefix in `code/` and `data/`). `12-omnific-hulls-PROOF_AUDIT.md` and
  `12-omnific-hulls-SOURCES_AND_SCOPE.md` name `verify.py` and
  `verification_results.json` (shipped as `code/12-omnific-hulls-verify.py`
  and `data/12-omnific-hulls-verification_results.json`).
- `13-beyond-finite-BUILD_REPORT.md` (delivered as `notes/BUILD_REPORT.md`)
  names `code/verify.py`, `data/verification_results.json` and
  `SHA256SUMS.txt`, and its SHA-256 lines (44–46) describe the delivered
  `article.tex` and `article.pdf`, which are not shipped (this report's
  `article.tex` and `article.pdf` are different files).
  `13-beyond-finite-PROOF_AUDIT.md` names `article.tex`; 13's notes also
  refer to `notes/`, `code/` and `data/` of its package.
- `data/08-mixed-volume-tomography-build_report.json` and
  `data/12-omnific-hulls-build_report.json` describe the delivered 24- and
  28-page PDFs, which are not shipped; 12's names `article.pdf`, `verify.py`
  and `verification_results.json`.
- `data/10-tropical-mixed-volumes-verification.txt` is the capture made by
  10's `build.sh` (`python verify.py | tee verification.txt`), not written
  by the program; it equals the JSON.
- The eleven build files name `article.tex`, `surreal_polytopes.tex`,
  `surreal_polytopes_contact_depth.tex`, `code/verify.py`, `verify.py`,
  `verification/verify.py`, `verification_results.json`,
  `verification_output.txt`, `data/verification_results.json` and `build/`;
  see the hazards above.
- `data/02-transfinite-scales-validation.json` (delivered as
  `notes/validation.json`) records 02's 28-page PDF and SHA-256 values of the
  delivered `article.tex`, `article.pdf` and `code/verify.py`; only the
  program is shipped (as `code/02-transfinite-scales-verify.py`).
  `data/02-transfinite-scales-verification_run.txt` is a captured log, not a
  program output, and names the packager's directory
  `/mnt/data/surreal_polytopes_package/data`.

In the article, every file that a manuscript's text names is given its
shipped path; where a manuscript names a file that is not shipped (its PDF,
README, checksum list or a research-library copy), a `[write]` note says so.
Verbatim command blocks of the sources keep their delivery names, followed
by a `[write]` note with the shipped names.

## Provenance

- **Pins and placement.** Manuscript 05 of batch 58 compared itself with
  ProveIt at `5e0f4e050`, source 09 at `b2b626d85`, all others at
  `6996fee43` (whose commit time 16:07:39 UTC 02 and 07 print correctly).
  The six batch-58 manuscripts were placed together in `b30441a8c` as one
  new report, because no surreal report, README question or Lean file
  treats polytopes; they are one merged report with three spines rather
  than three reports because they answer one prompt, share one setting and
  triplicate its basic lemmas. The six batch-59 manuscripts were placed in
  `f2cb2034e` as additions to it, because each continues a theorem or
  question of Parts I–IV and none continues anything else (12's quadratic
  analogue, `omnific-groups-and-lattices` Part III, is cited by 12 only as a
  close prior theme); their files continue the report's local prefix
  sequence `08-`–`13-` in manuscript order.
- **Bases.** 05 is the base of Part I and of the report (weaker hypotheses:
  an ordered subfield, against 02's real closed field; stronger conclusions:
  exact leading terms, the flag classification, exact degrees). 07 is the
  base of Part V (every `n ≥ 4`, linear and semidefinite lifts, descent for
  every convex valuation ring, every fixed dimension, the sharper parameter
  count `dN ≤ r(r−1)` against 04's `s ≤ r²`). Source 10 is the base of Part
  VII (same hypotheses as 09, sharper compression constants, the general
  matroid criterion).
- **Where the merges chose.** Duplicated results are printed once with both
  sources and both labels (listed above), with a genuinely different proof
  kept as a "Second proof (source 02/04/09/10)" or a third route. Statements
  that overlap but add something were printed beside each other with a
  `[write]` note: 02's cut-compatible compression and comparison-rank
  theorems beside 05's pivot theorem and corollary, 02's stage threshold
  beside 05's lemma, 02's Puiseux model beside 05's arc theorem, 02's query
  bound beside 05's halting-problem obstruction, 04's transcendence-degree
  proposition beside 07's generic bound (07's statement does not cover the
  circle), 04's Yannakakis proposition beside 07's factorization; 08's
  colorful determinant formula beside Part III's determinant theorem
  (generator-count against dimension-only constants), 10's realization
  criterion beside Part III's full characterization, 09's initial-polynomial
  theorem beside 10's, and 09's symmetric compression, colored-minimum
  criterion and integer-mixing bound as marked remarks. Results of sources
  08–10 identical to Part III results (08's adaptive test and all-probes
  classification; 10's and 09's positive sums, parallelotope compression,
  standard part of volume, Rado lemma and exchange-convexity) are printed
  once in Part III, with `[write]` pointers in Parts VI and VII carrying the
  sources' labels and their different proofs. 09's coefficient obstruction
  is printed in its stronger form ("even up to a positive scalar"), with
  10's proofs and witness as second routes; the two Fano cubics are one
  polynomial, printed once with the dictionary between the labellings.
  02's Section 6, its tests, audit, directions, conclusion and appendices
  form Part II. The Lean roadmaps of Parts I–V are in Section 83; those of
  Parts VI–X stay in their Parts. In Part V the appendix-derived sections
  precede the merged questions, so that the questions end the Part; in the
  other Parts the source order (questions, conclusion, appendices) is kept.
  Questions stay with their Parts; where two manuscripts ask the same thing
  they are merged (three pairs in Part V, seven in Part VII, where twenty
  questions became thirteen) or cross-referenced (05's questions 1, 2, 4, 5
  with four of 02's directions; 02's residue direction 28.5 with Part III's
  questions 43.3 and 43.6; 08's questions with Part III's), and a question
  that another manuscript answers in part is re-scoped by a note (see
  "Answered or re-scoped questions" above; also Part III's
  face-specialization question by 02's optimality band and Part V's
  factorization question by 04's Theorem 71.2).
- **Checks during the writes.** The repository statements of all twelve
  were re-checked at the current head: `Geometry.lean`, `OmnificUnits.lean`,
  `OmnificFloor.lean`, `OmnificDivision.lean`, `OmnificResidues.lean`,
  `SignSequenceValuation.lean` and `SignSequenceStandardPart.lean` (the
  cited blobs are unchanged), the collection and report READMEs 08, 09, 12
  and 13 describe (unchanged blobs, accurate), the Presburger project's
  README, the transseries report's title, subtitle and positive-grading
  theorem, the computer-algebra report, the labels of other reports that
  Part IX names, and the absence of "extension complexity" everywhere
  outside this directory and of mixed volumes, Ehrhart theory and curve
  selection in the Lean files; all are accurate, so nothing is stale or
  retracted. The explicit thresholds (`1/34`, `1/10`), 07's bounds table (all
  five rows reproduced) and the value group of the rank-two field were
  recomputed in the batch-58 write; in batch 59 the placement audit
  recomputed 11's bound table, the Fano relabelling, the two-body interval
  and 12's knapsack Graver set, and the write re-ran all six programs.
- **Author lines.** 05: research manuscript prepared for Vladimir
  Reshetnikov, an AI-assisted contribution to the ProveIt research program.
  02: research article prepared for Vladimir Reshetnikov. 06: research
  article prepared for Vladimir Reshetnikov. 03: research manuscript
  prepared for Vladimir Reshetnikov. 07: research manuscript prepared for
  Vladimir Reshetnikov. 04: research manuscript prepared for Vladimir
  Reshetnikov; developed with ChatGPT; independent review and formalization
  pending. 08: research manuscript prepared for Vladimir Reshetnikov. 09:
  research manuscript, prepared for Vladimir Reshetnikov. 10: research
  manuscript prepared for the ProveIt research program. 11: research
  manuscript prepared for Vladimir Reshetnikov, an AI-assisted contribution
  to the ProveIt research program. 12: research draft prepared for Vladimir
  Reshetnikov (its PDF metadata reads "ChatGPT"). 13: prepared for Vladimir
  Reshetnikov with ChatGPT.
