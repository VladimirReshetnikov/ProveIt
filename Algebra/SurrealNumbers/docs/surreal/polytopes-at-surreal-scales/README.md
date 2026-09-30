# Polytopes at Surreal Scales

**Lifting compression, truncation histories, affine residues, lattice counts and invisible extension complexity**

This is a research report dated 30 September 2026, built in the batch-58
write phase from six manuscripts. All six were written independently on
that day, in answer to one question about finite polytopes over the surreal
numbers. Each author line reads "research manuscript" or "research article
prepared for Vladimir Reshetnikov"; manuscript 04's adds "Developed with
ChatGPT; independent review and formalization pending".

| Source | Batch 58 | Archive (inner directory, main file; delivered PDF): title | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 05 | manuscript 05, base | `surreal_liftings_research` (`surreal_liftings/article.tex`; 25 pp. A4): *Finite-Scale Geometry of Surreal Liftings* | `5e0f4e050` | `b30441a8c` | Part I, whole: Sections 2, 4, 6, 8–10, 13, 15–18, 20–25 |
| 02 | manuscript 02 | `surreal_polytopes_research` (`surreal_polytopes/article.tex`; 28 pp. Letter): *Surreal Polytopes at Finite and Transfinite Scales* | `6996fee43` | `b30441a8c` | merged into Part I (Sections 3, 5, 7, 11, 12, 14, 19, parts of 13, 18, 21); Part II (Sections 26–31) |
| 06 | manuscript 06 | `Surreal_Polytopes_Research_Package` (`Surreal_Polytopes/article.tex`; 27 pp. A4): *Surreal Polytopes: Affine Residues, Mixed-Volume Scales, and Simultaneous Segment Models* | `6996fee43` | `b30441a8c` | Part III, whole: Sections 32–45 |
| 03 | manuscript 03 | `surreal_polytope_research` (`surreal_polytopes/surreal_polytopes.tex`; 28 pp. Letter): *Infinitesimal Boundary Geometry of Surreal Polytopes* | `6996fee43` | `b30441a8c` | Part IV, whole: Sections 46–61 |
| 07 | manuscript 07, base of Part V | `surreal_polytopes` (`surreal_polytopes/surreal_polytopes.tex`; 26 pp. A4): *Invisible Complexity in Surreal Polytopes* | `6996fee43` | `b30441a8c` | Part V, whole (Sections 62–82) |
| 04 | manuscript 04 | `surreal_polytopes_beyond_all_orders` (same name, `article.tex`; 26 pp. A4): *Beyond-All-Orders Extension Complexity in Surreal Polygon Geometry* | `6996fee43` | `b30441a8c` | merged into Part V (its own Sections 70, 71, 76, 77, 80, 81, the rest distributed) |

The archives arrived in `b2b626d85`. `6996fee43` is the commit of
30 September 2026, 16:07:39 UTC, and `5e0f4e050` is its second parent.
Archives 02, 03 and 07 wrap inner directories of the same name,
`surreal_polytopes/`, but are different packages. Manuscript 01 of batch 58
(on a Keller map) went to another report. The formalization roadmaps of
05, 02, 06, 03 and 07 are printed together in Section 83.

**Status.** Six AI-assisted, unrefereed research manuscripts. Every theorem
has a written conventional proof in its source, and the programs check
finite examples only. **Nothing in this report is formalized**; no
independent proof review has been done; no manuscript claims literature-wide
priority or the solution of a named published problem.

```
README.md                                                     this guide
article.tex                                                   the report: standalone LaTeX, internal bibliography
article.pdf                                                   the compiled report, 182 pages (unnumbered title page,
                                                              contents pages 1-4, then pages 5-181)
02-transfinite-scales-proof_audit.md                          02's proof audit (delivered as notes/proof_audit.md)
02-transfinite-scales-sources.md                              02's source notes (delivered as notes/sources.md)
05-finite-scale-liftings-PROOF_REVIEW.md                      05's proof review
05-finite-scale-liftings-SOURCES.md                           05's source provenance
06-affine-residues-PROVENANCE.md                              06's provenance note
07-invisible-complexity-SOURCE_AUDIT.md                       07's source audit
07-invisible-complexity-verification-README.md                07's notes on its checks (delivered as verification/README.md)
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
```

The directory also holds 39 files of batch 59, placed in `f2cb2034e`
(after this report's batch-58 placement) for five further Parts VI–X that
are **not yet written** into `article.tex`; this README does not describe
them yet:

```
08-mixed-volume-tomography-PROOF_AUDIT.md          code/12-omnific-hulls-Makefile
08-mixed-volume-tomography-SOURCE_AUDIT.md         code/12-omnific-hulls-verify.py
09-finite-mixed-volume-models-SOURCE_AUDIT.md      code/13-beyond-finite-Makefile
10-tropical-mixed-volumes-source_audit.md          code/13-beyond-finite-verify.py
12-omnific-hulls-PROOF_AUDIT.md                    data/08-mixed-volume-tomography-build_report.json
12-omnific-hulls-SOURCES_AND_SCOPE.md              data/08-mixed-volume-tomography-requirements.txt
13-beyond-finite-BUILD_REPORT.md                   data/08-mixed-volume-tomography-verification.json
13-beyond-finite-PROOF_AUDIT.md                    data/09-finite-mixed-volume-models-requirements.txt
13-beyond-finite-SOURCES_AND_SCOPE.md              data/09-finite-mixed-volume-models-verification_results.json
code/08-mixed-volume-tomography-build.ps1          data/10-tropical-mixed-volumes-fano_coefficients.csv
code/08-mixed-volume-tomography-build.sh           data/10-tropical-mixed-volumes-rank_two_example.txt
code/08-mixed-volume-tomography-verify.py          data/10-tropical-mixed-volumes-requirements.txt
code/09-finite-mixed-volume-models-Makefile        data/10-tropical-mixed-volumes-verification.json
code/09-finite-mixed-volume-models-verify.py       data/10-tropical-mixed-volumes-verification.txt
code/10-tropical-mixed-volumes-build.sh            data/11-contact-depth-requirements.txt
code/10-tropical-mixed-volumes-verify.py           data/11-contact-depth-verification.json
code/11-contact-depth-build.sh                     data/12-omnific-hulls-build_report.json
code/11-contact-depth-verify.py                    data/12-omnific-hulls-verification_output.txt
                                                   data/12-omnific-hulls-verification_results.json
                                                   data/13-beyond-finite-verification_results.json
                                                   data/13-beyond-finite-verification_stdout.txt
```

The manuscripts' own READMEs and PDFs, the five member manuscripts
(02, 03, 04, 06, 07) and three checksum files (05 `SHA256SUMS.txt`, 06
`SHA256SUMS`, 07 `MANIFEST.sha256`) are not shipped; they survive in the
arrival commit `b2b626d85`. Manuscript 05's `article.tex` and `README.md`
were staged as delivered in `b30441a8c`; the merged `article.tex` and this
README replace them, and `article.pdf` is a build of `article.tex`.
Delivery paths were flattened at placement: 02's `notes/proof_audit.md`,
`notes/sources.md` and `notes/validation.json`; 07's
`verification/README.md`, `verification/verify.py` and
`verification/results.json`; the top-level `verify.py` and
`verification.json` of 03 and 06; every other file received its
manuscript's prefix.

## The report in brief

Three spines and five Parts; Section 1 of the article is a guide.

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
  `d^d` determinants; probe classification and a `d+1`-measurement test.
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

## Labels and numbering

Every label in `article.tex` carries the prefix `poly:`. Manuscript 05's 52
labels are `poly:` followed by the delivered name; the others carry a
sub-prefix before the delivered name: 02 `poly:ts:` (69 labels), 03
`poly:ehr:` (62), 04 `poly:bao:` (57), 06 `poly:mv:` (70), 07 `poly:ic:`
(75). All 385 delivered labels are present and none was dropped. The merge
added 46 labels, for 431 in all, with no duplicate:

- report and Parts: `poly:sec:guide`, `poly:sec:notation`,
  `poly:rem:threedegrees`, `poly:rem:rankthree`, `poly:sec:formalization`,
  `poly:app:provenance`, `poly:part:lift`, `poly:part:ts`, `poly:part:mv`,
  `poly:part:ehr`, `poly:part:ic`;
- Parts I–II: `poly:def:signtype`, `poly:cor:uniform`, `poly:sec:truncation`,
  `poly:sec:oneparam`, `poly:sec:leanplan`, `poly:ts:rem:slack02`,
  `poly:ts:sec:workflow`, `poly:ts:q:residue`, `poly:ts:sec:leanplan`;
- Part III: `poly:mv:def:affine-residue`, `poly:mv:def:exchange-convex`,
  `poly:mv:q:face-specialization`, `poly:mv:q:joint-residue`,
  `poly:mv:sec:lean-pointer`, `poly:mv:sec:formalization`;
- Part IV: `poly:ehr:def:rational-flags`, `poly:ehr:app:scope`,
  `poly:ehr:app:ledger`, `poly:ehr:rem:descent-rank-one`,
  `poly:ehr:sec:lean-pointer`, `poly:ehr:sec:formalization`;
- Part V: `poly:ic:q:lifting`, `poly:ic:rem:firstgap`, `poly:ic:rem:rankthree`,
  `poly:ic:rem:directions`, `poly:bao:cor:information` (04's unlabelled
  corollary), `poly:bao:rem:circlecount` (04's unlabelled remark),
  `poly:bao:sec:proofmain`, `poly:bao:rem:onefield`, `poly:bao:rem:sharpcount`,
  `poly:bao:rem:mten`, `poly:bao:rem:sametheorem`, `poly:bao:rem:normalization`,
  `poly:bao:rem:pointcase`, `poly:bao:rem:scalar`.

A result printed once for two manuscripts carries both labels: in Part I
`poly:prop:stconv`/`poly:ts:prop:stconv` (with `poly:ts:eq:stconv`),
`poly:prop:slack`/`poly:ts:lem:slack`, `poly:thm:general`/`poly:ts:thm:transfer`
(and `poly:sec:general`/`poly:ts:sec:transfer`); in Part V
`poly:ic:lem:flat`/`poly:bao:lem:flat`, `poly:ic:thm:orderunit`/`poly:bao:prop:orderunit`,
`poly:ic:thm:residuenonnegative`/`poly:bao:prop:normalization`,
`poly:ic:thm:precision`/`poly:bao:thm:tolerances`,
`poly:ic:thm:conservativity`/`poly:bao:thm:algebraicrealization`,
`poly:ic:cor:scalar`/`poly:bao:prop:scalar` and
`poly:ic:sec:questions`/`poly:bao:sec:questions`. 04's section labels whose
sections were distributed into 07's order sit on subsections. Citation keys
carry the prefixes `fs:` (05), `ts:` (02), `ehr:` (03), `bao:` (04), `mv:`
(06) and `ic:` (07); 02's Gonshor and Basu–Roy entries are printed under
05's keys, and 04's Yannakakis, Fiorini–Rothvoß–Tiwary and Kaibel–Pashkovich
entries under 07's (56 entries in four lists, numbered consecutively).

Sections are numbered consecutively through the report: Section 1 is the
guide, Parts I–V are Sections 2–82, Section 83 collects the formalization
roadmaps, and Appendix A is the provenance. There is one theorem counter,
numbered within sections (cleveref types through `aliascnt`, as in 04), and
equations are numbered within sections, so no source number survives.
Source appendices are ordinary sections at the end of their Parts. Text
added in the merge is marked `[write]`.

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
has the same table):

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

Letters kept with a Part-local meaning, listed in the article's table: 02's
comparison rank `p` (= 05's `m`; in 02's blocks `m` is a stage index), 02's
space `L_A` (05's `L_h` is a map), `r` (02's history length, 05's `r_0`,
02's residuals `r_i(h)`, 06's affine dimensions), `L` (06's scale lattice
`L(P)`, 03's count `L_P(n)`), `V`, `S`, `T`, `ρ`, `η`, `q`, `m`; the general
jet scale is `s` in 07's statements and `ε` in 04's.

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
  39.2 and Proposition 39.3 (probes), Corollary 40.1 (full characterization),
  Theorem 41.2 (finite-support specialization).
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

Statements added in the merge, each marked `[write]`: Remark 1.1 and 1.2;
the threshold comparison before Theorem 11.4 (both thresholds, recomputed
over all basis slacks and augmented determinants, give `η = 1/34` for the
hexagon and `η₀ = 1/10` for 05's three-scale example); Remark 50.3 (03's
descent lands in a rank-one field, where Part V's jet kernel vanishes; 03
makes no valuation claim, so no conflict); Remark 68.2 (recomputed from
Table 6's formulas: the first strict linear gap is at `n = 121`, 17 > 16;
there is none for `131 ≤ n ≤ 153`, and one for every `n ≥ 154`; the table's
`n = 258` row is a linear but not a semidefinite gap, as its caption says);
Remark 70.7 (07's proof applied to 04's circle gives
`xc(P°_n)(xc(P°_n)−1) ≥ n`, a write-phase observation that neither
manuscript states); Remark 70.8 (one rank-two field); Remark 71.3 (04's
hypothesis `m ≥ 10` in Theorem 71.2 is conservative: the needed
`⌈√n⌉ > 2m` already holds at `m = 9`); Remarks 72.5, 72.8 and 74.5 (rank
three against rank two; 04's criterion and 07's order-unit theorem are one
theorem; residue descent lowers complexity while real-algebraic transfer
keeps it).

## What the report does not claim

Every limitation, disclaimer and priority caveat of the six manuscripts is
printed in its Part; the non-claim passages the placement dossier listed
(11 of 05, 8 of 02, 13 of 06, 8 of 03, 8 of 04, 10 of 07) were each located
in the merged text. In brief:

- **No new finite combinatorics.** A finite surreal polytope has an
  ordinary real (even real algebraic) realization of its labelled face
  lattice; transfer is classical and is not claimed as new.
- **Classical ingredients.** Conway normal forms, real-closed-field transfer
  and curve selection, lexicographic models of ordered vector spaces,
  secondary polytopes and regular subdivisions, Graver bases, mixed volumes
  and valuated matroids, Ehrhart theory and the Pólya–Carlson/Fatou–Kronecker
  facts (cited, not proved, in Part IV), and the extension-complexity
  toolbox (Yannakakis, Fiorini–Rothvoß–Tiwary, Kaibel–Pashkovich,
  Kwan–Sauermann–Zhao) are attributed in each Part. 05 does not claim the
  first higher-rank secondary theory (Chirivì–Costa Cesari–Fang–Littelmann,
  September 2026, is discussed) or new higher-rank degenerations.
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
  semidefinite rank.
- **Evidence.** The programs test finite exact examples; they are not
  proofs of the universal, transfinite or class-sized statements, not
  implementations of surreal arithmetic, and not formal verification.
- **Priority.** No manuscript establishes literature-wide priority, and none
  claims to solve a named published open problem; the research questions
  are proposed directions.

## Formal status and relation to the collection

**Nothing in this report is formalized.** Placement beside the collection's
Lean development confers no formal status. The Lean declarations the
manuscripts name (checked with `rg` at the write):

- `Surreal.Foundations.SignSequence.omnific_bounded_iff`
  (`Surreal/Foundations/OmnificUnits.lean:65`: a real bound on an omnific
  integer is equivalent to its being an ordinary integer), with
  `omnific_isFinite_iff` (`:55`) and `omnific_eq_intConstant_of_finite`
  (`:42`). Manuscript 03 uses `omnific_bounded_iff` as an input in Part IV;
  it is the only declaration any Part relies on. The file's blob,
  `c9ce3771`, is the one 03 inspected.
- `Surreal.Complexify.dot`, `cross`, `cross_def`, `cross_swap`,
  `dot_sq_add_cross_sq`, `ptolemy_identity`, `ptolemy`, `triangleArea`,
  `heron_factorization` and `heron` (`Surreal/Algebra/Geometry.lean`; blob
  `450fd4b` at both pins and now). Manuscripts 05 and 02 inspected this file
  as background; no result uses it.
- Related, but neither cited nor used: `Surreal.Surcomplex.RegularPolygon`
  (`vertex`, `vertex_radius`, `side_length`, `area_eq` in
  `Surreal/Surcomplex/RegularPolygon.lean`; regular polygons at surreal
  radius, close to 04's regular `R_n`) and
  `critical_point_mem_convexHull_roots`
  (`Surreal/Surcomplex/PolynomialGeometry.lean`, a surcomplex convex hull).

No statement of this report duplicates a Lean declaration, and none of its
labels has an entry in the collection's formalization ledger. Section 83
collects the Lean roadmaps of 05, 02, 06, 03 and 07 as proposals; 04 has no
roadmap section (its "Formalization milestones" question is merged with
07's last question).

**Neighbouring reports.** No report of the collection treats polytopes,
lifting subdivisions, mixed volumes, Ehrhart functions or extension
complexity, so this report continues none and answers no named question.
04's remark that the repository never mentions "extension complexity" was
true at its pin and outside this directory still is; this report is now the
repository's treatment. There are passing contacts:
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
accurate. None of these shares a theorem with this report.

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
enumitem, xcolor, TikZ, tcolorbox, fancyhdr, needspace, etoolbox, aliascnt,
xurl, hyperref, bookmark, cleveref). No external figures, bibliography
database or downloads are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build (MiKTeX 26.2, pdfTeX 1.40.29, from a clean directory)
has 182 pages. It has no errors, undefined references or citations,
multiply defined labels, duplicate destinations, LaTeX or package warnings,
or overfull boxes; it has 10 underfull boxes. The title page is wrapped in
`\hypersetup{pageanchor=false}` … `pageanchor=true`. Pages were rendered
and inspected, among them the title page, the guide's remarks and notation
table, the Part openings, the hexagon table and fan figure, 02's four-point
figure, 06's thin-triangle figure, 07's bounds table and the provenance
tables.

## Rerunning the verification programs

Every delivered program writes its outputs under its **delivery names**,
into its own directory or into `data/` beside its parent, so a run in place
would add unprefixed files to this report: 02 and 04 would both write
`data/verification.json`, 03 and 06 would both write `code/verification.json`
(03 also `code/counts.csv`), 05 would write `data/certificates.json` and
`data/verification_report.txt`, 02 also `data/hexagon_example.json` and
`data/universal_history_example.json`, and 07 `code/results.json`. Run them
only on copies laid out as delivered, or with an explicit output path, from
this directory:

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
```

(On Windows use `py` for `python3`.) Runs on copies at placement, 30
September 2026: 05 passed its 53 cases (7 named, 6 sharpness, 40 random with
seed 20260930; 60 extra dependence vectors each) in about 10 s; 02 passed
163,914 exact assertions in about 32 s; 03 passed in about 24 s and
regenerated `counts.csv` byte for byte; 04 passed 114 of 114 checks in about
4 s; 06 passed in about 26 s; 07 passed in about 6 s. Every regenerated JSON
or text file equals the shipped one apart from line endings (Python's
`write_text` writes CRLF on Windows) and, for 04 and 07, the recorded Python
and SymPy versions (the shipped runs record Python 3.13.5 and SymPy
1.14.0). Compare modulo CR. Do not use Python's `-O` switch: the programs
check by assertions.

Hazards:

- **`data/03-boundary-geometry-counts.csv` has CRLF line endings** (102
  lines), as delivered: `csv.writer` writes CRLF on every platform. A `-text`
  line in `Algebra/SurrealNumbers/.gitattributes` keeps the bytes. Never
  re-save it.
- **The build files name delivery paths** and must not be run in this
  directory. `code/02-transfinite-scales-Makefile` runs
  `python3 code/verify.py` and `pdflatex` three times on `article.tex` in the
  working directory, and its `clean` target removes `article.aux`,
  `article.log` and the like there: run from this directory it would rebuild
  or clean *this* report. `code/06-affine-residues-Makefile` runs `latexmk`
  on `article.tex` and `python3 verify.py` in the working directory.
  `code/04-beyond-all-orders-build.sh` changes into `code/`, creates
  `code/build/` and fails on the missing `article.tex`.
  `code/07-invisible-complexity-build.sh` changes into `code/` and runs
  `python verification/verify.py` and `latexmk` on the missing
  `surreal_polytopes.tex`.

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
- The four build files name `article.tex`, `surreal_polytopes.tex`,
  `code/verify.py`, `verify.py`, `verification/verify.py` and `build/`; see
  the hazards above.
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

## Provenance

- **Pins and placement.** Manuscript 05 compared itself with ProveIt at
  `5e0f4e050`, the others at `6996fee43` (whose commit time 16:07:39 UTC 02
  and 07 print correctly). The six were placed together in `b30441a8c` as one
  new report, because no surreal report, README question or Lean file
  treats polytopes; they are one merged report with three spines rather
  than three reports because they answer one prompt, share one setting and
  triplicate its basic lemmas.
- **Bases.** 05 is the base of Part I and of the report (weaker hypotheses:
  an ordered subfield, against 02's real closed field; stronger conclusions:
  exact leading terms, the flag classification, exact degrees). 07 is the
  base of Part V (every `n ≥ 4`, linear and semidefinite lifts, descent for
  every convex valuation ring, every fixed dimension, the sharper parameter
  count `dN ≤ r(r−1)` against 04's `s ≤ r²`).
- **Where the merge chose.** Duplicated results are printed once with both
  sources and both labels (listed above), with a genuinely different proof
  kept as a "Second proof (source 02/04)". Statements that overlap but add
  something were printed beside each other with a `[write]` note: 02's
  cut-compatible compression and comparison-rank theorems beside 05's
  pivot theorem and corollary, 02's stage threshold beside 05's lemma, 02's
  Puiseux model beside 05's arc theorem, 02's query bound beside 05's
  halting-problem obstruction, 04's transcendence-degree proposition beside
  07's generic bound (07's statement does not cover the circle), 04's
  Yannakakis proposition beside 07's factorization. 02's Section 6, its
  tests, audit, directions, conclusion and appendices form Part II. All
  Lean roadmaps are in Section 83. In Part V the appendix-derived sections
  precede the merged questions, so that the questions end the Part; in
  Parts III and IV the source order (questions, conclusion, appendices) is
  kept. Questions stay with their Parts; where two manuscripts ask the same
  thing they are merged (three pairs in Part V) or cross-referenced (05's
  questions 1, 2, 4, 5 with four of 02's directions; 02's residue direction
  28.5 with Part III's questions 43.3 and 43.6), and a question that
  another manuscript answers in part is re-scoped by a note (Part III's
  face-specialization question by 02's optimality band; Part V's
  factorization question by 04's Theorem 71.2).
- **Checks during the write.** The repository statements of all six were
  re-checked at the current head: `Geometry.lean` and `OmnificUnits.lean`
  (unchanged blobs), the collection READMEs, the transseries report's title,
  subtitle and positive-grading theorem, the computer-algebra report, and
  the absence of "extension complexity" everywhere outside this directory
  and of mixed volumes, Ehrhart theory and curve selection in the Lean
  files (mixed volumes occur only in passing elsewhere in the collection,
  for example in a research question of `autonomous-dilation-relations`);
  all are accurate, so nothing is stale or retracted. The explicit thresholds
  (`1/34`, `1/10`), 07's bounds table (all five rows reproduced) and the
  value group of the rank-two field were recomputed.
- **Author lines.** 05: research manuscript prepared for Vladimir
  Reshetnikov, an AI-assisted contribution to the ProveIt research program.
  02: research article prepared for Vladimir Reshetnikov. 06: research
  article prepared for Vladimir Reshetnikov. 03: research manuscript
  prepared for Vladimir Reshetnikov. 07: research manuscript prepared for
  Vladimir Reshetnikov. 04: research manuscript prepared for Vladimir
  Reshetnikov; developed with ChatGPT; independent review and formalization
  pending.
