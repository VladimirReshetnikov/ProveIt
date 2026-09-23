# Hilbert Geometry at Surreal Scales

**Orthogonal splitting, amplified and infinitesimal graphs, projection-lattice obstructions, metric rigidity, and Fredholm least squares**
Merged research report, 23 September 2026, from two manuscripts written
independently on the same day (batch 27, placed in `a4dcb91`): 03 (the base)
and 06. Prepared for Vladimir Reshetnikov. AI-assisted draft; not refereed; no
Lean formalization.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 55 pages (title, contents i-iii, pages 1-51)
README.md     this guide
03-orthogonal-splitting-proof_audit.md    source 03's proof-audit ledger, as delivered
06-hilbert-foundations-RESEARCH_AUDIT.md  source 06's repository and literature audit, as delivered
code/
  03-orthogonal-splitting-checks.py        source 03 checks (SymPy; 16 named checks)
  06-hilbert-foundations-verify_finite.py  source 06 checks (standard library; 234 identities)
  06-hilbert-foundations-build.sh          source 06's build script for its own manuscript (not shipped)
data/
  03-orthogonal-splitting-check_results.json  recorded run of the source 03 checks
  03-orthogonal-splitting-check_results.txt   byte copy of the JSON file, as delivered
  03-orthogonal-splitting-build_report.txt    source 03's record of building its own PDF
  06-hilbert-foundations-verification.json    recorded run of the source 06 checks
```

Every label in `article.tex` carries the prefix `hgeo:`; the report has 142
labels. The placed text was source 03 with 69 bare labels; nothing in the
collection cited them, and each was prefixed unchanged (`thm:threshold` is
`hgeo:thm:threshold`, `thm:lattice` is `hgeo:thm:lattice`, and so on). The
source manuscripts and their PDFs are not shipped. `code/`, `data/` and the two
audit files are byte-identical to the deliveries; they refer to the sources'
own file names and theorem numbers (for example source 03's Theorem 7.2 is
Theorem 8.3 here), not to this report's.

## Two sources, one report

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **03** | *Hilbert Geometry at Surreal Scales: Orthogonal Splitting, Amplified Graphs, and Fredholm Least Squares* (29) | `9a385d3` | **The base.** Residue normal form and graph chart; amplification threshold for bounded operators; lattice dichotomy with the finite-dimensional converse; Fredholm reduction, Moore–Penrose inverse, exact inverse valuation; scale coherence; class descent in NBG without global choice; fine-net stabilization. Files `03-orthogonal-splitting-*`. |
| **06** | *Hilbert Geometry at Surreal Scales: Orthogonal subspaces, infinitesimal graphs, metric rigidity, and projection-lattice obstructions* (25) | `a45d722` | The `c00` example; the strict-contraction functional; unitary orbits, the unitary group, finite simultaneous straightening; graphs of closed densely defined operators and the distance cut; the positive operator with a noncomplemented kernel; the missing countable join and two obstructions to countable straightening; metric rigidity; the global geometry corollary; the Solèr framing. Files `06-hilbert-foundations-*`. |

- **Why one report.** Both work in the same space (Part I of the
  infinite-dimensional spectral report), prove the same central classification
  and the same no-meet example, and each has a large part the other lacks.
- **Base.** 03 has the weaker hypotheses on every shared theorem: the lattice
  theorem for every infinite-dimensional `H` with its converse (06: `ℓ²`, one
  direction), the class descent without global choice (06: with it), an
  arbitrary amplification scalar (06: a monomial).
- **Printed once.** Positivity, spherical completeness, automatic adjoints,
  the integral-projection lemma (both proofs kept), the normal form, the graph
  chart, the no-meet construction (identical up to swapping coordinates), the
  class descent, fine discreteness.
- **Printed by citation, not reprinted.** `ihs:hh:thm:adjoint` and
  `ihs:hh:cor:autobounded` (both sources reprove them; the rectangular form
  follows from the square one by a two-line reduction), `ihs:hh:thm:norm`,
  `ihs:hh:prop:inner`, `duals:prop:spherical`, `duals:thm:riesz`, the rotation
  lemma `ihs:fr:lem:rotation`, the finite report's `thm:leastsquares`,
  `thm:scales`, `lem:DeltaInvariant` (03's elimination proof of its Lemma 11.1
  is kept as a second route), and `a:thm:discrete`.
- **Renamed symbols** (Section 1.3, Table 3). 06's `F`/`K` were swapped (real
  `K`, complex `F`); here `F = R((t^Γ))`, `K = C((t^Γ))`, as in 03 and the
  spectral reports. 06's `E_Γ(H)` for the whole space is `ℋ_Γ(H)`, because the
  three-duals report's `E_Γ(V)` is the algebraic extension. 06's `τ = t^δ`,
  `S`, `D = diag(n)`, `𝒜_Γ`, `𝒰`, metric `G` are `q = t^η`, `T`, `Λ = T⁻¹`,
  `𝓑_Γ`, `𝖴`, `Θ`; 03's Fredholm blocks and auxiliary letters that met `F`,
  `G`, `D` were renamed.

## Results added in the merge

Each is marked `[merge]` and has a complete proof.

- **Scaled closed relations** (Theorem 8.10, Corollary 8.11). For a closed
  linear relation `R ⊆ H ⊕ G` and `v(b) > 0`, `M_b(R) = {(x, by)}` has residue
  `dom R ⊕ mul R` and is orthogonally split iff `dom R` is closed. 03's
  threshold (infinite case, via the coordinate flip and `R = Graph(T)⁻¹`) and
  06's criterion for closed densely defined `A` (`R = Graph A`) are corollaries.
  The two source theorems are printed in full, since neither implies the other
  and the relation theorem gives neither 03's finite-scalar clause nor 06's
  orthogonal complement.
- **Closed residue is not sufficient** (Proposition 6.7): the details of a
  remark of 06. `Graph(q f̂)` for a discontinuous functional `f` is valuation
  closed with closed residue `H ⊕ 0` but has zero orthogonal complement. This
  settles negatively the case 03's Remark 6.7 leaves open.
- **Rectangular reductions** of the automatic adjoint theorem and the
  norm-attainment criterion (Theorems 5.2, 4.4).
- **Comparison with the Hahn Fredholm alternative** (Remark 11.2): Theorems
  11.1 and 12.1 contain the determinant-free clauses of `ihs:fr:thm:fredholm`
  (index zero, equal kernel and cokernel dimensions, inverse in the algebra iff
  bijective), for any index, between different spaces, with bounded rather
  than trace-class coefficients; nothing about the determinant.

## What the report claims

`H`, `G` ordinary real or complex Hilbert spaces, `Γ` a set-sized ordered
abelian group (nonzero where needed, never assumed divisible), `ℋ_Γ(H) =
H((t^Γ))` with the coefficientwise inner product, `𝓑_Γ(H,G) = B(H,G)((t^Γ))`.

- **Classification** (Theorem 6.5, Corollary 6.6; 03, 06). `M` is
  orthogonally split iff `M = U ℋ_Γ(M_0)` with `U` unitary, `v(U − I) > 0`,
  `M_0 = res M` ordinary closed; equivalently `M` is the graph of a
  positive-order `X ∈ 𝓑_Γ(M_0, M_0^⊥)`. Given `ihs:fr:lem:rotation` this is a
  corollary of the integral-projection lemma (Lemma 6.3). Closed residue is
  necessary (Corollary 6.4), not sufficient (Proposition 6.7).
- **Unitaries** (06). Orbits of projections are classified by two ordinary
  dimensions (Corollary 7.1); every adjointable unitary is `Û_0 exp X` uniquely
  with `X` skew and of positive order (Theorem 7.2); finite orthogonal
  decompositions straighten simultaneously (Theorem 7.3).
- **Graphs.** `Graph(aT)` for bounded `T` is split iff `a = 0`, `v(a) ≥ 0`, or
  `ran T` is closed; for `v(a) < 0` the residue is `ker T ⊕ ran T`
  (Theorem 8.3; 03); an explicit graph with no nearest point, not repaired by
  enlarging `Γ` (Example 8.5, Corollary 8.6). For closed densely defined `A`,
  `M_q(A)` is orthoclosed and spherically complete, `M_q(A)^⊥ =
  {(−qA*y, y)}`, residue `Dom A ⊕ 0`, split iff `A` bounded (Theorem 8.7; 06);
  no nearest point (Corollary 8.8) and, for `Λ = diag(n)`, a distance set whose
  lower bounds are exactly `0` and the positive infinitesimals
  (Proposition 8.9, the cut of `duals:thm:distance`).
- **Projection poset.** `Spl(ℋ_Γ(H))` is an orthomodular poset (Proposition
  9.1); for `Γ ≠ 0` it is a lattice iff `dim H < ∞`, with an explicit pair
  without meet (Theorem 9.2; 03, one direction also 06). `L = B*B` with
  exponents `0, η, 2η` has a noncomplemented kernel; the algebra is not
  Rickart (Theorem 9.4; 06). A countable orthogonal family of rank-one
  projections has no join (Theorem 9.5); countable simultaneous straightening
  fails by unbounded coefficients (Corollary 9.6) and, if `Qη ⊆ Γ`, by
  incoherent supports (Proposition 9.7).
- **Metric rigidity** (Theorem 10.1, Corollary 10.2; 06). A positive metric
  `Θ = Θ̂_0 + Θ_+` with strictly positive `Θ_0` is isometric to the canonical
  one by some linear bijection (no regularity assumed) iff `Θ_0 ≥ c > 0`;
  `T² + q²I` is coercive but not isometric.
- **Fredholm least squares** (Theorems 11.1, 12.1, 13.2, Corollaries 12.2,
  13.3, Example 13.4; 03). For `A = T_0 + E`, `T_0` ordinary Fredholm,
  `v(E) > 0`: `dim ker A = m − r`, `dim coker A = n − r`, index `m − n`;
  `ker A`, `ran A` split; `A†` exists in `𝓑_Γ(G,H)` with an explicit formula;
  all least-squares problems have minimum-norm solutions; `v(A†) =
  −(ν_r − ν_{r−1})` for `r > 0`, and `A†` is integral with residue `T_0†` iff
  `S = 0`.
- **Scale extension and the whole class** (Proposition 14.1, Theorem 14.2,
  Corollary 14.3, Proposition 14.4; 03, 06). Constructions transport along any
  ordered embedding; in NBG without global choice every class-linear map with
  an everywhere-defined class adjoint has one set-sized support of ordinary
  bounded coefficients, so the geometry, the counterexamples and metric
  rigidity hold over literal `No` and `No[i]`; every set of global vectors is
  closed and discrete in the fine topology (vector form of `a:thm:discrete`).

## What the report does not claim

- Both sources are AI-assisted, unrefereed drafts; priority is not certified;
  no named published conjecture is claimed solved; nothing is formalized and
  `docs/FORMALIZATION.md` maps none of these labels.
- The construction, positivity, completeness, automatic adjoints, norm bounds,
  the Riesz failures, the direct rotation and the finite Moore–Penrose and
  scale theorems are background, cited or credited, not contributions.
- Closed residue is not sufficient for splitting; whether every orthoclosed
  subspace with closed residue splits is open (Question 15.2). Fredholm is
  sufficient, not necessary, for an adjointable `A†` (Question 15.1). No
  sufficient condition for infinite orthogonal synthesis is proved
  (Question 15.3). No spectral measure, spectral theorem or physical
  interpretation is claimed.
- The class results are algebraic; the global class is not a set-sized
  Hilbert space, and completions are not claimed to commute with scale
  enlargement.
- Appendix B keeps every limitation stated by a source, numbered per source:
  03 (34 items), 06 (33), and 6 for the merge (73 in all).
- The finite checks verify finite identities only.

## Corrections and stale statements

The pins `9a385d3` (03) and `a45d722` (06) are 35 and 30 commits before the
placement; none of the cited reports changed in between, so the corrections are
omissions of the sources (Appendix A.4):

- neither source credits `ihs:fr:lem:rotation`, which already is the rotation
  for every projection with `v(P − P°) > 0`;
- 03 does not compare its Fredholm theorems with `ihs:fr:thm:fredholm`, and does
  not cite the finite spectral-theory report (`thm:leastsquares`, `thm:scales`,
  `lem:DeltaInvariant`, and `spec:thm:svd`, which at 03's pin already covered
  nondivisible `Γ`);
- 06's distance cut does not credit `duals:thm:distance`;
- neither cites `a:thm:discrete` or the Lean-formalized `found:thm:discrete`;
- 06 assumes global choice for its descent theorem; its proof does not use it;
- 06's theorem numbers for the spectral and duals reports (Theorems 6.1, 11.3,
  13.2; Propositions 5.1, 8.1 and Sections 8-9) are correct at the current build and are replaced by labels;
- 03's "not developed" items (unbounded operators with proper domains,
  infinite-family joins) and its Remark 6.7 are settled within the report by 06
  and by Proposition 6.7 (the joins and the remark negatively).

## Relations to neighbouring reports

- [`infinite-dimensional-hahn-spectral-theory`](../infinite-dimensional-hahn-spectral-theory/):
  the space and the background theorems of Part I; the rotation lemma and the
  Fredholm alternative of Part IV. The first further question of Part IV
  (`ihs:fr:sec:questions`: when do all cluster rotations assemble into a
  bounded-coefficient Hahn unitary?) gets only necessary conditions here
  (Corollary 9.6, Proposition 9.7: bounded coefficient synthesis and a
  coherent common support); it and the other two questions there stay open.
  Part I's remark about "a stronger orthogonal-completeness axiom" is
  constrained by Solèr's theorem (Sections 15.1, 15.2). No contradiction with
  `ihs:rf:thm:commutant` (constant coordinate projections).
- [`three-duals-of-hahn-vector-spaces`](../three-duals-of-hahn-vector-spaces/):
  spherical completeness, the Riesz criterion, the closed hyperplane and the
  distance cut, repeated here for an orthoclosed subspace.
- [`spectral-theory`](../spectral-theory/): the finite Moore–Penrose, least
  squares and determinantal-scale theorems that Sections 11 and 13 transport
  through the infinite Schur reduction.
- [`analysis`](../analysis/) and
  [`foundations`](../../foundations-and-computation/foundations/): fine
  discreteness of sets.
- [`hidden-negative-hermitian-directions`](../hidden-negative-hermitian-directions/):
  two-scale positivity, related in spirit to the metric rigidity theorem;
  neither answers a question of the other.

## Build

From a copy of this directory in a scratch location:

```
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The build has no errors, no LaTeX or package warnings, no overfull or
underfull boxes, no undefined references or citations, no multiply defined
labels and no duplicate destinations. pdfTeX prints one informational
`ignored: Infinite glue shrinkage found in box being split` line where a
captioned longtable breaks across pages (the committed omnific-groups report
prints the same). Commit only `article.pdf`, not the auxiliary files.

## Reproducing the finite checks

Run them **on a copy**: 03's script writes `verification/check_results.json`
next to itself, and 06's writes `verification.json` in the working directory by
default.

```
mkdir /path/to/scratch && cp code/*.py /path/to/scratch/ && cd /path/to/scratch
python -m pip install sympy==1.14.0
python 03-orthogonal-splitting-checks.py                 # writes ./verification/check_results.json
python 06-hilbert-foundations-verify_finite.py --output verification.json
```

Expected: 03 prints a JSON report ending with `"summary": "16 checks passed,
including 125 exponent triples."`, and its written JSON equals
`data/03-orthogonal-splitting-check_results.json` except for the recorded
Python version; 06 prints `"status": "PASS"` with `"total_identity_checks": 234`
and `"formal_prefix_order": 14`, and its JSON equals
`data/06-hilbert-foundations-verification.json` up to line endings. The reruns
for this report used Python 3.14.4 and SymPy 1.14.0 (the recorded 03 run used
Python 3.13.5). The checks cover finite projection, rotation, Schur, Penrose and
pole identities only; they do not verify support well-ordering, Baire
arguments, unbounded domains, the nonexistence of meets, joins or projections,
or any class assertion. `code/06-hilbert-foundations-build.sh` builds source
06's own manuscript, which is not shipped, and cannot be run here.
