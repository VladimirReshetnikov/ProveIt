# Hilbert Geometry at Surreal Scales

**Orthogonal splitting, amplified and infinitesimal graphs, projection-lattice obstructions, infinite unitary straightening, metric rigidity, and Fredholm least squares**
Merged research report, 23 September 2026, from two manuscripts written
independently on the same day (batch 27, placed in `a4dcb91`): 03 (the base)
and 06; batch 34 (placed in `a7a435f`) adds a third manuscript, 07, written
later against this report, as Sections 16-23. Prepared for Vladimir
Reshetnikov. AI-assisted draft; not refereed; no Lean formalization.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 83 pages (title, contents i-iv, pages 1-78)
README.md     this guide
03-orthogonal-splitting-proof_audit.md    source 03's proof-audit ledger, as delivered
06-hilbert-foundations-RESEARCH_AUDIT.md  source 06's repository and literature audit, as delivered
code/
  03-orthogonal-splitting-checks.py        source 03 checks (SymPy; 16 named checks)
  06-hilbert-foundations-verify_finite.py  source 06 checks (standard library; 234 identities)
  06-hilbert-foundations-build.sh          source 06's build script for its own manuscript (not shipped)
  07-unitary-synthesis-verify.py           source 07 checks (SymPy 1.14.0; 159 assertion groups)
  07-unitary-synthesis-build.sh            source 07's POSIX build script for its own manuscript (not shipped)
  07-unitary-synthesis-build.ps1           source 07's PowerShell build script for its own manuscript (not shipped)
data/
  03-orthogonal-splitting-check_results.json  recorded run of the source 03 checks
  03-orthogonal-splitting-check_results.txt   byte copy of the JSON file, as delivered
  03-orthogonal-splitting-build_report.txt    source 03's record of building its own PDF
  06-hilbert-foundations-verification.json    recorded run of the source 06 checks
  07-unitary-synthesis-verification_results.json  recorded run of the source 07 checks
  07-unitary-synthesis-requirements.txt       source 07's Python requirement (sympy==1.14.0)
  07-unitary-synthesis-BUILD_REPORT.json      source 07's record of building its own 22-page PDF
```

Every label in `article.tex` carries the prefix `hgeo:`; the report has 217
labels: the 142 of the batch-27 merge, all kept with unchanged numbers, and 75
added in batch 34 under the sub-prefix `hgeo:us:` (unused before). The placed
text was source 03 with 69 bare labels, each prefixed unchanged
(`thm:threshold` is `hgeo:thm:threshold`, `thm:lattice` is
`hgeo:thm:lattice`, and so on); source 07's bare labels were replaced by
`hgeo:us:` names (`thm:main` is `hgeo:us:thm:main`, `thm:uniform-counter` is
`hgeo:us:thm:uniform`). The formalization ledger indexes the batch-27
statements under their labels, all **Pending**, with no checked
implementation mapping; it does not yet list the `hgeo:us:` labels. The
source manuscripts and their PDFs are not shipped, and no source 07 audit
markdown was delivered (its provenance appendix is printed as Appendix A.5).
`code/`, `data/` and the two audit files are byte-identical to the
deliveries; they refer to the sources' own file names and theorem numbers
(for example source 03's Theorem 7.2 is Theorem 8.3 here, and source 07's
Theorem 3.2 is Theorem 17.2), not to this report's.

## Three sources, one report

| | Manuscript (pages) | Pin | Contributes |
|---|---|---|---|
| **03** | *Hilbert Geometry at Surreal Scales: Orthogonal Splitting, Amplified Graphs, and Fredholm Least Squares* (29) | `9a385d3` | **The base.** Residue normal form and graph chart; amplification threshold for bounded operators; lattice dichotomy with the finite-dimensional converse; Fredholm reduction, Moore–Penrose inverse, exact inverse valuation; scale coherence; class descent in NBG without global choice; fine-net stabilization. Files `03-orthogonal-splitting-*`. |
| **06** | *Hilbert Geometry at Surreal Scales: Orthogonal subspaces, infinitesimal graphs, metric rigidity, and projection-lattice obstructions* (25) | `a45d722` | The `c00` example; the strict-contraction functional; unitary orbits, the unitary group, finite simultaneous straightening; graphs of closed densely defined operators and the distance cut; the positive operator with a noncomplemented kernel; the missing countable join and two obstructions to countable straightening; metric rigidity; the global geometry corollary; the Solèr framing. Files `06-hilbert-foundations-*`. |
| **07** | *Simultaneous Unitary Straightening at Surreal Scales: An exact synthesis criterion, atomic spectral calculus, and uniformly controlled counterexamples* (22) | `fc27d87` | Added in batch 34 (manuscript 09; archive `surreal_unitary_synthesis`, delivered in `a4611ad`) as Sections 16-23; see "Source 07" below. Files `07-unitary-synthesis-*`. |

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

The bullets above describe the batch-27 merge of 03 and 06; the batch-34
addition of 07 is described in the next section.

## Source 07: infinite simultaneous straightening (batch 34)

| Manuscript | Pin | Contributes |
|---|---|---|
| 07 = batch 34, manuscript 09: *Simultaneous Unitary Straightening at Surreal Scales* (22 pp., dated 23 September 2026) | `fc27d87` (61 commits before the placement `a7a435f`; neither this report nor the spectral report changed in between, apart from the placement) | The exact criterion (B)+(H) with an explicit unitary for complete and incomplete families; no new scales, gauge classification, scale-enlargement invariance; the finite-jet theorem and the first-order equation; the atomic-calculus equivalence, joins, weighted reconstruction; the uniformly controlled counterexample with a missing join; bounded columns with incoherent support; surreal descent; omnific matrix rigidity; 12 questions. |

- **Placement.** New Sections 16-23 after Section 15, and new subsections
  A.5 (07's provenance appendix), B.4 (07's non-claims), B.5 (the addition's
  non-claims), rows in Tables 1-4 and a paragraph in Appendices C and D, so
  that no existing section, theorem, equation, table or item number changed
  (checked against a build of the committed text: all 142 earlier labels
  keep their numbers).
- **Number map** (07 -> here). Lemma 2.1 -> Lemma 16.1; Def. 3.1, Thm. 3.2 ->
  Def. 17.1, Thm. 17.2; Cors. 5.1-5.3 -> Cors. 18.1-18.3; Cor. 5.4 -> Theorem 7.3
  (Remark 17.3); Thm. 5.5, Prop. 5.6 -> Thm. 18.4, Prop. 18.5; Def. 6.1, Thm.
  6.2, Props. 6.3, 6.4 -> Def. 19.1, Thm. 19.2, Props. 19.3, 19.5; Thm. 7.1, Rem.
  7.2 -> Thm. 20.1, Rem. 20.2; Thm. 8.1 -> Thm. 21.1; Cor. 9.1, Thm. 9.2 -> Cor.
  22.1, Thm. 22.3; Questions 11.1-11.12 -> Questions 23.1-23.12.
- **Printed once.** 07's Lemma 2.1 with Lemma 6.3 and the unitary residue
  argument of Corollary 7.1; its support principle, formal functions and
  strong summability with Lemma 2.1, (5.2) and Definition 2.2; its surreal
  substitution with (2.2); its finite-family corollary is Theorem 7.3,
  re-derived from the criterion (the two constructions agree: Remark 17.3).
- **Second routes kept.** The necessity direction of Theorem 17.2 contains
  Corollary 9.6 and Proposition 9.7 (Remark 17.4); 06's direct proofs are
  kept. Theorem 21.1's first projections are Proposition 9.7's with `η = 1`;
  both nonexistence proofs are printed.
- **Added in the merge** (`[merge]`, complete proofs): Remark 17.3 (in the
  finite case `P_∨ = Σ P_j` and `W` is Theorem 7.3's `W` for the family with
  its complement adjoined); Remark 17.4 (the countable obstructions of
  Section 9.4 are instances of necessity); Remark 19.4 (joins for incomplete
  families and real scalars; `P_∨` is the join of the family; the criterion
  is sufficient, not necessary, for joins); Remark 21.2 (Theorem 21.1 over
  any group containing `Qη`); Corollary 22.2 (class unitaries, from Theorem
  14.2(ii)); the status notes.
- **Renamed symbols** (Section 16.3, Table 3). 07's `𝔽 ∈ {R, C}`, `K`, `ℋ`,
  `𝒜`, `𝒜_{≥0}`, `𝒜_{>0}`, `I_H` are `𝕜`, `F`/`K`, `ℋ_Γ(H)`, `𝓑_Γ(H,H)`,
  `𝓑^{≥0}_Γ`, `𝓑^{>0}_Γ`, `I`; index set `I` -> `𝓘`, finite subsets `J` -> `𝓙`,
  subsets `A, B` -> `𝓢`, left-half set `J` -> `𝓛`, basis index `J` -> `𝓝`;
  `F = I − E` -> `E^⊥` (`F` is the real Hahn field); calligraphic `𝒟_E` ->
  script `𝒟_E` (`\mathscr D`, since `\mathcal D` is the Schur block matrix);
  `G = C*C + F` -> `Ω`
  (`G` is a Hilbert space); `Q = C G⁻¹ C*` -> `P_∨` (the report's `Q_j`, `Q_n`
  are residue projections, 07's `E_j`); `T = C + (I − Q)F` -> `W` (Theorem 7.3's
  `W` in the finite case; `T = diag(1/n)`); `B = (T*T)^{-1/2}` -> `|W|⁻¹` (a
  formal series; `B` is the row operator); generic `R` -> `Y`, upper bound `R`
  -> `P'`, `S = U*RU` -> `P''`; `R_m = exp(tA_m)`, `A_m`, `u_m, v_m`, `F_m` ->
  `V_m = exp(tX_m)`, `X_m`, `u_m, u_m'`, `Π_m` (`v` is the valuation); `J`
  (2×2), `q_n = t^{1/n}`, `R_n` -> `𝖩`, `t^{1/n}`, `V_n` (`q = t^η` is fixed);
  first-order `K`, `D` -> `Y`, `Y_c` (`K` is the complex field); gauge `W` ->
  `Ξ`; residue `V = U_0`, second straightener `V` -> `U_0`, `U'`; `𝒜_N` ->
  `𝓑^{[N]}`; `A_λ` -> `N_λ`; generic `T` -> `A`; `⟨S⟩` -> `S*`. 07's inner
  product is conjugate-linear in the first argument, the report's linear;
  its rank-one maps and matrix entries are converted (same maps). Kept with
  a scoped meaning: `E` (a residue projection, never the Fredholm
  perturbation of Sections 11-13), `C` (the column series), `Φ, Ψ`, `S`
  (supports, not the Schur matrix). Tempting false reading: `P_∨` is not the
  formal sum of the `P_i` (it is only for finite families).
- **Stale scope in 07.** 07 deliberately does not use an automatic
  class-operator representation theorem (Theorem 14.2 here) and asks for one
  (its Question 11.10, here 23.10); for maps with an everywhere-defined class
  adjoint Theorem 14.2(ii) already gives it, so the merge adds Corollary 22.2
  and a status note. 07 names the finite straightening statement and the
  support-incoherence obstruction of this report without labels (Theorem 7.3,
  Proposition 9.7). Appendix A.4 items 11-14.
- **Dossier numbering.** 07's joins and weighted-reconstruction
  propositions are its Propositions 6.3 and 6.4 (not 6.4 and 6.5).

### What source 07 settles

- **Question 15.3** (infinite orthogonal synthesis): answered. A set-indexed
  orthogonal family `(P_i)` in `𝓑_Γ(H,H)`, `Γ` any set-sized ordered group, `H`
  real or complex, residues `E_i`, `E = SOT-Σ E_i` (incomplete families
  allowed), has a unitary `U` with `P_i = U E_i U*` for all `i` (equivalently a
  near-identity one) iff **(B)** every canonical column
  `C_γ^fin(Σ x_i) = Σ (P_i)_γ x_i` extends to a bounded operator and **(H)** the
  active support `S_C` is well ordered (Theorem 17.2). Explicitly
  `Ω = C*C + E^⊥`, `P_∨ = C Ω⁻¹ C*`, `W = C + (I − P_∨)E^⊥`, `U = W (W*W)^{-1/2}`;
  complete case `U = C (C*C)^{-1/2}`. Stability under composition, also asked
  there, is not treated.
- **Question 15.5** (which countable families have joins): answered in part.
  Families satisfying the criterion, and all their subfamilies, have joins
  (Proposition 19.3, Remark 19.4); Theorem 20.1 adds another family with a
  subfamily lacking a join. No characterization.
- **Question 15.2** (orthoclosed subspaces with closed residue): open; 07
  restates it (Question 23.1).
- **The first further question of the spectral report's Part IV**
  (`ihs:fr:sec:questions`): answered in exact-criterion form for the family
  of cluster projections ((B) at every order plus (H); Proposition 18.5 is the
  corresponding first-order equation), not in the spectral-gap and
  coefficient-ideal form in which it is posed. That report is not edited.

### Claims of source 07

- No new scales: `supp(U − I) ∪ supp(P_∨ − E) ⊆ S*` for `S = S_C \ {0}`
  (Corollary 18.1); straighteners are unique up to commuting near-identity
  gauges (Corollary 18.2); solvability is invariant under every ordered scale
  enlargement (Corollary 18.3).
- For `Γ = Z`: one near-identity jet mod `t^{N+1}` for the whole family at
  every `N` (no compatibility, no uniform bound) implies a formal straightener
  (Theorem 18.4). For complete families a bounded skew-adjoint solution of
  `[Y, E_i] = (P_i)_1` exists iff `C_1` is bounded, and then `Y = C_1 + Y_c`
  with `Y_c` commuting (Proposition 18.5).
- For complete families (complex `H`) the criterion is equivalent to a
  unique normal completely bounded coefficientwise atomic calculus
  `Φ(a) = U ρ(a) U*` (Theorem 19.2); `P(𝓢) = U E(𝓢) U*` is the join of
  `{P_i : i ∈ 𝓢}` (Proposition 19.3); coherent eigenvalue data reconstruct a
  unique normal operator (Proposition 19.5).
- A complete rank-one family in `𝓑(ℓ²)[[t]]` (blocks of dimension `4^{m²}`)
  with supports in `N` and `sup_i ‖(P_i)_n‖ < ∞` at every order `n` has no
  straightener at any scale, although every finite subfamily straightens;
  its left-half subfamily has no join, while the whole family has join `I`
  (Theorem 20.1). This strengthens Corollary 9.6 (coefficient norm `n` there)
  and Theorem 9.5.
- Over `Γ = Q` (merge: any `Γ ⊇ Qη`), a complete rank-one family satisfies
  (B) with `b_γ ≤ 1` but fails (H) (Theorem 21.1); its first projections are
  those of Proposition 9.7.
- Surreal descent for set-supported series (Corollary 22.1; merge: class
  unitaries, Corollary 22.2); projections and unitaries with entries in `Oz`
  or `Oz[i]` are coordinate projections and signed or Gaussian-phase
  permutations (Theorem 22.3, elementary).

### What source 07 does not claim

Kept as items 07.1-07.26 of Appendix B.4, with 7 items for the addition in
B.5. In short: an AI-assisted unrefereed draft, priority not established, not
Lean; the criterion is not a decision procedure; straighteners are unique
only up to gauge; classical polar decomposition, projection geometry,
support calculus and the omnific normal form are credited, not claimed; the
repository's lattice counterexamples and support obstruction are not claimed
for the first time; the atomic calculus is not strong Hahn summability or
valuation convergence, and there is no continuous spectral measure or
general spectral theorem; not every normal operator has atomic data, and its
spectrum is not claimed to be the labels; automatic regularity of atomic
representations is open; the surreal descent is for the specified category
(set-supported bounded-coefficient series), not all class-linear maps (the
merge's Corollary 22.2 extends it only to maps with an everywhere-defined
class adjoint); omnific rigidity is elementary; the closed-residue question is
not settled; the setting is not a non-Archimedean Banach space with an
unspecified completion; the Abramov announcement on Conway's refinement
conjecture is cited for provenance only; the repository review covered
catalogues and four guides, not the long proofs; the literature check was
targeted; the finite checks test finite identities only.

## Results added in the batch-27 merge

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
  sufficient, not necessary, for an adjointable `A†` (Question 15.1). Sources
  03 and 06 prove only necessary conditions for infinite orthogonal
  synthesis; source 07's exact criterion (Theorem 17.2) answers Question 15.3,
  but it is not an effective test, and a characterization of the families
  with joins is not given (Question 15.5). No spectral measure, spectral
  theorem or physical interpretation is claimed.
- The class results are algebraic; the global class is not a set-sized
  Hilbert space, and completions are not claimed to commute with scale
  enlargement.
- Appendix B keeps every limitation stated by a source, numbered per source:
  03 (34 items), 06 (33), 6 for the batch-27 merge, 07 (26) and 7 for the
  batch-34 addition (106 in all). Merge item M.4 was updated: the spectral
  report's assembly question is now answered in criterion form.
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

For source 07 (pin `fc27d87`, 61 commits before its placement), Appendix A.4
items 11-14: its references to this report and to the spectral report are
still correct; it leaves Theorem 7.3 and Proposition 9.7 unnamed; it asks for
the class representation theorem that Theorem 14.2(ii) already gives for
adjointable maps; its build scripts and build report refer to its own
unshipped manuscript. In this report, the sentence "These are necessary
conditions only; no sufficient condition is proved" after Proposition 9.7
and the "No sufficient hypothesis is proved" sentence after Question 15.3
are rewritten, and Questions 15.2, 15.3, 15.5 carry "Status (batch 34)"
notes; no question was deleted.

## Relations to neighbouring reports

- [`infinite-dimensional-hahn-spectral-theory`](../infinite-dimensional-hahn-spectral-theory/):
  the space and the background theorems of Part I; the rotation lemma and the
  Fredholm alternative of Part IV. The first further question of Part IV
  (`ihs:fr:sec:questions`: when do all cluster rotations assemble into a
  bounded-coefficient Hahn unitary?) gets necessary conditions from 03 and 06
  (Corollary 9.6, Proposition 9.7) and, from 07, an exact criterion for the
  family of cluster projections (Theorem 17.2: (B) at every order plus (H);
  Proposition 18.5 is the first-order equation), not in the spectral-gap form
  in which it is posed; the other two questions there stay open. 07
  distinguishes its bounded-coefficient category from Part II's row- and
  column-finite one. That report is not edited here.
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
labels and no duplicate destinations. pdfTeX prints an informational
`ignored: Infinite glue shrinkage found in box being split` line where a
captioned longtable breaks across pages (the committed omnific-groups report
prints the same): once before batch 34, four times now, because the rows
added to Tables 2-4 make them break at more places. Commit only
`article.pdf`, not the auxiliary files.

## Reproducing the finite checks

Run them **on a copy**: 03's script writes `verification/check_results.json`
next to itself, 06's writes `verification.json` in the working directory by
default, and 07's writes `verification_results.json` in the working directory
by default (`--output` names another path).

```
mkdir /path/to/scratch && cp code/*.py /path/to/scratch/ && cd /path/to/scratch
python -m pip install sympy==1.14.0
python 03-orthogonal-splitting-checks.py                 # writes ./verification/check_results.json
python 06-hilbert-foundations-verify_finite.py --output verification.json
python 07-unitary-synthesis-verify.py --output verification_results.json
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

07 prints `Passed 159 exact assertion groups; results: ...`, and its JSON
equals `data/07-unitary-synthesis-verification_results.json` up to line
endings (rerun for batch 34 with Python 3.14.4 and SymPy 1.14.0 on Windows,
which wrote CRLF; the record stores the SymPy version, not the Python
version). The 159 groups: the construction on a complete rank-one family of
size 3 to order 6 (38), an incomplete family of size 4 to order 6 (28) and a
complete block family of size 5 to order 5 (37); flat-block identities for
`m = 1, 2, 3` with block dimensions 1, 4, 9 rather than `4^{m²}` (14 each);
the support block to order 10 (14). They do not verify well-ordered support,
bounded extension from a dense subspace, unboundedness across infinitely many
blocks, or novelty. The script's docstring and 07's delivered README call it
`verify.py`; `code/07-unitary-synthesis-build.sh` and `.ps1` run pdfLaTeX on an
`article.tex` next to themselves (07's unshipped manuscript) and cannot build
this report; `data/07-unitary-synthesis-BUILD_REPORT.json` names 07's own
`article.pdf` and `verification_results.json`.
