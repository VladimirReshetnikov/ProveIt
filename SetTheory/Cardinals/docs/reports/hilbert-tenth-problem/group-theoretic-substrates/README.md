# Groups as Diophantine Substrates

**Arithmetic van Kampen certificates, three commutative phases, pair order and affine matrix inputs: low-degree certificates through the integral Heisenberg group**

This is a research report dated 2 October 2026, built from four manuscripts
of ProveIt's incoming reports: manuscripts 03 and 05 of batch 76 (Parts I
and II) and manuscripts 09 and 13 of batch 78 (Parts III and IV). All four
are AI-assisted research manuscripts "prepared for Vladimir Reshetnikov".
They are called *source 03*, *source 05*, *source 06* and *source 07* after
the file prefixes of their shipped programs and data. The batch-76 prefixes
are those manuscripts' numbers; the batch-78 prefixes `06-` and `07-`
continue this report's own sequence and are **not** batch-78 manuscript
numbers.

| Source | Manuscript | Archive (arrival commit) | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 03 (base) | batch 76, manuscript 03 | `arithmetic_van_kampen.zip` (`6914ccca6`); *Arithmetic van Kampen Certificates: Quartic equations, exact filling area, and optimal proof-DAG compression*, main file `arithmetic_van_kampen.tex`, 29-page PDF | `c58206ca1` | `2a04b60f2` | Part I (Sections 2–17) and Appendices A–C |
| 05 | batch 76, manuscript 05 | `three_commutative_phases_research.zip` (`6914ccca6`); *Three Commutative Phases Are Diophantine-Universal: A fibre-preserving Heisenberg compiler and a proposed resolution of the three-subgroup problem*, main file `article.tex`, 22-page PDF | `433df1be3` | `2a04b60f2` | Part II (Sections 18–31) and Appendices D–F |
| 06 | batch 78, manuscript 09 | `Order_Is_Not_a_Moment.zip` (`808b53ed8`); *Order Is Not a Moment: Exact Pair-Count Geometry and Diophantine Certificates for Heisenberg Computation*, main file `article.tex`, 26-page PDF | `4cccfa068` | `41e7f1189` | Part III (Sections 32–42) and Appendices H–I |
| 07 | batch 78, manuscript 13 | `ProveIt_Affine_Matrix_Diophantine_Research.zip` (`48ee077c7`); *Affine Matrix Inputs and Diophantine Universality: Sharp rigidity, exact period bounds, and computation with existential witnesses*, main file `article.tex`, 25-page PDF | `4cccfa068` | `41e7f1189` | Part IV (Sections 43–60) |

Full pins: `c58206ca101d4744a015a0f0104646109357d943` (03),
`433df1be37188224dd00d0561bfb157949cd6320` (05),
`4cccfa06866b6b81b2467e1cf7514ea85ed0216d` (06 and 07). All are ancestors of
their placement commits. Appendix G of the article is the provenance.

Every result, proof, example, remark, limitation, research question and
audit of the four manuscripts is printed. No two of them share a theorem,
and none cites another. Source 03 treats a finitely presented group as a
proof-producing substrate and uses the Heisenberg group as an *area
detector*; source 05 treats an ordered product of three abelian subgroups
of a Heisenberg power as the substrate and uses the Heisenberg group as the
*ambient group*; source 06 treats a three-generator submonoid of a
Heisenberg power and uses the group to *record order* (pair counts of
words); source 07 asks how an ordinary integer input can be loaded into a
fixed matrix subgroup, and uses the cyclic subgroup `⟨h(1,1,0)⟩` as its
test. The shared setup — the integral Heisenberg group, its multiplication,
inverse and power laws — is printed once, in Section 1.2, with two tables
of the letters the Parts use differently (Tables 1 and 2).

**Status: AI-assisted, unrefereed, not formalized.** Part II's main theorem
is a **proposed resolution, unrefereed**, of a published open problem; its
priority is not certified. Sources 06 and 07 state that their priority is
not established either. Nothing in the report is formalized in Lean or
Rocq.

```
article.tex                                          the report, standalone LaTeX with an internal bibliography
article.pdf                                          the compiled report, 123 pages (unnumbered title page, then pages 1–122)
README.md                                            this guide
03-van-kampen-SOURCES.md                             source 03's dependency, provenance and novelty notes, as delivered
07-affine-inputs-SOURCE_AUDIT.md                     source 07's source and claim audit, as delivered
code/03-van-kampen-van_kampen.py                     source 03's exact matrix routines, Sanov decoder and symbolic compilers (SymPy; patched by db3b377f0, see below)
code/03-van-kampen-verify.py                         source 03's deterministic exact-arithmetic tests (imports van_kampen)
code/05-three-phases-build.sh                        source 05's three-pass pdflatex script (delivered layout; see below)
code/05-three-phases-heisenberg_compiler.py          source 05's standard-library exact-integer three-phase compiler (patched by db3b377f0, see below)
code/05-three-phases-verify.py                       source 05's 190,826-assertion verification (imports heisenberg_compiler)
code/06-pair-order-Makefile                          source 06's Makefile (delivered layout; see below)
code/06-pair-order-pair_geometry.py                  source 06's gap constructions, corner decision, polynomial gadgets and quartic export (standard library)
code/06-pair-order-verify.py                         source 06's finite checks; recomputes and compares with the bundled receipt (imports pair_geometry)
code/07-affine-inputs-verify.py                      source 07's exact-arithmetic reference implementation and 91,142-case verification (standard library)
data/03-van-kampen-commutator_budget_1.json          the one-budget compiler for [a,b]: 11 variables, 13 quadratic residuals
data/03-van-kampen-grid_1_1.json                     the shared dyadic grid compiler for [a^2,b^2]: 12 variables, 16 residuals
data/03-van-kampen-grid_1_1_witness.json             a satisfying assignment of the grid example (all values)
data/03-van-kampen-receipt.json                      source 03's recorded run: all checks passed (Python 3.13.5, SymPy 1.14.0)
data/03-van-kampen-render_check.json                 source 03's record of its own 29-page PDF build
data/03-van-kampen-export_check.json                 source 03's record of 4 + 4 sparse-polynomial evaluations
data/03-van-kampen-requirements.txt                  source 03's pin, sympy==1.14.0
data/05-three-phases-circuit.json                    compiler data and generator lists for the circuit example (Section 25.2)
data/05-three-phases-circuit_input.json              its quadratic specification
data/05-three-phases-multiplication.json             compiler data for xy − z = t: all fourteen basis matrices (Section 25.1)
data/05-three-phases-multiplication_input.json       its quadratic specification
data/05-three-phases-profinite_obstruction.json      compiler data for F(x) = 6x² − 5x in H × Z (Section 28)
data/05-three-phases-profinite_obstruction_input.json  its quadratic specification
data/05-three-phases-verification_receipt.json       source 05's recorded run: PASS, 190,826 assertions in 30 families
data/06-pair-order-canonical_c2_quartic.json         the canonical c = 2 quartic: 24 residuals and the expanded polynomial (297 terms, degree 4)
data/06-pair-order-verification_receipt.json         source 06's recorded test counts and the SHA-256 of pair_geometry.py
data/06-pair-order-worked_example.json               captured output of `pair_geometry.py decide 3 2 2 1 4` (the unique 24-witness tuple)
data/07-affine-inputs-verification.json              source 07's recorded run: PASS, 91,142 cases, seed 20261002
```

### Delivered names

Every shipped file other than `article.tex`, `article.pdf` and `README.md`
is byte-identical to the delivery, **except two batch-76 programs**:
`code/03-van-kampen-van_kampen.py` and
`code/05-three-phases-heisenberg_compiler.py` were patched in place by
commit `db3b377f0` ("Apply reviewed guard fixes to imported group
compilers", input-guard repairs reviewed in the Hilbert-tenth-problem
research programme), after placement and before Parts I and II were
written. (This README, as written in batch 76, said that all shipped files
were byte-identical; that was not true of these two.) The delivered bytes
survive in the arrival archives. Delivered name → shipped name:

- Source 03: `code/van_kampen.py`, `code/verify.py` →
  `code/03-van-kampen-*.py`; `examples/commutator_budget_1.json`,
  `examples/grid_1_1.json`, `examples/grid_1_1_witness.json`,
  `verification/receipt.json`, `verification/render_check.json`,
  `verification/export_check.json`, `requirements.txt` →
  `data/03-van-kampen-*`; `SOURCES.md` → `03-van-kampen-SOURCES.md`;
  `arithmetic_van_kampen.tex` → the base of `article.tex` (Part I).
- Source 05: `build.sh`, `code/heisenberg_compiler.py`, `code/verify.py` →
  `code/05-three-phases-*`; `examples/*.json` and
  `verification_receipt.json` → `data/05-three-phases-*`.
- Source 06 (inner directory `order_is_not_a_moment/`): `Makefile`,
  `code/pair_geometry.py`, `code/verify.py` → `code/06-pair-order-*`;
  `data/canonical_c2_quartic.json`, `data/verification_receipt.json`,
  `data/worked_example.json` → `data/06-pair-order-*`; `article.tex` →
  Part III and Appendices H–I of `article.tex`.
- Source 07 (inner directory `Affine_Matrix_Diophantine_Research/`):
  `verify.py` → `code/07-affine-inputs-verify.py`; `verification.json` →
  `data/07-affine-inputs-verification.json`; `SOURCE_AUDIT.md` →
  `07-affine-inputs-SOURCE_AUDIT.md`; `article.tex` → Part IV of
  `article.tex`.

Not shipped: the manuscripts of sources 05, 06 and 07 (printed as Parts
II–IV), all four PDFs, all four delivered READMEs (this text and
`article.tex` replace them), source 03's checksum ledger `SHA256SUMS.txt`
(13 of 13 files verified at placement) and source 06's `SHA256SUMS` (9 of 9
verified at placement); sources 05 and 07 shipped none. They survive in the
archives of the arrival commits:

```sh
git show 6914ccca6:docs/incoming/arithmetic_van_kampen.zip > avk.zip
git show 6914ccca6:docs/incoming/three_commutative_phases_research.zip > tcp.zip
git show 808b53ed8:docs/incoming/Order_Is_Not_a_Moment.zip > oinm.zip
git show 48ee077c7:docs/incoming/ProveIt_Affine_Matrix_Diophantine_Research.zip > amdr.zip
```

No file of sources 06 and 07 was excluded as a heavy regenerable artifact
(the largest delivered file is source 07's 476,603-byte PDF).

## Labels and numbering

Every label carries the prefix `gts:`; the report has 324 labels.

- Batch 76 (189 labels): source 03's 89 labels are `gts:vk:` plus their
  delivered names, and source 05's 64 are `gts:tp:` plus theirs; no source
  label was dropped or renamed apart from the prefix. Source 05's three
  Heisenberg equation labels (`gts:tp:eq:Hmult`, `gts:tp:eq:Hinv`,
  `gts:tp:eq:Hpower`) sit on the common Section 1.2. The merge added 36
  labels: twelve `gts:` labels of the front section, the two Parts and the
  provenance appendix (`gts:sec:front`, `gts:sec:parts`, `gts:sec:heis`,
  `gts:eq:commutator`, `gts:sec:notation`, `gts:tab:notation`,
  `gts:sec:relation`, `gts:sec:status`, `gts:sec:questions`,
  `gts:part:vk`, `gts:part:tp`, `gts:app:provenance`); `gts:vk:q:*` on
  source 03's twelve research questions and `gts:tp:q:*` on source 05's nine
  research directions; `gts:vk:sec:problem`; `gts:tp:rem:credit`; and
  `gts:tp:app:sources`.
- Batch 78 (+135 labels; none of the 189 was renamed or removed): source
  06's 55 labels are `gts:po:` plus their delivered names, and source 07's
  69 are `gts:ai:` plus theirs. The write added eleven: `gts:part:po`,
  `gts:part:ai`, `gts:tab:letters78`, `gts:po:sec:literature`,
  `gts:po:sec:projection`, `gts:po:sec:software`, `gts:po:sec:questions`,
  `gts:po:app:names`, `gts:po:app:provenance`, `gts:ai:rem:subgroup` and
  `gts:ai:rem:binomial`.

Each Part keeps its source's numbering of statements, by section: source
03's Section *n* is Section *n* + 1 here (Sections 2–17); source 05's
Section *n* is Section *n* + 17 (Sections 18–31); source 06's Section *n* is
Section *n* + 31 (Sections 32–42); source 07's Section *n* is Section *n* +
42 (Sections 43–60). Theorem *n.m* moves with its section. The two
statements the batch-78 write added, Remarks 46.3 and 53.2, follow every
source statement of their sections, so no source number changed. Source
03's appendices A–C keep their letters; source 05's appendices A–C are
Appendices D–F; Appendix G is the provenance; source 06's appendices A and
B are Appendices H and I (placed after G so that A–G keep their letters);
source 07 has none. Text written at the batch-76 merge is marked `[write]`,
text written at the batch-78 write `[write 78]`; text without a marker is
the source's own.

## Setting and notation

All four sources use the integral Heisenberg group with the same
convention, `h(a,b,c)h(a',b',c') = h(a+a', b+b', c+c'+ab')`. Renamed
symbols (no normalization changed anywhere):

- source 03's group `H = Z^3`, `(x,y,z) = h(x,y,z)` → `𝖧`, because Part I
  also uses `H` for a height bound;
- source 06's matrix `H(α,β,γ)` and group `ℍ` → `h(α,β,γ)` and `𝖧`;
- source 07's interpolation coordinates `λ_i(t)` and vector `𝛌(t)` →
  `θ_i(t)` and `𝛉(t)`, because `λ` is Part II's coordinate `2c − ab`.

Source 07's `\cref` cross-references (33) are printed as "Lemma …",
"Section …" and so on; one proof step of source 06 called "the second
phase" is printed as "the second stage". Bibliography keys of sources 06
and 07 carry `po-` and `ai-`, with entries unchanged. Tables 1 and 2
(Section 1.3) list the letters used differently, among them:

- `A, B` — Part I: shear matrices (and `a⁻¹`, `b⁻¹` in software words);
  Part II: phase homomorphisms; Part III: letters of the alphabet; Part IV:
  `A = VBV⁻¹`, a shear `B`, a lattice basis `B`, `B(t) = binom(t,2)` (Part
  II's `𝔟(t)`).
- `T` — Part II: the third phase `T(r) = h(−r,−r,𝔟(r))`; Part III: doubled
  pair counts `T_ij`; Part IV: the pencil `T(t,s) = h(t,t,s)` and a hit set.
- `a, b, c` — Part II: coordinates of `h(a,b,c)`; Part III: letter
  multiplicities (Part II's `2c − ab` reads `2γ − αβ` there, never
  `2n_C − n_A n_B`).
- `λ`, `ℓ` — Part I: label indices; Part II: `λ = 2c − ab`; Part III: `ℓ =
  (2α, 2β, λ)` and sign-split witnesses `λ_j^±`; Part IV: `θ_i` (source
  `λ_i`).
- `L, U, D, K, P, N, E` and others — see Table 2.

Watch for these readings (Section 1.3):

- **Phase** (Part II) is one commuting factor of an ordered product of
  subgroups or submonoids — not a complex phase, a Fabius/Rvachev phase, or
  the "four-phase zero test" of `canonical-diophantine-certificates`
  Part XIII. Parts III and IV do not use the word.
- **History-free** (Part I's subtitle) means that no conjugator *word* is
  stored, only four chart integers. It is not the sense of
  `canonical-diophantine-certificates` Part XIV.
- **Compiler** is unrelated to the sparse-machine "universal compiler" with
  arithmetic-operation counts in the Hilbert-tenth-problem research notes;
  no operation record is claimed.
- **Slice**: Part I's Corollary 7.4 is a bounded-*area* slice; Part II's
  Corollary 20.3 is a *central* slice of `𝖧^N × Z^m`.
- **Moment** (Part III's title) is a gap-index sum `Σ(c−i)x_i`, not a
  probabilistic moment and not Part IV's moment curve `(t, t², …, t^k)`.
- **Pair count** (Part III) is the central coordinate of Part I's detector
  on a positive word, not a filling area.
- **Single-fold**: Part III over a complete pair profile, not over a
  projected target; Part IV over accepted inputs of languages already forced
  to be finite or periodic. Neither is a single-fold MRDP.
- **Exactly periodic** (Part IV) means a union of residue classes on all
  of `Z`; `Spec_c` (Part III) is a set of pair counts.

## Status: what is claimed, and what is not

The report claims conventional mathematical proofs, by its sources, for:

- **Part I (source 03).** Sanov's chart (classical; proof included): the
  free group on two letters is exactly the integral points of
  `x + t + 4xt − yz = 0`. A fixed-itinerary quartic with `8m − 4` witnesses
  and `5m` residuals, and an all-label area-budget quartic with
  `(2s+13)m − 4` witnesses and `(2s+11)m` residuals, whose zeros are in
  bijection with (padded) factorizations and which accept exactly the words
  of area at most `m`. A small-witness height bound (from the
  Cornulier–Tessera bounded-conjugator lemma, imported) and a
  primitive-recursive decision of bounded-area slices. The compiler's
  minimal allocated arity equals `(2s+13)·Area − 4`, and the Dehn function
  correspondingly; the computable-cutoff equivalence with the word problem
  (classical, reproved through the compiler). A proof-DAG quartic with
  `4p + 8h + 4j + 4h_c − 4` witnesses. For `[a^(2^k), b^(2^ℓ)]` in
  `⟨a,b | [a,b]⟩`: area `2^(k+ℓ)`, exactly `k+ℓ` product gates (optimal in the
  stated calculus), and an `8(k+ℓ) − 4`-witness quartic. An addition-chain
  sandwich for rectangular commutators; no computable sharing bound; infinite
  native fibres.
- **Part II (source 05).** An integral binomial normal form of quadratic
  maps; three injective phase homomorphisms into `𝖧^N × Z^m` whose ordered
  product realizes every integral quadratic system with an exact
  fibre bijection; central embeddings into a pure power `𝖧^(N+m)`; with
  MRDP, three fixed free abelian subgroups of `𝖧^d` with computably
  enumerable complete product membership, even on a central affine cyclic
  line (**proposed** negative answer to the three-subgroup question of
  König–Lohrey–Zetzsche, Remark 6.7, and Roman'kov); decidability of two
  commuting phases for integer, natural and mixed exponents; free
  commutative monoid versions; an explicit quartic reverse compiler with
  `2n + 2N` parameters; exact counting, weights and height bounds; no
  computable search bound; an explicit three-subgroup product in `𝖧 × Z`
  (from `F(x) = 6x² − 5x`) that is not closed in the profinite topology.
- **Part III (source 06).** For three letters with multiplicities `a, b, c`
  and pair counts `K_AC = p ≤ ac`, `K_BC = q ≤ bc`, the realizable values of
  `K_AB` form a gapless interval with explicit endpoints (Theorem 35.3).
  A six-equation quadratic certificate with `2c + 4` natural witnesses for
  each externally fixed `c` (Theorem 34.2); for `c = 2`, endpoints from four
  bilinear corner values (Theorem 36.2) and a canonical quartic with 24
  natural witnesses, 24 residuals and 297 monomials that has exactly one
  witness tuple on each accepted profile (Theorem 37.1). Four letters:
  spectra `{bj : 0 ≤ j ≤ ⌊n/2⌋}`, hence arbitrarily large holes and an
  integral hole in the convex hull (Theorem 38.1, Corollary 38.2). A lift to
  three generators of `𝖧^r` with `3r` added equations (Theorem 39.1), and
  decidable membership in a three-generator submonoid of `𝖧^r` when the
  multiplicity of one generator is supplied (Theorem 40.1).
- **Part IV (source 07).** For every entrywise affine unimodular curve
  `L(n) = C + nD` in `SL_d(Z)` and every subgroup `K`, the hit set
  `{n : L(n) ∈ K}` is finite (at most `k ≤ d − 1` elements, `k + 1` the
  nilpotency index of `C⁻¹D`) or exactly periodic (Theorem 46.1), with the
  free basis `I+N, …, I+kN` of the evaluation group (Theorem 45.2), the
  sharp period `P_k(e)` (Theorem 47.4) and every nonempty set of at most `k`
  integers realizable. Single-fold degree-`2k` certificates for these rigid
  languages given a lattice basis; no uniform algorithm (Proposition 50.1);
  a commuting-polynomial extension. With the repository's quadratic loader
  (reconstructed and attributed, Theorem 52.1), input degree two is the
  least degree that can load a noncomputable c.e. set, in every dimension
  (Corollary 52.2). A `6 × 6` jointly affine multiplication gadget (Theorem
  53.1) and an affine abelian compiler into `SL_{6g+2}(Z)` with `2g` unique
  added coordinates and a quartic certificate (Theorem 54.1); with MRDP,
  every c.e. relation through a fixed free-abelian unipotent subgroup
  (Corollary 54.2); one quantified coordinate is decidable in the
  block-cyclic form (Proposition 56.1).

**Credit for the two-phase theorem (Remark 23.2).** For
*integer* exponents, source 05's two-phase decidability is a special case of
known results, which source 05 does not cite for it: König, Lohrey and
Zetzsche, Remark 6.7 (a product of two subgroups of a polycyclic group is
profinitely closed, hence has decidable membership), and Roman'kov, J. Group
Theory 28 (2025) (the product of two subgroups membership problem is
decidable in every finitely generated nilpotent group of class two). What
source 05 adds: a direct, elementary decision procedure for commuting lists
through the integral logarithmic coordinate `λ = 2c − ab`, reducing
membership to one integer linear system; and the natural and mixed exponent
domains, i.e. ordered products of two finitely generated commutative
submonoids (or of such a submonoid and an abelian subgroup), which are not
subgroup products. No priority is claimed for the latter; the literature on
submonoid products beyond those two papers was not searched.

**Credit added at the batch-78 write.** Parikh matrices (Mateescu, Salomaa,
Salomaa and Yu, 2001), which source 06 cites only through Teh: for an
ordered binary alphabet the Parikh matrix is source 06's recording factor
`h(n_X, n_Y, K_XY)`, and its binary realization lemma is the description of
binary Parikh matrices; the ternary Parikh matrix does not record `K_AC`, so
the interval theorem concerns 2-binomial data. Source 07's curve `Q(n)` is
the curve (12) of the research note `group_unipotent_input_loaders.md`,
which source 07 does not cite.

The report does **not** claim:

- historical priority for any Part (all four sources say so); for Part
  II's main theorem, the placement check found no earlier resolution (the
  arXiv text of König–Lohrey–Zetzsche and the abstract of Roman'kov, which
  still states the three-subgroup case open), but that does not certify
  novelty, and Roman'kov's full paper was not read by source 05; source 07
  names the comparison with Leibman, Hu and Cahen–Chabert as its open
  priority audit;
- a finite-fold or single-fold Diophantine representation of c.e. sets or of
  group word problems; Part I's native fibres are generally infinite, Part
  II transfers fold bounds only conditionally (the four-square conversion can
  change multiplicities), Part III's canonical quartic is single-fold over a
  complete profile but not over a projected matrix target, and Part IV's
  added circuit coordinates are unique only given the source witnesses;
- a universal arithmetic-operation record, an improvement of the universal
  degree-four bound or of the repository's 87-operation benchmark, an
  optimized ambient dimension, an instantiated universal presentation,
  Higman subgroup, Roman'kov monoid, polynomial or matrix table;
- that its counts are minimal: they are the literal counts of the stated
  compilers; Part I's lower bound is a lower bound in its stated proof
  calculus, and Part IV's dimension `6g + 2` and its gadget are not claimed
  optimal;
- one fixed-arity polynomial: Part I's budget and circuit shape and Part
  III's separator count `c` are external data, and MRDP's fixed-arity
  polynomial preserves neither fibres nor the area ledger;
- that Part II answers the open question of the repository note
  `heisenberg_two_generator_membership.md` (do three generators of a
  Heisenberg *submonoid* suffice for undecidability?) — it does not; it
  concerns ordered products of three *subgroups*. **Part III answers it in
  part** (exact ternary word realizability; decidability with a supplied
  multiplicity), and leaves the unrestricted three-generator question open;
- that Part IV's classification is computable from subgroup generators (it
  proves that it is not, uniformly), or that its degree threshold bounds
  anything but the input degree of its stated interface; the degree-two
  half rests on the external effective Higman embedding (Mikaelian) through
  the repository construction it reconstructs;
- any Lean or Rocq verification. The finite checks illustrate; they do not
  prove.

## Relation to neighbouring reports and to the formal project

This is one of seven reports of the collection's `hilbert-tenth-problem`
category at this write, which are organized by substrate family; finitely
presented, nilpotent and matrix groups form this one.

- **[`probabilistic-quantum-and-continuous-computation`](../probabilistic-quantum-and-continuous-computation)**,
  Part VI (its sources 11 and 16; `pqc:dr:thm:main`): Mihailova's
  fibre-product compiler from finite presentations to rotation gates in
  `SO(4, Z[1/5])`, c.e.-complete membership of a fixed finitely generated
  subgroup, and quartic certificates for bounded *words*. Part I has the same
  input but certifies relator area and proof-DAG size in a free subgroup of
  `SL_2(Z)`; Part II has a statement of the same kind for a product of three
  abelian subgroups of a unitriangular group. Step 3 of Part IV's Theorem
  52.1 prints Mihailova's generators again (`pqc:dr:prop:mihailova`), as a
  marked second route with that pointer — the one re-proof of a
  neighbouring report's result in this report. The bounded-search argument
  of `pqc:qm:cor:nobound` recurs, for different statements, in Part I
  (Corollary 8.3, Theorem 13.2) and Part II (Proposition 27.1).
- **[`canonical-diophantine-certificates`](../canonical-diophantine-certificates)**:
  executions compiled to canonical arithmetic zeros. Part I's native compiler
  is explicitly not canonical; Part II compiles in the reverse direction.
  Its Part XIV uses "history-free" in another sense; its research-question
  remark on four-squares conversions is Part II's four-square caveat, also
  repeated by sources 06 and 07.
- **[`liveness-beyond-halting`](../liveness-beyond-halting)**: no overlap.
- **Within this report**: Part III's recording map is Part I's area detector
  applied to one pair of letters; Part III's logarithmic map carries Part
  II's `λ = 2c − ab` (the third derivation in the repository); Part II's
  three-subgroup theorem shows that Part IV's subgroup hypothesis is
  necessary, and answers the negative half of Part IV's question 9 for
  three-factor products (Remark 46.3); Part IV's cyclic test
  `⟨h(1,1,0)⟩` is Part II's binomial device in a different cyclic subgroup
  (Remark 53.2).
- **The Hilbert-tenth-problem research programme** (read-only for this
  report), `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`:
  `group_commutator_universal_substrate.md` (universal subgroup membership
  in `SL(4,Z)` along a fixed quadratic curve; Part IV's Theorem 52.1 is its
  attributed reconstruction); `group_unipotent_input_loaders.md` (a free
  pair in `SL_2(Z)` without an arithmetic image; Part IV reprints its curve
  (12) as `Q(n)`); `heisenberg_two_generator_membership.md` (the coordinate
  `2c − ab`; two-generator submonoids decidable; its three-generator
  question is not answered by Part II and is answered in part by Part III);
  `group_affine_input_obstruction.md` (the paired-SL₂ case, `k = 1`, of
  Part IV's rigidity theorem; that note and two others restrict the
  degree-two conclusion to SL₂–SL₄ interfaces, which after Part IV applies
  to the single-coset shape only); `group_complete_matrix_compiler.md`
  (does part of Part IV's question 10); the affine mortality notes (a
  different interface); `group_projective_label_aligned_lanes.md` (source
  03's own comparison).
- **Reviews of the batch-78 archives in that programme**, written before
  this placement: `incoming_substrate_review_808b53ed8.md` with
  `incoming_parallel_order_review_808b.md` (commit `126028588`, source 06)
  and `affine_matrix_square_projection_review808b.md` (commit `a1264b55c`,
  source 07). They found no mathematical defect and replayed both programs.
  They prove two reductions, printed in the article as dated `[write 78]`
  notes: source 06's quartic finalizer can leave eight sign-split products
  unsquared (289 monomials, eight fewer multiplications, nonnegative on the
  real orthant), or ten residuals (287 monomials, natural zeros only); and
  each square gate of source 07's compiler can drop one 3-dimensional block
  and one coordinate (dimension `6g − 3s + 2`; the worked example 20 → 17).
  The shipped files are the unreduced delivered ones.
- **The formal project.** The report sits in the collection, not in
  `Computability/HilbertTenthProblem`, and **placement beside a Lean/Rocq
  development confers no formal status**. Parts I, II and IV import MRDP only
  as a classical theorem (Part III does not use it); the project's formal
  endpoint is `Diophantine.mrdp`, `Diophantine.mrdp_iff` and
  `Diophantine.mrdp_dioph_iff`
  (`Computability/HilbertTenthProblem/Lean/Diophantine/MRDP.lean`, lines 33,
  42, 26), described by `Lean/MRDP.md` (cited by source 03) and
  `Lean/Diophantine/Common/MRDPCore.lean` (cited by sources 05 and 07);
  both files are unchanged from the sources' pins to the write. The project
  has formalized none of this report's statements: its Hilbert-tenth-problem
  Lean development has no free-group chart, Heisenberg-group, word
  pair-count, Dehn-function, subgroup-product or affine-matrix-curve
  module. The Lean module names in Part III's formalization route are
  suggestions.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

pdfLaTeX, in a scratch directory; standard packages (Latin Modern, AMS,
microtype, booktabs, longtable, enumitem, fancyhdr, needspace, listings,
TikZ, xurl, hyperref). The committed build has 123 pages: no undefined
references or citations, no multiply defined labels, no duplicate
destinations, no overfull boxes. The log has three underfull lines: badness
3118 in the `[write]` note on shipped file names at the start of Section 14
(present since batch 76), badness 1147 in the proof of Theorem 45.2 (source
07's text), and badness 2165 in the bibliography entry for Bogopolski and
Ventura.

## Rerunning the programs

All four verification programs depend on their delivered layout, and
several write into it. **Never run them in place.** Copy `code/` and
`data/` to a scratch directory and recreate the delivered layout there
(`py` is the Python launcher on this machine; the delivered texts say
`python` or `python3`). Run without `-O`: sources 06 and 07 rely on
assertions.

```sh
# source 03 (needs SymPy 1.14.0)
mkdir -p r03/code r03/examples r03/verification
cp code/03-van-kampen-van_kampen.py r03/code/van_kampen.py
cp code/03-van-kampen-verify.py r03/code/verify.py
cd r03
uv run --no-project --with sympy==1.14.0 python code/verify.py --receipt verification/receipt.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py budget 1 --relator abAB --output examples/commutator_budget_1.json
uv run --no-project --with sympy==1.14.0 python code/van_kampen.py grid 1 1 --output examples/grid_1_1.json
cd ..
# source 05 (standard library only)
mkdir -p r05/code r05/examples
cp code/05-three-phases-heisenberg_compiler.py r05/code/heisenberg_compiler.py
cp code/05-three-phases-verify.py r05/code/verify.py
cd r05 && py code/verify.py && cd ..   # writes r05/verification_receipt.json and r05/examples/*.json
# source 06 (standard library only)
mkdir -p r06/code r06/data
cp code/06-pair-order-pair_geometry.py r06/code/pair_geometry.py
cp code/06-pair-order-verify.py r06/code/verify.py
for f in canonical_c2_quartic verification_receipt worked_example; do cp data/06-pair-order-$f.json r06/data/$f.json; done
cd r06
py code/verify.py                                    # recomputes and compares with data/verification_receipt.json; never pass --write
py code/pair_geometry.py decide 3 2 2 1 4 > decide.json   # compare with data/worked_example.json
py code/pair_geometry.py export ../export06.json     # compare with data/canonical_c2_quartic.json
cd ..
# source 07 (standard library only)
mkdir -p r07
cp code/07-affine-inputs-verify.py r07/verify.py
cp data/07-affine-inputs-verification.json r07/verification.json
cd r07 && py verify.py --output verification.replayed.json && cd ..   # always pass --output
```

At the batch-76 write (Windows; `PYTHONUTF8=1`) sources 03 and 05 passed:
source 03's run (uv selected Python 3.13.5) reproduced the receipt and both
exported polynomials, and source 05's (Python 3.14.4) the receipt and all
six example files, each equal to the shipped file apart from line endings
(the Windows runs write CRLF; the shipped files are LF). That record does
not say whether the delivered or the `db3b377f0`-patched programs were run;
the message of `db3b377f0` reports that the patched programs pass both
author suites unchanged. The other three files of source 03 —
`grid_1_1_witness.json`, `render_check.json` and `export_check.json` — are
not written by any shipped program; the witness was rechecked at placement.
To compile a quadratic specification with source 05's compiler, run
`py code/heisenberg_compiler.py examples/multiplication_input.json out.json`
in `r05`.

At the batch-78 write (Python 3.14.4, `PYTHONUTF8=1`) the source 06 and 07
recipes above passed: source 06's verifier in 29 s (59 s at placement),
matching its receipt, including the SHA-256 of `pair_geometry.py`; the
`decide` output and the export equal `data/06-pair-order-worked_example.json`
and `data/06-pair-order-canonical_c2_quartic.json` as JSON; source 07's run
passed all 91,142 cases in about 5 s, and its output equals
`data/07-affine-inputs-verification.json` as JSON. Source 07's program never
compares with its receipt; compare the two files yourself, as above.

## Discrepancies and disclosures

- The shipped `code/05-three-phases-build.sh` keeps the delivered layout: it
  changes to its own directory (`code/`) and runs pdflatex three times on
  `article.tex`, which is not there; it would not build this report. Use the
  build command above.
- The shipped `code/06-pair-order-Makefile` also keeps the delivered layout.
  Its targets run `python3 code/verify.py`, write
  `data/canonical_c2_quartic.json` (`export`), build `article.tex` with
  latexmk (`pdf`) and run `latexmk -c` and `rm -rf code/__pycache__`
  (`clean`). Run from this directory it would build *this* report and look
  for delivered names; do not run it in place. `code/06-pair-order-verify.py
  --write` overwrites the receipt of its layout.
- `code/07-affine-inputs-verify.py` writes `verification.json` in the
  current directory unless `--output` is given (argparse default), which
  would overwrite a receipt of that name; its source README advised bare
  `python` on Windows.
- Source 03's `SOURCES.md` and the reproduction section of Part I (Section
  14.3) name delivered paths (`code/verify.py`, `verification/receipt.json`,
  `examples/*.json`, `requirements.txt`, `arithmetic_van_kampen.tex`), and
  Part I's software section names `verification/receipt.json` and
  `code/van_kampen.py`; Part II names `code/heisenberg_compiler.py`,
  `code/verify.py`, `examples/multiplication.json` and
  `multiplication_input.json`; Part III's software section (Section 41)
  names `code/pair_geometry.py`, `code/verify.py`, `data/*.json`,
  `README.md`, `Makefile` and `article.tex`/`article.pdf`; Part IV's
  (Section 58) names `verify.py`, `verification.json` and `SOURCE_AUDIT.md`.
  These are delivered names (map above); `[write]` and `[write 78]` notes at
  those places give the shipped names. `03-van-kampen-render_check.json`
  describes source 03's own 29-page PDF, which is not shipped.
  `07-affine-inputs-SOURCE_AUDIT.md` calls source 07's manuscript "the
  article"; it is Part IV here.
- Source 03's `SOURCES.md`, `07-affine-inputs-SOURCE_AUDIT.md` and all
  four sources' repository sections describe the repository at their pins
  (`c58206ca1`, `433df1be3`, `4cccfa068`). Every repository file they cite
  is unchanged from the pin to the write. None of them knew the related
  repository material listed above, and sources 06 and 07 could not know
  Parts I and II; the report adds it (Section 1.4 and the notes in the
  Parts).
- The bounded-conjugator lemma of Part I is imported from
  Cornulier–Tessera (Lemma 2.D.2), not proved; it is needed only for the
  height bound and the bounded search. Part II's description of Roman'kov's
  paper rests on its abstract (source 05 did not read the full paper); the
  report's credit sentences rest on the same abstract and on the arXiv text of
  König–Lohrey–Zetzsche. Part IV's degree-two upper bound imports the
  effective Higman embedding (Mikaelian, arXiv:2507.04347), not run or
  reproduced.
- The delivered title pages are replaced by one title page; each source's
  title, subtitle (where present), abstract and status statement open its
  Part verbatim. The author line "Research report/manuscript prepared for
  Vladimir Reshetnikov" is kept, with "AI-assisted" added.
