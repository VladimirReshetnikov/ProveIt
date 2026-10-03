# Conservative-signal and sparse-lattice typesetting transfer

The transfer of the corrected signal and sparse-lattice manuscripts into Parts III–IV passes this bounded audit, with **one new abstract qualification to repair**. The original mathematical statements, displayed and inline formulas, source labels and companion bytes are preserved. The detailed new scope passages correctly separate physical universality, finite-horizon certificates, natural-domain projections and low-mass decidability.

The review is pinned to `bd8a8afd67108107c1fe443e488b84ef05236d78`, parent `ae7c1e6aae3dc58c9c638b35646865ad6c10387d`. It concerns only this integration and its new editorial comparisons. It is not a renewed proof review of Parts I–II, an unchanged-code replay or a review of a later commit. The [portable checker](review_signal_typesetting_bd8a8afd6.py), [receipt](review_signal_typesetting_bd8a8afd6.json) and [narrow patch](signal_typesetting_bd8a8afd6_partial_map.patch) use only pinned source objects and private temporary copies.

## Source preservation, with multiplicities

The checker authenticates both retained archives from the parent of their placement commit and all 94 members:

| Source | Archive SHA-256 | Members |
|---|---|---:|
| Corrected conservative signals | `e2acf725fcf017e14b2705cc9097fa9e3eb8b02c2fc9faf8ce486d3614816990` | 45 |
| Sparse lattice certificates | `90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68` | 49 |

Their article inputs are expanded in the delivered order, including the signal machine's separate Morita table and all five sparse-lattice chapter files. Mathematical block matching is restricted to Part III and its Appendices F–H for the signal source, and Part IV for the sparse source. Every source occurrence consumes a **distinct target occurrence in source order**; repeated formulas cannot satisfy multiple source occurrences by set membership or dictionary replacement.

| Source | Formal statement/proof blocks | Displayed formulas | Inline formulas | Preserved labels |
|---|---:|---:|---:|---:|
| Corrected signals | 11 | 46 | 452 | 49 |
| Sparse lattices | 12 | 60 | 497 | 53 |

All match. The formal blocks include the seven signal statements and four proofs, and eight sparse statements and four proofs. These are counts of named LaTeX environments; prose arguments outside those environments are not miscounted as additional formal proof blocks. Formula counts overlap the formal-block coverage and are not independent mathematical results.

Normalization is explicit: strip comments and whitespace, remove label declarations, remove the new source-label prefixes, rename the natural-number macro `\N` to `\NN`, and apply the two documented bibliography-key renamings. It changes no mathematical operator, coefficient, variable, quantifier or condition. The receipt records each source occurrence's normalized hash and distinct target occurrence/line. Regression cases reject an omitted duplicate and reversed order; a genuine repeated-occurrence positive control passes.

The source-aware placement manifest also verifies all **71 distinct companion files** at this commit against their archive bytes: 36 signal files and 35 sparse files. These correspond to 73 original member identities because each package had one duplicate-content member shipped once. This is not an unqualified cross-package hash match. The commit changes only `README.md`, `article.tex` and `article.pdf`; no computational source or data export changed.

The TeX SHA-256 is `74a15d44a7cd23d1ffe813bb6d70bd61986bc93a43615504176c2f756505f239`, README `ebe0ba2754003afb46f8771399e420c5594edb5f9b1bb605a44b4719ec250201`, and PDF `fe5e275afec2f381801a403538bae36efd8cfcd119cee69478e2733b14b55b8a`. PDF metadata reports 119 pages. No PDF build or rendered-layout verification was performed.

## Required abstract qualification

The new master abstract at `article.tex:98` describes the event dynamics as an “18-dimensional integer-linear map.” The source theorem and the new detailed description at line 278 correctly say **partial piecewise homogeneous integer-linear map**. Different modes and canonical pivots select different guarded matrices; the construction is not one global linear transformation.

The patch restores exactly those missing qualifiers in the master abstract. It leaves the fixed-horizon sentence and all source theorems unchanged. The checker applies it to a private copy and verifies the resulting TeX SHA-256 `dab5a33e516c2869fcf7c695295c73e6bef608fdebd2e942e1267dbd1f850df5`. The copied README and PDF remain byte-identical. **Applying the text patch requires rebuilding `article.pdf`.** This is a presentation correction, not a defect in the imported event theorem or compiler.

## Physical universality and the finite polynomial family

I read the newly added master summary, Part III preface and marked comparisons, the updated question answers, both release/review summaries and the README's new scope/reproduction passages. The detailed text retains the necessary limitations:

- Part III supplies the literal 18-live-signal machine with 114 labels and 445 injective two-to-two rules. The ten-live binary machine is an existence construction, not a supplied literal table. Accepting and null terminal pairs remain distinct, and undefined encounters are forbidden.
- The source's eventually blank finite-support tape convention is retained. The loader constructs two exact rational distances from a prepared tape. Its cost is linear in that prepared word length in the stated arithmetic model; ordinary binary input still needs the separately identified digit extraction, recoding and base conversion. The physical finite-input interface is useful but does not itself pay that ordinary-input compiler.
- There are 49,700 modes and 80,501 candidate branches in the emitted closure. This finite mode graph overapproximates geometric reachability and does not bound universal runtime or make every graph path realizable.
- The one-step packet is an ordinary quadratic polynomial. Its concatenation has an externally fixed event horizon; the witness count grows as `4,197,016K−18`. Quantifying over the union of all horizons does not give one fixed-arity polynomial.
- Scaling a rational seed to integers changes its physical scale. The pivot-scaled lift and the uniform common-denominator lift are properly distinguished. The nonaccumulation claim is for encoded runs; it does not reinterpret arbitrary malformed configurations or accumulation points.

The new comparisons to the one-batch endpoint argument and common-denominator devices are appropriately limited. The introduced germ condition is explicitly acknowledged: a post-event cut can have zero gaps between separating outputs. The relation to the earlier universal-frontend question is also qualified by the different universal machine and the unpaid ordinary-integer loader.

The actual step polynomial has squared affine terms and complementarity products whose affine factors have nonnegative coefficients. Its nonnegativity on the real orthant is therefore correct, but the text does not infer that its real zeros are natural. The one-step graph is a finite union of rational linear conditions over natural integers, hence is Presburger/semilinear. The cited CDC single-fold quadratic theorem and the QOC polynomial format have the claimed interfaces. I read those specific statements and the PQC finite-trace theorem, rather than re-auditing those large reports. The named Lean Presburger declarations exist, but no Lean build or whole-development audit was performed.

For the new classical credit, Balas's [author-written account](https://lara.epfl.ch/w/_media/projects/disjunctive_programming.pdf), page 284, explicitly presents the disaggregated variables and sum-one weights behind the convex-hull extended formulation, and explains the 1979/1985 publication distinction. The [Jeroslow–Lowe publisher record](https://link.springer.com/chapter/10.1007/BFb0121015) confirms the stated mixed-integer representability subject and bibliographic data. This supports the background attribution of the selector/copy mechanism. The signal packet's natural selectors and complementarity constraints are still what enforce its own exact, unique witness; no convex-hull relaxation is used as an exact chronology certificate. I did not obtain and independently re-prove the complete Jeroslow–Lowe paper, reauthenticate Morita's unavailable table visually, or conduct a priority search.

## Natural guard projection and arithmetic accounting

The new note at `article.tex:3001` and README lines 608–613 faithfully reports the independently reviewed guard projection. Retain the positive pivot gap, mode equality, all selected-edge tie equations, and unselected first-event strict forms for nonnegative closing speeds. Delete all germ rows, the span row, and the automatically positive first-event forms for negative closing speeds.

On complete natural zeros, a selected tie forces a positive gap, retained strict rows force the remaining nonnegative-speed gaps positive, and negative-speed first-event forms are positive from natural gaps and a positive pivot. Deleted strict forms are integral, so positivity means at least one. Their slack restoration `s=L(copy)−selector` is therefore natural and unique; inactive copies restore zero slacks. This establishes the claimed bijection after dropping/restoring coordinates, not equality of polynomials on unchanged coordinates. The real-domain exception remains explicit: a strictly positive fractional gap need not restore a nonnegative unit-offset slack.

The checked arithmetic is exact:

```
18 · 80,501 = 1,449,018 deleted rows and slacks,
4,196,998 − 1,449,018 = 2,747,980 witnesses,
2,762,961 − 1,449,018 = 1,313,943 squared rows,
25,392,522 − 17,903,098 = 7,489,424 saved operations.
```

The 80,501 complementarity products remain. The savings concern the explicit sparse-affine evaluation schedule of this enormous one-step family. The typeset note does not present them as a global optimum, a change to the imported theorem, an unbounded-history representation or an improvement of the universal 87-operation bound.

The corrected signal evaluator is accurately described as already patched. Its companion bytes match the corrected archive. The earlier defects, three correction modes and prior author replays are reported as prior review evidence; none was rerun here.

## Sparse-lattice editorial scope

A second reader independently checked every new Part IV marked paragraph and the relevant front matter/README against the complete sparse review, projection proof and specifically cited CDC statements. That bounded read found no further actionable issue. Its separate [review note](review_signal_typesetting_sparse_editorial.md) has SHA-256 `1ec66f9ebb8c78e466ef4a07375df0f97bc6110f868136db17aa5daee4d0ac12`; its [source-pin record](review_signal_typesetting_sparse_editorial.json) has SHA-256 `5b64e908cdcafcd1242e5a72a7ab8c22a7a116f8e99acb817a5c34abe9a07f5c`. These are separately pinned supporting review artifacts, not runtime dependencies of the portable checker.

The resource distinctions remain accurate. A unit-record certificate pays the numerical conserved mass `M`, not just support cardinality or binary mass length. Large gaps are numerical coordinates, not omitted unknown dynamics. Horizon `T` is external. The two free initial counter positions in the paid loader are not an ordinary binary program/data decoder.

The bounded-diameter result decides an orbit promised to stay within the bound, including its translated periodic tail. Escape from a chosen bound is not rejection of unrestricted later reachability. The mass-at-most-two result assumes the stated positive weights and unique zero-weight vacuum; it is a fixed-rule decision/semilinearity theorem. It neither proves that three particles suffice nor identifies a least universal mass. The text keeps the binary-coordinate complexity claim distinct from semilinearity of numerical coordinates. The safe universal source remains an existence construction; the fully specified doubling example is nonuniversal. The pulse observer is an anchored event, not global halting or exact-target undecidability.

The prior constructor defect is disclosed correctly at `article.tex:3680` and README lines 614–619: the low-level sparse `Poly` repair is **not applied** to the shipped original producer. The high-level valid-source theorem is not confused with a repaired hostile-input constructor contract. The later projection is accurately reported as reducing the default row-selector core to

```
V = T[M(S+7)+4M(M−1)],
R = T[10M+4M(M−1)].
```

It preserves quadratic residuals and natural zeros but does not establish an arithmetic-gate saving; optional endpoint, orthant, loader and observer costs remain separate. The five-witness congruence comparison similarly changes a witness count within the fixed post-elimination compiler. This pinned integration predates the separate existential 15/14-operation tradeoff and makes no claim about it.

## Reproduction and limits

```
python review_signal_typesetting_bd8a8afd6.py \
  --repo /path/to/Proofs \
  --patch signal_typesetting_bd8a8afd6_partial_map.patch \
  --expect review_signal_typesetting_bd8a8afd6.json
```

The helper reads Git blobs, authenticates ZIP members without executing or extracting their code, performs the occurrence-preserving census, checks source-aware placement and the displayed arithmetic, and privately applies the text patch. It compares saved receipts with recursive exact-type equality. Its deterministic receipt contains no wall-clock or host-version normalization.

No report module or unchanged author suite was run; no repository, archive or canonical PDF was modified. In particular I did not attempt to reproduce the README's reported Windows-specific stager/newline failure or its typesetter's compilation log. Those are disclosed execution observations, not mathematical premises of the transfer. The root's earlier POSIX placement/replay evidence and the typesetter's Windows report are not conflated. No future commit is included in this result.

Root independently read the qualifier repair, helper and source theorem, then reproduced the exact saved receipt. This fresh replay included the private patch application and unchanged README/PDF checks. The separate sparse editorial note and source-pin record were also read; unchanged author suites were not rerun.
