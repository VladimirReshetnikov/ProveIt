# Scoped review of the reciprocal five-particle notes

Result: PASS for the added prose and the specific cross-references checked below. No introduced arithmetic or domain contradiction was found. No new complete ordinary-input Diophantine bound follows from this editorial change.

## Revision and coverage

The reviewed revision is **0f95145cb65d5dc279e2053e8707a71bb490bb59**, “Write batch 82 (reciprocal notes): five-particle bounds and sources into SMC, and pointers in QOC, STE, FPB, FUP and CDC”. All added or replacement text in its twelve README/article.tex diffs was read, including historical-status corrections, the reciprocal references and reproduction/build prose. The six changed PDFs were not rendered or rebuilt. Build-success claims are inherited records, not freshly reproduced here.

All line references below refer to that revision. The evidence pins are obtained from its Git blobs, **not from the later working tree**; in particular this review does not absorb the overlapping edits in 8c5831d55. Context reads are distinguished from the changed prose. No predecessor, archive or publication Python was executed, and no repository file was changed.

Abbreviations below mean the corresponding report directory under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/`: SMC = signal-machine-collision-certificates, FPB = five-particle-binary-automata, QOC = quadratic-orthant-certificates, FUP = fixed-universal-polynomials, CDC = canonical-diophantine-certificates, STE = stochastic-and-thermal-exactness.

## Checked claims and their boundaries

1. **Five is the stated one-dimensional threshold, under the inherited compiler proofs.** The SMC additions at article.tex:4890–4893, :5367–5370 and README.md:1710–1729 correctly combine FPB Reports 14/15 with the mass-at-most-four lower theorem. Context FPB article.tex:1332–1347 and :2159–2174 limits the assertion to fixed finite-radius rules and finite zero-background inputs, with the specified halt-pattern or computably supplied exact-target convention. SMC article.tex:5991–6019 requires a finite positively weighted alphabet, unique vacuum, and at most one weight-one symbol. The binary case satisfies these assumptions and supplies the claimed reversible integer-state upper bound. This is not radius-one or intrinsic universality, nor an input-independent exact-target theorem. The all-dimensional upper-bound paragraph retains Reports 16/26 as dependencies (SMC :578–583). The earlier open statements are dated historical statements with explicit later updates. A parallel bounded cross-read by Aristotle independently confirmed these threshold and interface distinctions; it did not recertify the entire inherited CA construction.

2. **Literal source completion is not a three-mass rule completion.** Report 16's 122,622 controls and 141,561 rows match the source/intake context. Its global partial injection applies on the primitive natural counter interface, while clean-loader universality and nonblocking have their stated initialization promise. FPB :2728–2777 distinguishes that source from an allocated downstream CA truth table. The new SMC notes explicitly say that the guarded source answers the source question only in part: it does not print the separated three-mass pulse alphabet/local rule. Neither those counts nor five-particle universality discharge an ordinary-input loader or an unbounded fixed-arity Diophantine history obligation.

3. **The horizon and domain accounting is consistent.** QOC :4749 points to FPB's 8,408-row source certificate. FPB :2197–2205 and :2275–2287 explicitly fix a syntactic source-instruction horizon h and give h(B+2) witnesses and h(4+z)+1 squared residual slots, yielding 10,750h and 2,344h+1. These are not paid gate counts. The optional physical-clock row adds one square and, if time is a witness, one coordinate (:2313–2326). The nonnegative-real variant requires one selector-norm residual **per layer** (:2372 onward), hence h extra squares; the displayed natural core count must not be read as already including them. The new phrase “paid norm row” is consistent with this contextual accounting. The source loader still contains explicit exponential encoding, and existentially varying h does not convert this family into one fixed-arity polynomial. “Weaker” here compares the quartic degree to the referenced quadratic theorem, not a claim that every resource count is larger.

4. **The canonical quartic pointers retain the correct quantifiers.** CDC's addition points to SMC :9934–10010: a fixed promised rule and fixed mass-at-most-four input, stationary-frame visited sites, signed external site coordinates, and natural witnesses. “One witness” means one complete tuple, not one variable. The direct clause construction gives B+I+2C witnesses; a shared cycle coordinate and two residuals enforce first-arrival time. The original-frame extension at SMC :10080–10092 concerns complete configuration targets via orbit injectivity; it does not establish original-frame first hits for arbitrary sites or patterns. No real/rational-witness, uniform-over-input arity, or generic single-fold MRDP theorem is claimed. This agrees with the pinned intake and fixture notes listed below.

5. **The reciprocal matrix and Pell references do not import stronger conclusions.** FPB/FUP/QOC/STE refer to Report 32's fixed directed semigroup and variable matrix target, with finite U15 tape input and inherited Neary–Woods universality. The FUP reference is for input hardness, expressly not a use of its conditional universal polynomial theorem. This matches the existing matrix publication review. The table/frontend byte-identity and the `(u10,b)` transcription discrepancy are inherited source-audit claims; this bounded review did not freshly reconstruct the 528-row compiler or compare all serialized table bytes. FPB/FUP's infinite-fiber pointer matches SMC :9256–9295: from one positive seed, a congruence-preserving Pell power gives infinitely many positive native extensions at fixed scale. It does not make the outer predicate nonempty, prove finite-foldness, or supply a new costed universal source.

## Arithmetic opportunities, without promotion

The most concrete reusable algebra in these references is already explicit: the inactive-chart product `(E-e_i) Z_i` forces all inactive private natural coordinates to zero, and constant-term lifting avoids multiplying an entire quadratic output by a selector (SMC :6860–6891). Signed private coordinates would invalidate the nonnegative-sum argument. A second useful mechanism is the shared cycle N in :9992–10010: common clock cN²+bN plus selected affine offsets replaces branch-private clocks with one coordinate and two quadratic residuals. Both mechanisms merit literal circuit comparisons in suitable finite chart compilers; neither changes the current universal 84-operation result. They are already recognized in the existing fixed-input first-hit work, including its 35-operation example, so this review claims no new saving or discovery.

In particular, no new proof here removes the unbounded history encoding, pays the original-program ordinary-input loader, freezes the missing three-mass simulation interface, or makes a horizon-dependent certificate fixed-arity. Particle counts, source row counts, residual counts and arithmetic gate counts remain different resources.

## Exact reviewed text pins

All paths in this table are relative to the report directory prefix above. SHA-256 hashes cover the complete file at the reviewed commit, not only the changed lines.

| File | SHA-256 at 0f95145cb |
|---|---|
| `canonical-diophantine-certificates/README.md` | `cd1d823dbb5f2ae27ca2aff9b1aa397f1354d06ddb20e4aac9fecbf86aa28256` |
| `canonical-diophantine-certificates/article.tex` | `2f148d1d17c8449283baa2118ed5203a51d870a346affa8cd58430fdf747ce3a` |
| `five-particle-binary-automata/README.md` | `512fc3eb4de2729279d8363ae455ba91bbbccc498e4ce94f87740b486fcd35e4` |
| `five-particle-binary-automata/article.tex` | `cfc5cec4299f2fa926b6f9eae41fab9af1ec4ba4235e15aed5ff34e063d458f9` |
| `fixed-universal-polynomials/README.md` | `1dc77bd29642ffbd5c3c900ff35ae291bf30428ed7be81632db3b3000d9807f0` |
| `fixed-universal-polynomials/article.tex` | `c68b7a9548a7796ffb3978621616ffb3d7b90ad752280197d768de3973324cff` |
| `quadratic-orthant-certificates/README.md` | `26c179059517b34842cd5dc9220bad2df57a0e23eaddce228a83876835dc83a3` |
| `quadratic-orthant-certificates/article.tex` | `514b43e57fc01d83208ef00da5804138d794f5e1594895aafe04ce4b0fc2e5dc` |
| `signal-machine-collision-certificates/README.md` | `4cb2614b54e4bac05c2a9045d4041f18fcc65a3878c44f4ef47d8110129e15af` |
| `signal-machine-collision-certificates/article.tex` | `17d3c0d9b449c689f88c1dc082ffee9b116993e4f5585b65d52c4fe591b2d962` |
| `stochastic-and-thermal-exactness/README.md` | `3eb35d1a160b713d37512bc32c3d0d100888fe44a258d7402c8d6e6c573a8f39` |
| `stochastic-and-thermal-exactness/article.tex` | `a9b43c4871fd2b4df0901acc92d5754e83278aa01633eb0f506f0cc566138ab7` |

## Pinned context, not additional publication-delta coverage

The theorem passages cited above are inside the pinned article files. The following previously reviewed WIP notes were used for their stated interface/implementation boundaries, not rerun or promoted to broader audits. Paths are relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/` and hashes again refer to the reviewed commit.

| Context note | SHA-256 |
|---|---|
| `review_literal_universal_reversible_source16.md` | `c26ce5b15dc7b7da80de7a9a13f3ed39745ef533e026b5f2037da95ff38c41ce` |
| `review_parallel_particle_reports.md` | `46990e5e8787dcc3d808d01e65c3e2b2bc7b815ce5d950b7424c96efe3cbca93` |
| `review_matrix32_publication_20261003.md` | `37837e904564bef88c772456c426538a15bcd0774ae2acef4d33376605fea2fe` |
| `review_original_frame_first_hit30_intake.md` | `96d0e1fef873ea4d2ef8fcf8139fb047a52b4535786e7860183de882b27c33a6` |
| `original_frame_first_hit30_fixture.md` | `8e9f78d88c3d87ea403e4c749bea1ddfb5582fdc6b1c23ae2fe7c29f587662a7` |

This is a prose/scope and selected formula review. It is not a fresh primary-literature review, full proof recertification of six manuscripts, CA implementation audit, table regeneration, or PDF/build verification. No correction is requested within the checked scope.
