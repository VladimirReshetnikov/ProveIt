# Report 32 publication delta review — 2026-10-03

Result: PASS at the bounded publication-review scope below. No introduced mathematical, domain, count, collision, or fiber contradiction was found. This is a review of the publication delta and its correspondence with already reviewed source material, not a new universality proof or a new arithmetic compiler bound.

## Frozen objects

Publication commit: `134dfc0c8bd9ef385485d62f8165cfb3d166e811`. Its changes are the README, article TeX, and PDF under `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/`.

| Object | SHA-256 |
| --- | --- |
| Publication README.md | `78f643539bf121ea91a1d637556da2d5a5b6428fc0b3ccab6e9b353004c9bec9` |
| Publication article.tex | `817a257f696e2ee171ffd8436bf5db6d5e09eada28ece442e2e7643a5ea7974e` |
| Publication article.pdf, bytes only | `317de66a9a826e276b2560f2a56316fa97f7086747c7622335282a372707911f` |
| Original Report 32 ZIP | `b494c2b8e516d811cbecf305a748197af2a565882319a86586fec316c5ba8c47` |
| Original report32.tex | `8d2f7f93dad98bd5423681705597026114c8ee178b4fbb1e8ad4db20faff7fd0` |
| core/PROOF.md | `8764c608e380132e6e226c7e2f7754bf591579bdbea1162511179677a0663794` |
| paired/PROOF.md | `51fee9e3e720370fb235558215d8f045ce1ce0d0a6a338c4f51505a6e2330899` |
| fiber/PROOF.md | `4b6536ceab85593b6d8981e8461e9c1e8bb4bf0c9842a113c9aa7be38fc6f228` |
| core/loader-audit/U15_DEPENDENCY_AUDIT.md | `e8121b79d24eabb025bf74b144cc6517f084b26992b2b9c4b4ace47c62f070f5` |
| core/data/semigroup.json | `506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9` |
| Prior WIP review_incoming_matrix_grill.md | `14c0c3042558b212db8ee5885338f9a7af983d57a702f0c7af2b3d352a657cb8` |
| Prior WIP group_directed_semigroup193.md | `75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e` |

The ZIP path at arrival commit `db37d18c8687ca698be0ee59b7446fa5c18a8ebf` is `docs/incoming/Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip`. Its member prefix is `universal-matrix-report32-release-20261003/`. Source placement commit is `2f58ab4e92dea865e0b25a43925970cf92e9e324`.

The four proof/audit members and semigroup JSON listed above were freshly compared byte-for-byte with their placed `08-matrix-semigroup-*` copies. The original accepting-witness and accepting-94-ledger JSON files were likewise compared with their placed copies. WIP paths are relative to `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

## Correspondence and preserved boundaries

An inert text comparison found the original report's main body, from its first results section to its bibliography, identical to the new Part V main body after removing the added `\wtagc` editorial lines, undoing label/macro/citation-name changes, and normalizing whitespace. This exact comparison does not cover the appendices. The editorial additions were read separately for the claims considered here.

The publication correctly distinguishes the following interfaces.

* The 229 matrices are fixed directed positive-semigroup generators in `SL_4(Z)`. This is not the existing inverse-closed subgroup or projective-vector construction. The local reduction takes finite, blank-tailed U15 tape descriptions and produces a variable matrix target.
* The r.e.-completeness claim retains the effective published simulation-chain dependency. The downstream literal reduction is audited; this review does not independently reprove or implement the inherited arbitrary-machine-to-U15 compiler. The publication explicitly states this limitation.
* Encoding a finite tape of total length `n` costs `n+5` fixed `2 by 2` matrix products, with `O(n)` working bits and `O(n^2)` elementary bit work. This external encoder is not a paid ordinary-integer-input Diophantine loader.
* For numerical length `r`, the signed-target certificate has `130r` natural auxiliary variables and `17r+4` squared residuals. Degree is two at `r=0` and four for `r>=1`. The alternative natural external signed-pair interface retains the auxiliary count, adds four residuals, and has degree four also at zero length. Naturality is essential; the theorem is not promoted to arbitrary integer or real witnesses.
* The union over all lengths has growing arity. Canonical witnesses for a chosen sequence do not imply a unique witness for a target. Copy stutters give infinitely many witnesses across lengths for every accepted encoded target; each fixed-length fiber is finite.
* The exact rational fiber generating function is stated for halting live inputs and counts factorization words, equivalently tile sequences or canonical roots, not distinct resulting matrices. It is not a halting algorithm or a fixed-arity finite-fold representation.
* The 197- and 193-generator successor summaries match the prior directed-semigroup reports. The 193 construction has 91 rules and 96 tiles, and its accepting example uses 12 rewrites, 83 tiles, and 167 generator factors. Its maximum coefficient size is 31 bits and total magnitude-bit census is 19,321. These are generator/source statistics, not universal arithmetic-gate bounds.

Useful article locations at the pinned publication: lines 304–305 and 373–379 state the principal interface limits; lines 4269–4280 identify provenance and inherited universality; lines 4360–4397 state the finite-tape dependency; lines 4668–4683 distinguish witness domains; lines 4748–4770 charge the external encoder and generic evaluator; lines 4831–4855 describe the example and collisions; lines 4875 onward separate unbounded fibers from fixed-length finiteness; line 5046 summarizes the successors.

## Fresh bounded checks

No archive Python or predecessor builder was executed. Fresh standard-library data calculations independently recounted 229 literal matrices, 3,664 entry slots, 1,831 nonzero entries, 21,372 magnitude bits in total, and maximum absolute coefficient 63,038,000.

Generic integer matrix multiplication checked both displayed length-two collisions: `(20,109)` versus `(110,20)`, and the added editorial pair `(20,111)` versus `(112,20)`. Their upper targets respectively are

```
[[22474169, 568874], [-892774960, -22598231]]
[[20176021, 510698], [-801482200, -20287219]]
```

The lower blocks agree with the required fixed block. The second pair is exactly the bit-one analogue of the first: both tile sequences have upper word `XX` and lower word `X1X`. This review did not rerun the exhaustive 12,996-product census; that census remains inherited evidence from the existing audit.

The reported generic evaluator formulas were independently recomputed from its declared monomial ledger and charging convention. For `r>=1` they are `M=11246r-9036`, `A=3804r-2700`. At `r=94`, these give 12,220 auxiliaries, 1,602 residuals, 1,048,088 multiplications, and 354,876 additions, agreeing with the saved ledger and publication. These are exact charges for the deliberately unoptimized evaluator, not lower bounds.

For the stated halting example, the fiber denominator weights are `2,4,5,6,7,8,8,9,9,10,10,10,10,10,10`. A fresh small coefficient computation gave `1,0,1,0,2,1,3,2,6,5,14,7,19`, matching the printed initial coefficients after the leading `z^94` shift. The product of weights times `14!` is `759246199455744000000000`, matching the leading asymptotic denominator. The proof's unique separator blocks, one-marker restriction, cleanup interleavings, and insertion of copy loops support the stated counting scope.

## Limits of this review

The PDF was hashed but not rendered or rebuilt. No full manuscript certification, fresh external literature audit, exhaustive collision census, historical compiler replay, full arbitrary-length certificate-generator audit, or expansion of the complete quasipolynomial was undertaken. Existing source reviews supply those inherited implementation claims to the extent explicitly stated there. The publication makes no new complete ordinary-input universal Diophantine operation bound, and this review establishes none.
