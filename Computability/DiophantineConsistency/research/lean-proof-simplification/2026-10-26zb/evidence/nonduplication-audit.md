# Exclusion audit for the next Lean simplification report

## Snapshot and scope

Repository: `VladimirReshetnikov/ProveIt`.

Pinned source and exclusion-corpus commit: `29936089835c0c55cca81edc86b4fb0c70ce34d5`.

The two user-specified locations contain **21 placed proof-simplification packets**,
`2026-10-26a` through `2026-10-26u`. The incoming directory at this commit contains
only its README. Its first table explicitly records that all twenty-one archives
were retired into the research directory. In particular, the three archives found
in an earlier API response are now packets **s**, **t**, and **u**; they must be
included in the baseline rather than treated as absent because the ZIPs moved.

Authoritative index locations:

- `Computability/DiophantineConsistency/research/lean-proof-simplification/README.md`, packet table.
- `docs/incoming/README.md`, lines 15-46, the twenty-one-packet retirement table.
- `Computability/DiophantineConsistency/research/lean-proof-simplification/ADOPTION.md`, adoption ledger.

The manifest records **1,143 files**, **35,059,944 bytes**, under the two roots.
This is a byte inventory, not a count of independent recommendations: it includes
PDFs, compiler receipts, omitted-source ledgers, proposals, and duplicate snapshots.
The primary-report index identifies the 21 manuscripts, their section files,
section headings with source line numbers, and their SHA-256 hashes.

No original submission program or proof script was run for this audit. Current
validation of new candidates belongs to the research agents' separate receipts.

## Novelty standard

Every old idea is part of the assumed baseline, including optional, uncompiled,
deferred, rejected-default, and notes-only ideas. The adoption record is useful
historical evidence but cannot make an old proposal new. A different implementation
of an old advertised interface is not counted as a new simplification.

The review used the main manuscripts and section headings, their detailed source
notes, and existing exclusion ledgers as an index. Candidate-specific checks were
then made against the actual report, proposal, patch, and note text. Bundled
unchanged source copies and compiler metadata were distinguished from proposed
changes. A source filename appearing only in an old snapshot does not establish
that a simplification of that source was already proposed.

This is a scoped nonduplication audit of the requested corpus. It is not a claim
that no similar mathematics appears in Mathlib or in the general literature.
The large incoming README also references old K215 and equation-construction
reports outside the specified roots. Its visible proof-engineering summaries were
screened, but this audit does not claim to reread every transitively linked retired
manuscript from unrelated projects.

## Broad exclusion taxonomy

The machine-readable ledger has **120 entries**. Its first 98 preserve packet u's
explicit mechanism taxonomy, with exact line anchors and a map from its historical
archive labels to the current placed packet names. The remaining 22 add mechanisms
from p-u that were outside that earlier ledger. Some entries overlap; 120 is a
ledger count, not a claim of 120 pairwise independent ideas.

| Family | Exclude as already proposed | Representative primary evidence |
| --- | --- | --- |
| Primitive recursion and scanners | Recursor congruence, shared iterator laws, encoded-list simulation, supplied-program preservation, exact Boolean outputs, tag dispatch | a `report.tex` sections 3 and 8; b sections 5-6; g section 4; h scanner section |
| Histories and proof fragments | Validated folds, append/invariant laws, separate row/stored types, arbitrary-arity certified fragments, rule-schedule syntax with two interpretations | b `report.tex:284-395`; p `report.tex:192-245`; r `report.tex:560-648` |
| Decoders and codecs | Successful Option inversion, fused quotation/depth graph, raw-parent total decoding, exact standard-library list-codec bridge | h decoder section; i `report.tex:182-220`; j `report.tex:123-167`; n section 03; t section 02 |
| Representation layout | Assignment naturality, renaming outside evaluation, finite witness splitting, early projection/count laws, inverse pairing graphs and canonical witnesses | a assignment patch; b witness-layout section; k `report.tex:253-413`; p `report.tex:326-363` |
| Circuit proof schemas | Existing power certificates, local indexed node equations, shared topological invariant, commutative simulations, append invariants, semantic cuts and common 99-node tail | a-c generated and compiler sections; f section 04 |
| Polynomial syntax | Finite residual sums, degree/cost interfaces, cancellation-aware normal forms, sparse row reflection, row operations preserving zero sets | a-c compiler sections; h residual section |
| Coefficients and support | Common coefficient majorants and naturality, support envelope, finite pushforward/fiber sums, injective sparse placement, exact local pair-fiber coefficient theorem | c coefficient section; d finite-fiber section; i `report.tex:250-281`; t section 03 and mixed-product prototype |
| Carries and cyclic words | Half-radix arithmetic, exact natural local quotient/remainder facts, derived carry recurrence, origin no-borrow decrement, fixed-point uniqueness, explicit extremal cyclic carries | a/b digit sections; i `report.tex:348-394`; j `report.tex:406-506` |
| Cyclic algebra and geometry | Aligned-cell equivalence, physical field residue API, rotation as point-mass convolution, cyclic packing as monoid-algebra homomorphism, quotient support separation | b native geometry; i `report.tex:283-307`; j `evidence/algebra_review.md`; p `report.tex:283-324` |
| Pell arithmetic | Exact-root rational descent, unit product decomposition, signed congruence relation, parity reuse, small-ordinate fundamentality, base monotonicity, negative-norm obstruction via positive units | i-m arithmetic sections; q `report/new-proof-simplifications.tex:139-215` |
| Pell approximation | Parameterized positive scale/error allowance, natural perturbation and power sandwich, exact binomial quotient rounding, two-budget integer recovery | p section A; r sections 3-4; s sections 3-4; u section 2 |
| Object-model proofs | Definable induction wrapper, all-model sealing, arity transport, internal constructor views, unique existence and recursive graph fusion, vacuous induction removal | a-c object sections; j sections 4-5; l Idea 1; q section 2 |
| Object-formula and certificate algebra | Compositional satisfaction normalization and semantic folds; monotone local certificate empty/union/insertion closure, observed pair/triple adapters | s `report.tex:177-289,443-516`; q `report/new-proof-simplifications.tex:317-376` |
| Native source interfaces | Coherent source/window extraction, named conjunction facts, nine-coordinate packaging, lower base import layer, natural/integer rank conversion | b/f source-interface sections |
| Native source rank | Stronger magnitude envelope `(2*q-1)*(q^2-1) <= rank`, yielding rank at least 40 and above `3*q` under the positive source assumptions | u `report.tex:198-268` |
| Wang row geometry | Exact high-color fibers, selected-index characterization, first failure with valid prefix, centered integer interval induction, row construction from shared edges | n section 08; o pages 6-8; t section 05; u `report.tex:270-438` |
| Small source cleanups | Standard list/modulo/power/sum lemmas, finite sum at most one, CRT congruence, support intersections, absolute trace bounds | f section 02; h local arithmetic; k first section; u `report.tex:440-448` |
| Methodology | Profiling, finite simp boundaries, shared certificates, generator synchronization, helper-inclusive metrics, axiom audits and import discipline | Present throughout; useful validation practice, not a fresh mathematical proposal |

## Easily missed exclusions

1. **Max-plus representation depth is explicitly old.** Packet j,
   `report.tex:347-405`, gives the `Covers` certificate relation, two-number bounds,
   factorial/product plans, and proposed graph-constructor adapters. Packet k,
   `report.tex:491-493,635-636`, also mentions `BoundedForallDepth` explicitly.

2. **Support-restricted evaluation is both existing source and an old note.**
   Packet j, `report.tex:108`, points out `WitnessCompaction.eval_congr`.
   Its `evidence/prior_ideas.md`, candidate 7, discusses frame/overwrite rules.
   The signed-expression extension is therefore not an untouched topic.

3. **Renaming-chain normalization is notes-only but still excluded.** Packet j,
   `evidence/semantic_review.md`, section 5, and `evidence/prior_ideas.md`,
   candidate 8, explicitly propose algebra of the schema index maps.

4. **Cyclic packing as an algebra homomorphism is notes-only but explicit.**
   Packet j's `evidence/algebra_review.md` and `evidence/prior_ideas.md`,
   candidate 9, propose the monoid-algebra homomorphism into
   `ZMod (radix^n-1)` and obtaining convolution and rotation by its universal
   property. Packet q's `evidence/prior_proposals_audit.md:111` records it.

5. **Negative Pell obstruction is exactly proposed in q.** Squaring a norm -1
   solution, classifying the resulting positive unit, and using the first-coordinate
   congruence is the substance of q `report/new-proof-simplifications.tex:139-215`.
   Reimplementing this in `ConsecutivePell.no_negative_nat_y` is not new.

6. **Shared-edge step rows remain excluded even though not integrated.** Packet
   u explains the `rowFromEdges` representation and the single bridge edge at
   `min(oldHead,newHead)`. It also explains the `liveCfg` adapter needed to preserve
   unconditional step-tile statements. The missing production equality does not
   make that proposed architecture available again.

7. **Local coefficient fibers include mixed products.** Packet t's optional
   `PairFiber.lean` and section `07_next.tex:34-43` extend its square coefficient
   theorem to the two contributions `u_i*v_j + u_j*v_i`, with the diagonal handled
   separately. Claiming the bilinear extension as new would repeat that prototype.

## Candidate-specific decisions for this pass

These decisions concern nonduplication, not Lean correctness or measured savings.

| Candidate | Decision | Exact distinction or overlap |
| --- | --- | --- |
| Signed finite-prefix borrow equals the Euclidean quotient of the signed raw prefix by `B^n`, and the word is its remainder | Retain with narrow claim | Earlier natural local carry normalization and cyclic carry formulas do not state this finite signed prefix contract, including negative raw prefixes. Generic quotient-from-decomposition itself is old. |
| Replace `row_zero_of_helix`'s signed induction by a period-one diagonal orbit | Retain | Neither u's interval induction nor aligned-cell equivalence supplies the straightened orbit `k -> T(x+w*k,t-k)`. Helical module names occur only in old freshness metadata. |
| Exact rank equality/order factorization through `C+q*F` | Retain | u bounds rank magnitude from positive source facts. It does not compare two arbitrary coefficient pairs through this scalar potential with fixed ports and `q>1`. |
| Coprime orthogonal-sum divisibility `(J*F | Q*F+J*T) <-> J|Q and F|T` | Retain with narrow claim | Earlier l keeps signed-divisibility witnesses abstract, but does not use coprimality to separate this mixed sum. Do not market generic library reuse or witness opacity as new. |
| Geometric identity gives the polynomial-range bound, eliminating a second induction | Retain with narrow claim | No proposal mentions these `PolynomialRangeBounds` targets or finite geometric-series reduction. Coefficient envelope/reflection work addresses different obligations. |
| Margin positivity gives a linear interval, then the coordinate lower bound | Retain with narrow claim | Earlier finalizer proposals concern rational-root descent or minimum saturation, not this geometric error bound. Source-fact projection is a companion cleanup rather than separate new architecture. |
| Maximum-plus `BoundedForallDepth` checker | Reject | Explicitly j section 6 and k further questions. |
| Negative Pell obstruction through positive units | Reject | Explicitly q section 3, with the same target. |
| Cyclic packing homomorphism | Reject | Explicitly j notes and q exclusion audit. |
| Halted-color normal form solely to share pass/finish allowedness cases | Do not count separately | Too close to n/o's existing color-fiber and finite-dispatch approach for the small advertised payoff. It may be incidental cleanup. |

For the retained rank comparison, keep the ports, `J`, and `q` fixed. At `q=1`
the rank factor vanishes. Equality of potentials does not imply equality of the
coefficient pair. Multiplication by a positive nonunit integer is not an order
isomorphism onto all integers; use strict antitonicity or an order embedding into
the image, as appropriate.

For the retained finite signed normalization, include `n=0` and negative-prefix
examples. The zero incoming borrow is a genuine finite-word definition here and
must not be transported into the already excluded cyclic carry setting.

## Files

- `packet-index.json`: 21 main-report identities, summaries, source paths and headings.
- `corpus-manifest.json`: exact file hashes and sizes under the two requested roots.
- `exclusion-ledger.json`: 120 mechanism entries with source anchors and historical-label map.
- `search-corpus-paths.txt`: text/code search inputs, omitting unchanged baseline directories.

The last file is an aid to reproduction, not an assertion that every listed file
is itself a novel proposal. Candidate searches inspected their hits to distinguish
proposal text from imports, inventories, copied code, and historical receipts.
