# Non-repetition audit of rounds a-r

Source pin: `1e2a853935a6155cbcf2aa199aaca51946c4fff9`.
Prefix `P` below means `Computability/DiophantineConsistency/research/lean-proof-simplification`.
The eighteen round directories were enumerated through untruncated GitHub subtree listings. The audit materialized 125 Markdown/LaTeX files, 313 Lean/patch files, and 48 relevant text/ledger files, plus the directory README and ADOPTION record: 488 files in total. Every selected file was verified against its pinned Git blob SHA-1; SHA-256 hashes are recorded in `prior-audit-verified-manifest.json`. Main reports, substantive notes, accumulated exclusion catalogs, proposal headings, and candidate-specific source/prototype passages were inspected. Bundled unchanged source snapshots are evidence, not by themselves proposals.

## Counterfactual baseline

The user's instruction excludes every substantive idea appearing in these packets, even when the repository adoption ledger says pending, deferred, rejected as default, optional, uncompiled, or notes-only. Stronger verification or another named helper implementing an old proposal is not a new idea. General textbook techniques are not globally forbidden; a new recommendation must identify a materially different proof obligation or a precise source-specific improvement beyond the prior interface.

The three current `docs/incoming` ZIPs are being audited separately by the incoming-review agent. This file covers the a-r rounds and does not certify novelty against the incoming ZIPs by itself.

## Consolidated exclusions

### Syntax, annotations, and realizers

- **PR recursion congruence**: move pointwise equalities through `Nat.rec`; `Realizes.prec`, scalar/vector PR and optimizer clients. Prior: a report, “Rewrite under primitive recursion”; a `lean/RecursorCore.lean`.
- **Core list and Option reuse**: `getElem?` to membership and back, `Option.map_injective`, Option successful-bind decomposition; shared `zero_pair`. Prior: a §small replacements; e checker patch; h report and `evidence/syntax/findings.txt` items 1, 2, 7.
- **Witness layout and assignment naturality**: `natAssignment ∘ Sum.map`, `Fin.addCases` witness splitting, reindexing, earlier constructor projections, `Sum.exists_sum`. Prior: a/b/d/g/h representation sections.
- **Scanner iteration and simulation**: zero/fixed-state laws, raw-code soundness, encoded completeness, invariant-preserving run folds, input-dependent seed/fuel/step PR iterator. Prior: a/b/c/d/e/g/h scanner sections.
- **History/proof-fragment composition**: heterogeneous input-line versus stored-judgment histories, `Produces.append/step`; **arbitrary-premise backward-reference synthesis from suffix lengths** is also prior (p, proposal B), beyond the original two/three-fragment framework.
- **Boolean/tag/constructor dispatch**: exact numeric output from range and acceptance; threshold tags; semantic binary/unary constructors. Prior: a/b/e numeric Boolean sections; h syntax findings item 6.
- **Decoder graph fusion**: quotation and depth in one induction and exact arbitrary-code/fuel graph iff; separate Option simplification as an axiom-sensitive alternative. Prior: h/i/j/n.
- **Total parent decoding**: reuse total decoding for arbitrary parent codes, preserve genuinely partial parser semantics. Prior: n section A1.
- **Extensional Primrec automation**: `fun_prop` rules and constructor adapters. Prior: i report and notes/checker.
- **Shared Direct/Native graph builder templates** and backend-specific counts. Prior: e §14.
- **Inverse pairing via product equivalence**, including coordinate projection and potential Cantor clients. Prior: k proposal 3; m inverse graphs.
- **Depth/witness arithmetic and max-plus certificates**: affine composition budgets, zero-arity distinctions, baseline/excess depth tables and automation. Prior: j depth proposal; k budget proposal; n supplemental S2.
- **Schema-map renaming-chain normalization**, support-restricted evaluator congruence/overwrite frame rules. Explicit notes-only proposals: j `evidence/semantic_review.md` §5 and `evidence/prior_ideas.md` candidates 7-8.
- **One rule-schedule AST with both typed and numeric interpretations**, including actual data-preservation bridge. Prior: r report final main proposal.

### Expressions, circuits, and compiler proofs

- **Finite residual aggregation**: sums of squares, zero iff all residuals zero, cost and degree bounds, shared semantic APIs across DAG/register compilers. Prior: a/b/c/d/g/h.
- **Semiring gate soundness/completeness reuse**, separate signed and natural wire codecs and exact counts. Prior: b/c/d/e/g.
- **Structural/weighted degree infrastructure**, shared Short-family prefixes, cancellation-aware normal forms; degree automation itself is also already implemented upstream. Prior: a/c/f; ADOPTION.
- **Existing power-checker certificates**, parent exponent labels, indexed node facade, compatibility wrappers and generator synchronization. Prior: a/b/e/f/g/h.
- **One topological DAG invariant**, including nonnegativity, uniqueness, degree and support; semantic block certificates and checked-circuit/safe-node views. Prior: a/d/f/g/h.
- **Circuit simulation with commuted add/mul**, input/ref/prefix maps and special unshifted input. Prior: a/c/g.
- **Register append/topology/evaluation interfaces**. Prior: a circuits source notes.
- **Shared 99-node free-carrier tail** and scalar ratio tail, semantic cuts and register binding. Prior: c/e/f.
- **Coefficient-envelope factoring**, finite nonnegative monomial majorants, syntax/table naturality and homomorphic row dispatch. Prior: c/d/f/g/h.
- **Sparse quadratic row reflection/normalization**, with independent source-residual specification. Prior: c/g.
- **Elementary row-operation and surjective reindexing invariance**; invertible-matrix extension already suggested. Prior: c report.
- **Guarded solution-existence transport**, pointwise zero-set equivalence lifting; **nine-coordinate packaging** and named conjunction/port accessors. Prior: e/f/g.
- **Split/Gap degree/source profiles** with exact sharp inequalities. Prior: f architecture section.
- **Univariate support envelope before coefficient proofs**. Prior: i report.
- **Dedicated natural-semiring register evaluator with erasure correctness**. Prior: h `evidence/structural/findings.txt` item 7. Rephrasing natural assignments as typed data is not automatically new.

### Native digits, cycles, and finite geometry

- **Exact half-radix quotient/remainder identity**; eliminate finite digit cases. Prior: a-g.
- **Strongest-modulus reuse**, cyclic addition/subtraction/source residues and whole-cell versus local residue distinction. Prior: a/c/d/e/f/g.
- **Exact carry decomposition API**, derived quotient, remainder, no-carry, residue, and removal of redundant recurrence fields. Prior: a/b/e/g.
- **Conditional padding witnesses** under phase assumptions. Prior: a.
- **Aligned-cell/finite-word interfaces**, ZMod/Fin/list conversions, geometry records, existing `Cell ≃ ZMod N` reuse, wraparound and N=1. Prior: b/e/g/h.
- **Coherent canonical source/window extraction**, common Facts views and CurrentCarrierBase import split. Prior: a digits notes §8; c/e/f.
- **Origin no-borrow word decrement**, direct physical selector sum and common mask-block bounds. Prior: a digits notes; e/g.
- **Finite pushforward/fiber sum**, arbitrary folding with collisions versus injective sparse placement. Prior: d/g.
- **Finite chunk/tail assembly**, generic finite checking wrappers, four packed-field descriptors/bounds. Prior: b/e/f.
- **Zero-or-singleton support from Finset sum≤1**. Prior: g/h/k/n.
- **Invariant predecessor through finite-set inverse invariance**, replacing orbit-period construction. Prior: i/l.
- **Rotation as convolution with a point mass**. Prior: i.
- **Canonical carry/digit uniqueness by finite maximum**, full-word injectivity; explicit least/greatest carries and precise two-solution boundary. Prior: i/j.
- **Cyclic packing as monoid-algebra homomorphism into ZMod**, with convolution/rotation from universal properties. Notes-only but explicit: j `evidence/algebra_review.md` final direction and `evidence/prior_ideas.md` candidate 9.
- **Physical permutation as positive tail**. Prior: m optional proposal.
- **South prefix clients**: normalize `offset19_word/offset20_word` directly by existing binary-prefix theorem, retain weighted correction. Prior: n C2; o page 4.
- **Binary-word congruence beside its definition** and copy translation/horizontal aggregation. Prior: n C3.
- **Exact difference-cell witness via theta**, zero-base propagation as `propagate_from` specialization. Prior: n C4; o page 5.
- **Equality-indexed North/South high-color fibers** and concrete classification clients. Prior: n W1; o pages 6-7.
- **Canonical selected-index characterization for the same original word**, transport of marked-word correctness, without assuming tile-color injectivity. Prior: o page 8.
- **Projected support-difference separation** outside S-S, exact NativeTemporalSupport54 displacement 606 client. Prior: p proposal D.
- **Ranking/SCC finite-state controller certificates** are already a broad future direction. Prior: e §13.

### Pell, arithmetic, and certificates

- **Literal Pell/source-register decoding** into named q/L/N/X facts and Nat/Int boundary normalization. Prior: b/c.
- **Reuse existing Pell parity**, preserve divisibility witnesses abstractly, signed congruence as compositional relation with negation/natAbs/multiplication/powers and guarded sign resolution. Prior: j/k/l/m.
- **Preserve exact rational roots under integral descent**, whole-tuple/sign-preserving finalizer descent. Prior: i/m.
- **Product-unit decomposition** into conditional ±1 alternatives. Prior: e/i.
- **Positive-denominator quotient/remainder/slack certificate and uniqueness**, separate quadratic/register realizers. Prior: e/k.
- **Compare Pell bases via simultaneous positive pair recurrence monotonicity**, removing exponential detours and redundant index hypotheses. Prior: l/r.
- **Prove nonsquare norm nonvanishing entirely in integers by power-divisibility**, eliminating rational-root detour. Prior: l idea 5.
- **Small-ordinate Pell fundamental/minimality criterion**. Prior: m.
- **Consume existing Boolean certificate directly before building a conditional**, preserving representation data. Prior: m.
- **Pell upper estimate with explicit real error factor** and both original specializations. Prior: p proposal A.
- **Natural perturbation/power-sandwich kernel for both Pell upper bounds** plus separate error budget. Prior: r.
- **Half-binomial exact integer-quotient rounding**, replacing real fractional-witness detour. Prior: r.
- **Successor-first fork-certificate equivalence** plus single impossible-zero case. Prior: p C.
- **Canonical square-pairing selector/slack/maximum witnesses**. Prior: p E.
- **Consecutive negative-norm obstruction from classification of positive units**, squaring a hypothetical negative unit and first-coordinate congruence. Prior: q.
- **One discriminant normal form for three norm/residue obstructions**, using existing `ShortEquation.strong_ne_neg_one`. Prior: q.
- **Heterogeneous/coupled minimum saturation with Finset.sum_eq_sum_iff_of_le**, deriving all equality cases at once. Prior: q.
- Standard finite intersection, huge-power symbolic handling, predecessor exponent and casts, sum factorization are prior local advice throughout.

### Internal object models

- **Arbitrary-model validity→sealed derivation bridge**, one ZFC-model→ZF-axioms proof, arity-polymorphic closed-sentence transport. Prior: a/b/c/h.
- **Definable induction wrappers** with actual formula/satisfaction witnesses; model-independent finite-index reasoning. Prior: a/c/g.
- **Internal constructor views and fused unique existence**, definable graph preservation/fusion. Prior: j.
- **Remove unused internal inductions using zero-or-successor cases** in addition cancellation/zero-product proofs. Prior: l/q.
- **Monotone local certificate closure calculus** for empty/union/insert and BoundCodeRel. Prior: q.
- **Use existing internal-semiring evaluator**; deliberately split foundational definitions if needed, preserving unguarded uniqueness. Prior: h syntax findings item 8; c report 854-867.
- **Ordering dependency cycle awareness**: c report lines 854-867 explicitly notes OrderedSemiring→Discrete prevents importing it into ObjectResidualSquares, and already suggests lower-assumption lemmas or module reordering. General import reorganization is excluded, though a new concrete algebraic proof can go beyond that advice.

## Candidate-specific preliminary decisions

| Candidate | Nearest precedent | Decision against a-r |
|---|---|---|
| Helical row-zero equality from period-one rigidity after reparameterizing along the helix | Shared cyclic geometry; centered integer induction is separately in pending ZIPs; finite predecessor invariance in i/l | No prior helical/period-one argument found in a-r. A concrete `Function.Periodic` proof removes two-sided induction and appears distinct. |
| Expose canonical CycleBand word and prove exact MarkedWord+binding before existential erasure; reuse in BandMarker | Canonical digit/window extraction (a/f), same-word selected-index coherence (o), general exact witnesses | No `CycleBand`, `BandMarker`, `canonicalWord`, `marked_word_of_halt` proposal found. Describe only this new exact-witness pipeline reuse; generic canonical witnesses are prior. |
| Strict multiplication from additive difference and NoZeroDivisors; idempotence via cancellation before discreteness | c report explicitly suggests reordering OrderedSemiring/Discrete dependency; k broad difference/order-embedding search direction | Exact strictness/idempotent mechanism absent. Retain only the stronger concrete result that these laws need no successor discreteness, with actual dependency change and measured client. Do not present import reordering as new. |
| Replace foundational expression totality/uniqueness/naturality by internal semiring evaluator graph | h report + syntax findings item 8; c object section | Exclude as repeat. |
| Generic sparse polynomial reflection / universal evaluator | c/g row reflection and coefficient naturality; j cyclic monoid algebra notes | Exclude broad formulation; requires a materially different exact mathematical contract. |
| Natural-register evaluator/subtype recasting | h structural findings item 7; b/c gate-semiring reuse | High overlap; not enough by itself. |
| Formula-code threshold 44 from coordinatewise square-pair monotonicity and constructor minima | e AnnotatedClosure proposal is typed/numeric iterate fusion; generic code/certificate bounds elsewhere | No prior lower-bound replacement found. Precise threshold/minimum proof removes separate custom nonlinear square/fork helpers and appears distinct. |

## Useful exact source references

- `P/ADOPTION.md`: adopted/in-validation/pending statuses; these do not limit the exclusion set.
- `P/2026-10-26q/evidence/prior_proposals_audit.md`: cumulative family taxonomy through a-k with explicit notes-only cautions.
- `P/2026-10-26p/evidence/novelty_audit.md`: detailed exact mechanisms and differentiation of pairing, fragments, projected support.
- `P/2026-10-26h/evidence/syntax/findings.txt`, items 6-8: less visible constructor/zero-pair/internal-evaluator proposals.
- `P/2026-10-26c/report.tex`, lines 854-867: ordered-semiring/discreteness import-cycle precedent.
- `P/2026-10-26o/report/report.tex`, pages 4-8: South prefix, cycle witness, exact color fibers, selector coherence.
- `P/2026-10-26r/report.tex`: Pell recurrence comparison, natural perturbation kernel, integer quotient, rule schedules.

This audit establishes a scoped non-repetition screen. It is not a claim of mathematical originality in the Lean ecosystem, and absence of a literal filename was never used as the sole novelty argument.


## Supplemental screen: docs/incoming/README.md

The pinned incoming README was inspected in addition to the three current ZIPs. Its first DiophantineConsistency section records the retirement and placement of the same eighteen a-r packets. The large Con(ZFC) equation section primarily records placements, recovery counts, and adoption status. The K215 proof-simplification section, approximately lines 390-530, also contains substantive summaries; those were read, together with the current K215 checkpoint, and the complete README was searched for the four retained mechanisms and their source declarations.

These summaries add the following exclusions where relevant: shared transfinite recursion and quotient syntax, proof fusion, collection-first assembly, common macros, direct seed/shared rules, native replacement, proof boundaries, quotient detachment, composition-address bounds, automatic certificates, checked affine cores, ordinary bisimulation, and semantic normal forms. They do not propose the precise helical period-one argument, the exact CycleBand quotient/binding factorization, multiplication strictness from canonical differences and no zero divisors, or the outer-constructor minimum proof for formula code 44.

| Retained mechanism | Result of supplemental README screen |
|---|---|
| Helix and seam status as period-one functions on the integers | No additional overlap. The current incoming centered-induction proposal concerns interval propagation around a known interior point, rather than the global adjacent equality used here. |
| Exact CycleBand quotient properties reused before existential erasure | No additional overlap. Existing coherent source/word interfaces remain excluded as general directions; this recommendation concerns the newly shared concrete CycleBand/BandMarker construction. |
| Strictness without successor discreteness, then Boolean idempotence by cancellation | No additional overlap. The earlier round-c dependency-cycle observation is still material precedent and must be acknowledged. |
| Formula-code minimum from coordinatewise pairing monotonicity and constructor minima | No additional overlap. Constructor-only certificate references in the README concern machine data, not this formula-code bound. |

Scope qualification: this screen covers the README's contents and summaries. It does not claim to have read every historical dossier linked elsewhere in that 270-KB intake ledger. It complements the separately inspected current incoming ZIPs and the SHA-verified a-r corpus. A general technique's occurrence elsewhere is distinguished from a repeated source-specific proposal; absence of a literal filename is not the sole novelty criterion.

The independently reviewed patches preserve existing public theorem statements and computational definitions. A separate `independent_patch_review.md` records proof obligations, integration checks, precise patch hashes, and the distinction between source review and compiler validation.

Pinned `docs/incoming/README.md` SHA-256: `63e6704dd21f5159d25e875db23a006b47945a285e028171c9e11f8261a38bf3`.

## Closing refresh at f42d3f94f78eb63639316a33e25f2f69d12c651e

The exclusion corpus was refreshed after main advanced. New rounds s, t, and u are the previously reviewed three incoming archives: 158 retained files were verified byte-for-byte with zero mismatches. New round v was separately audited through all 38 selected report/note/Lean/patch files, with Git blob verification. Its six proposals concern terminal-state encoding injectivity, action-halt equality reflection, write-site-only case splitting, absolute-value trace bounds, guarded translated interval induction, and a shared horizontal bond signal. None repeats the four retained precise mechanisms. In particular, v cites the old seam induction as precedent for its interval proof but does not propose the period-one seam or helical replacement. Full decisions, exact locators, retrieval hashes and comparisons are in `final-refresh/refresh-audit.md`, `final-refresh/retrieval-manifest.json`, and `final-refresh/existing-archive-byte-comparison.json`.
