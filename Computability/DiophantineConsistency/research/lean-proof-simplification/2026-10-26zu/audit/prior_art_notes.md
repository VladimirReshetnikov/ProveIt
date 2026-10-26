# Prior-proposal exclusion audit

Source cutoff: `9d9d1123b39927d30363f1dcd53c23f0575c30ee` (26 October 2026).

This is an intermediate audit for the current proof-simplification review, not a claim that earlier proposals have all been implemented or that they compile together. For novelty accounting, every prior proposed outcome is assumed available, including optional, deferred, uncompiled, competing, and exploratory proposals. Moving a lemma, validating an old candidate, renaming a framework, or applying an already announced mechanism to its announced family earns no new credit.

## Scope and counts

- The research directory contains **36 packets**, `2026-10-26a` through `2026-10-26zj`.
- Git lists **2,169 files** in that directory. The focused checkout materializes **2,068 text/code files**: 210 Markdown, 130 TeX, 77 TXT, 481 Lean, 153 patches, 39 diffs, 784 JSON, 25 CSV, 146 Python, and 23 shell files. The omitted formats are PDFs, TSV provenance tables, TOML, and checksum/license files; their paths were inventoried. The TeX manuscript sources were available.
- All five current incoming ZIPs were opened; every member was read in memory for decoding/hash/search. There are **1,933 non-directory members**, of which **1,899** decode as text in the chosen searchable source/document formats. **No nested ZIPs** occur.
- All 36 top-level READMEs, manuscript proposal/section indexes, current research README and adoption ledger, and the incoming README's relevant proof-simplification and checkpoint sections were read. Primary proposal statements and close technical precedents were read; candidate-specific searches included both prose and code. Existing inherited exclusion ledgers were used as a cross-check, not as a substitute for resolving close precedents.
- This does **not** claim a fresh semantic verification of every old proof implementation, every compiler log, or every historical research dossier linked by the 275 KB incoming README. It does not infer novelty from filename or keyword absence alone. Source snapshots copied into earlier packets are distinguished from proposals made by those packets.
- `prior_art_inventory.json` records each incoming archive's SHA-256, member counts, and the commit pin.

All paths below, unless otherwise specified, are relative to `Computability/DiophantineConsistency/research/lean-proof-simplification/`. A packet letter means its `2026-10-26` prefix.

## Established broad families: do not repeat

| Family | Assumed earlier outcome | Main evidence |
|---|---|---|
| PR and scanner proofs | Recursor congruence; fixed/reject/done/invariant iteration laws and Function.iterate bridge; dynamic/input-dependent supplied-program iterator; exact numeric Boolean results and tag dispatch. | a `lean/RecursorCore.lean`, `lean/ScannerCore.lean`; b `lean/ValidatedFold.lean`; a–h scanner sections. |
| Histories and checking | Shared validated-history fold with distinct input/stored types; arbitrary raw-code simulation with fuel; Produces append/step; exact reversed-history offsets; arbitrary-premise proof fragments. | b report §5; c syntax notes; h scanner/history sections; p report §B. |
| Decoders and syntax | Core List lookup and Option injectivity/bind inversion; fused quote/depth/graph invariant; total decoder bridge for parent codes; standard-list-code identification; typed checking from raw checking; tagged constructor/no-confusion views. | a–h lookup/decoder proposals; i/j decoder chapters; n A1/A2; t `report/sections/02_encoding.tex`; j constructor chapter. |
| Representation wiring | Assignment naturality, Sum.map/Fin witness splitting, support-restricted evaluator congruence, graph and relation constructor projections, pairing inverse projections and canonical witness uniqueness. | a assignment patch; b witness-layout chapter; j `evidence/prior_ideas.md` candidates 7–8; k/m projection chapters; p §E. |
| Compiler architecture | Shared finite sum-of-squares syntax/evaluation/zero/degree/cost; semiring gate specialization; generic topological evaluator invariant; generic translation simulation with commutative swaps; append/register topology; generated node façades and existing power labels. | a–h compiler and generated-circuit sections. |
| Circuit sharing | Preserve semantic register cuts; common 99-node Split/Gap tail and boundary substitution; common scalar FreeCarrier tail; cancellation-aware normal forms. | c shared-tail/register-cut sections; e scalar-tail chapters; f circuit chapter. |
| Degree and metadata | Earlier weighted syntax-degree interface, weight-one specialization, sharp numeric degree profiles; generic max-plus depth certificates and expression-plan traversal with sharing; early witness-count projections. | a/c/f/h degree chapters; j depth chapter; k/n budget helpers. |
| Coefficients | Common row-envelope dispatch, signed monomial majorants, homomorphic coefficient AST, sparse quadratic reflection, row operations, support-before-coefficients, local two-point coefficient fibers, multiplicative envelope composition. | c/d/f/g/h; i support chapter; t coefficient chapter; zc/zf. |
| Pell estimates | Exact rational-root descent; integer unit decomposition; positive-coordinate base monotonicity; odd-index reuse; sign ambiguity as a compositional relation; small-ordinate fundamentality; scaled/error-budget bounds; natural perturbation/power sandwich; exact quotient rounding; fixed-index anchor. | i–m; p/r/s/u; t minimality; z fixed-index-six chapter. |
| Norm and minima proofs | Integer-only nonsquare norm argument; negative Pell obstruction from positive units; shared residue obstruction; finite minimum saturation; separated signed-root finalizer. | l/m/q; zc/zf inherited ledgers. |
| Internal arithmetic | Model-axiom/completeness/sealing bridge; arity/environment transport; definable induction transport; exact formula-spec normalization; unique-existence code induction; definable recursive-graph preservation/fusion; remove vacuous internal inductions; ordered-semiring reuse; successor discreteness from membership; strict order supplies LinearOrder. | a–h object chapters; j; l/q; s; x/y/zf. |
| Cyclic word arithmetic | Exact half-radix decomposition; common local quotient/remainder/residue/zero-carry APIs; small CarryCertificate/WordFacts; redundant recurrence as derived method; aligned-cell/residue/origin-support geometry; direct selector sum; same-source extraction; whole-word congruence. | a digits notes; b/c/d/e/f/g/h; n/o word/cycle proposals. |
| Carry uniqueness | Fixed raw and digits imply unique carries by finite maximum principle; fixed packed word determines digits; explicit least/greatest cyclic carries, two-solution classification, budget selection; signed prefix borrow and concatenation; reset-separated raw prefixes. | i normalization; j cyclic carries; zb signed-borrow chapter; incoming `lean-proof-simplifications`. |
| Finite certificates | Generic chunks, balanced block assembly, finite pushforward/fiber identity, injective sparse placement, 34-control descriptors; signal mass through cardinality plus four color moments. | b/d/e/g; z P3. |
| Wang geometry | Guarded color fibers/NorthView; boundary prefix/cycle specialization; finite invariant predecessors; first-exit/prefix theorem; centered integer induction; halt encoding/action reflection; support-aware tape case analysis; shared horizontal/vertical edge fields or pulse; helical period group laws and exact quotient coordinates; canonical full operating rows. | i/l/n/o/t/u/v/w/x/y/z/za/zi. |
| Generic workflow | Profiling, simp boundaries, local certificates, sharding, generator synchronization, compatibility wrappers, imported-axiom audit and data preservation. | All rounds; not new proposal mechanisms. |

## Packet-by-packet additions that are easy to miss

| Packet | Distinct assumptions beyond the broad early baseline |
|---|---|
| a | Conditional padding witnesses; weakening stronger moduli; direct physical selector sums; no-borrow origin decrement; same-source restored windows. |
| b | Minimal carry record stores carry bound, digit bound, decomposition; exact source equations `q=1+Jβ`, `L=q²−1`, `N=q³`, `X=qw` decoded once. |
| c | Generic row operations; native coefficient naturality; generic finite majorant certificate; common 99-node tail. |
| d | Finite-fiber pushforward of folded stencil mass, convolution, and word; named carry interfaces. |
| e | Shared raw-step/bounded-run enumerator builders with separate cost models; optional mask block API; future actual-controller SCC/ranking invariants only after decoder binding. |
| f | Nine-coordinate packaging with coordinate 7 unshifted; lower CurrentCarrierBase facade; sharp Split/Gap degree profiles; predecessor-power cleanup and local finite-set/convolution simplifications. |
| g | Positive-zero-set transport; generic encoded scanner simulation; injective sparse placement distinct from colliding fold. |
| h | Exact decoder Option inversion; internal natural semiring evaluator; semantic binaryForm/unaryForm constructors; zero-pair identity; syntaxDegree rename reuse. |
| i | Rational witness preserved on integral descent; product-unit decomposition; graph decoder specification; finite predecessor reflection; support-first vanishing; convolution point-mass rotation; scoped Primrec fun_prop; normalization uniqueness. |
| j | Internal tagged views/unique existence; recursive-graph preservation/fusion; max-plus depth plans; explicit cyclic carries. Notes additionally include evaluator frame rules, rename index algebra, cyclic monoid/quotient-ring packing. |
| k | Finite support classification; Pell oddness; inverse graph from product equivalence; Euclidean certificate and canonical quotient/remainder/slack; affine composition budget; signed congruence. |
| l | Remove unused-IH internal induction; preserve abstract signed divisibility witnesses; Pell base comparison; integer norm proof; finite inverse invariance. |
| m | Common separated signed-root theorem; small-ordinate Pell criterion; Boolean certificate consumption before conditional witnesses; physical permutation as positive tail. |
| n | Parent total-decoder bridge; fused quotation/depth invariant; direct South prefix; binaryWord_congr moved to definition; zero-base propagation; color-indexed NorthView; CRT congruence and Fin2 budget helper. |
| o | Guarded high-color North/South fibers; reuse theta aligned-cell witness; selectors determine assignment and marked-word coherence. |
| p | Parameterized Pell error factor; arbitrary-premise fragments; successor-first fork correctness; support separation through quotient homomorphism; full canonical pairing witness vector. |
| q | Positive Pell units yield negative obstruction; normalized residue arguments; finite minimum saturation; monotone internal certificate closure under empty/union/justified insertion. |
| r | Natural perturbation/power-sandwich kernel; integer quotient/rounding; rule-schedule syntax derives both checker and PR interpretations. |
| s | Exact Object formula specifications normalize compositionally; Pell positive-scale theorem; discrete recovery from two approximation budgets; observed-certificate union/insertion closure. |
| t | Standard codec identity and typed-parent derivation; local ordered-pair coefficient fiber; squared second Pell coordinate minimality; first exit with valid prefix. |
| u | Native rank lower envelope `(2q−1)(q²−1)`; centered interval induction; first failure with prefix; shared-edge Wang construction; direct `le_abs'` trace bound. |
| v | Halt-last state equivalence; action-halting reflected through stateNumber injection; color_action split only at write site; horizontal edge pulse; translated intervals. |
| w | Period lattice vector; formal RefinedPair polynomial identity before evaluation; exact twisted-band coordinate equivalence; shared spatial/temporal edge fields. |
| x | Formula constructor minima thresholds; strict multiplication by nonzero difference before discreteness; period-one functions; preserve exact witness before existential erasure. |
| y | Sidon span before support case split; period lower bound from strip width; pairing branch from output shell threshold; list-head constructor bound; exact geometric sums; LinearOrder from strict part; direct moment polarization. |
| z | Fixed-index-six Pell anchor; sufficient color moments; canonical operating-row recognition including complete receiver tile. |
| za | Receive tile at actual moved head from spatial matching; canonical row-to-stepTile equality and south projection; finite seam-wall bound. |
| zb | Coprime divisibility interface; geometric range bound from identity; positive quadratic margin as centered interval; whole-prefix signed borrow and nonzero incoming borrow concatenation; native ranks compared by scalar `C+qF`. |
| zc | Compose coefficient estimates; scalar sixteen/72 exponential thresholds; optional explicit allowed-tile index by inverse. |
| zd | Selector-tail cutoff by duality; finite order certificates instead of prime-divisor cases; bounded color-complement cancellation; numeric control-slot invariants. |
| ze | Five Jones evaluation lemmas shared; positive square defect and affine domination for Thirteen carrier; monomial-list interpretation sum bridge; deterministic function witness elimination. **Exploratory joint NaturalSimplifier correctness/size induction is already proposed in `evidence/novelty_audit.md:75`, despite no selected patch.** |
| zf | Multiplication-at-zero specialization; successor membership gives discrete order and division/pairing adapters; coefficient estimate twice for products/powers; quadratic power-comparison threshold. |
| zg | Signed polynomial equality transports through splitNatural to cancellative semiring semantics; sparse-list monomial sum; quantification by restriction surjectivity; residual exponent order obstruction. |
| zh | Finite-chain rigidity; optional Fin.pred implementation; controller coprime/cardinality and Hs helper inline; exact marker-only convolution tail 1991–2010, with exceptional field 2008. |
| zi | Only retained new idea is shared halted pass/finish allowedness witness. Its helical and temporal candidates are explicitly superseded comparison evidence. |
| zj | Finite-order rigidity; controller bounded residue injectivity, cast/value coordinate lift, coprime cardinality; ArithmeticNonzero via square positivity; source positivity from selected digit without marking. |

## Five current incoming archives

### `Lean_Proof_Simplification_Power_And_Masks_2026-10-26.zip`

Read `Lean_Proof_Simplification_Power_And_Masks/README.txt`, primary report sections, `catalog/EXCLUSION_AND_ADOPTION_LEDGER.md`, and final late-review decisions. Exclude guarded power cast/divisibility equivalence in PrimePowerOrder; direct CRT image/exact order reuse and private modulus-transport helper deletion in CurrentPowerCoordinates2011; small-residue bit3 bound in CurrentWordPadding2011; optional Gamma positivity via coprimality. The q_prefix predecessor-power candidate was withdrawn as old and remains excluded. The final ledger explicitly includes ze's exploratory NaturalSimplifier induction and all 36 placed packets.

### `ProveIt_Lean_Simplification_Round5_2026-10-26.zip`

Read `LeanReview5/README.md`, report, selected candidate status and inherited baseline. Exclude Sidon injectivity endpoint reuse, controller order-one endpoint reuse, and definitional iterator depth. Finite physical-order rigidity is retained only as excluded comparison evidence. This packet reports only nine selected physical lines; do not inherit earlier shortlist totals.

### `diophantine-lean-new-obligations-2026-10-26.zip`

Read primary README/report and novelty audit. Exclude five Jones evaluation laws; Thirteen affine reflection `(m,G,y) ↦ (−m,−G,2−y)`; direct homogeneous enumeration with `List.Nat.antidiagonalTuple` (changes syntax, retires unused helpers); weaker fixed-power/annihilation controller assumptions while retaining the necessary auxiliary exact order.

### `lean-proof-simplifications-2026-10-26.zip`

Read primary README/report and 155-entry inherited exclusion map. Exclude fixed-modulus Gamma certificate; full LTE divisibility spectrum as the PrimePowerOrder API; reset-separated cyclic carry/raw-prefix characterization; quadratic sixteen_pow_bound. Generic fixed-point power substitution is covered, even though the actual production adapter is incomplete.

### `proveit-lean-additional-certificates-2026-10-26.zip`

Read primary README/report and exclusion taxonomy. Exclude common modulus `47*2011*120199` for all 941 selector rows and 34 controls (59 common chunks instead of 177); monoid `x^a=x → x^(a^n)=x`; finite-sum update and pointwise-update APIs in CurrentDummyMutation; origin_reflected_zero as reflected_source at zero. A rejected nonexistent-lemma proposal at AnnotatedProofChecker.axiomTags_exists is also recorded; do not blindly reuse its API name. The taxonomy explicitly excludes recurrence removal in the *new* CurrentCarryConstruction.Facts and generic ExpressionSize witness-count projection relocation. **Exploratory ideas also present:** ordered-ring/Grothendieck completion for internal residual semantics; generic ordered-semiring division uniqueness needing comparison to k; noncoprime affine-fiber equivalence for ControllerOrbitTransport/ControllerResidueLift (lines 245–249 and 276–282). Their lack of endorsement does not make them absent.

## Candidate-specific judgments for this review

| Candidate | Decision and nearest precedent |
|---|---|
| Exact unlabeled-tree equality of splitNatural halves; diagonal reachable SplitSize metadata | **Promising residual.** No prior exact shape/count/depth symmetry found. j supplies numeric max-plus inequalities, zg supplies cross-sum semantics, and b supplies earlier count projections; none establish structural balance. Focus on exact symmetry, not generic metadata folds. |
| Polynomial.totalDegree_specializeOne_le through a general affine substitution bound | **Promising residual.** No prior target or MvPolynomial eval₂ degree-substitution mechanism found. Existing proposals concern Expr weighted syntax, residual squares, and cancellation-aware degree. Prefer an existing library theorem to a moved handwritten proof. |
| ObjectDivision.quotient_not_lt via disjoint quotient intervals | **Qualified only.** zf changes successor_step/division_exists, leaving quotient_not_lt unchanged; no explicit interval proof was found. However incoming additional-certificates taxonomy lines 245–249 already mentions generic ordered-semiring division uniqueness as an exploratory direction. Do not present that general idea as new. A narrowly distinct concrete mechanism needs additional justification. |
| Shared monotone half-open-bin uniqueness for ObjectDivision and MaxSquarePairing | **Promising but qualified residual architecture.** y explicitly retains max_not_lt/square_le_square while changing branch recognition; r/s interval rounding is over real approximation. No prior generic monotone-boundary bin theorem or cross-client sharing found. Distinguish it from the incoming exploratory generic division-uniqueness idea. Charge the entire common helper and both adapters; do not reclaim y's branch reduction. |
| NaturalSimplifier fused semantic/size induction | **Reject:** explicitly proposed by ze/evidence/novelty_audit.md:75 and re-excluded by incoming Power_And_Masks final review. |
| boundedRun_eq fixed-none induction replaced by IsFixedPt.iterate | **Reject as standalone novelty:** a/b scanner fixed-point contract plus Function.iterate bridge already provides this. A distinct exact partial-run hitting-time theorem needs separate comparison with t/u first-exit infrastructure. |
| Fresh minimal CurrentCarryConstruction.Facts | **Reject generic record/recurrence idea:** b CarryCertificate already stores carry bounds, digit bounds, decomposition; incoming additional-certificates specifically flags this fresh Facts target. A separate scalar transport theorem could be considered only if it eliminates a genuinely additional obligation. |
| Affine-monoid Horner chunk assembly | **Weak novelty:** no exact affine-monoid proposal located, but b/e generic block assembly and incoming common-modulus certificate already promise the main eliminated repetition. Requires a distinct residual obligation, not representation repackaging. |
| source_N_eq_q_cube by direct polynomial syzygy | **Exclude as a separate source-equation idea:** b already explicitly promises N=q³ from these rows. A one-line proof of its shared implementation is ordinary cleanup, not a newly discovered source-decoding mechanism. |
| Principal bitset ideal/complement-mask API | **No exact precedent located**, but not yet endorsed: must specify bitwise order, width bounds, real clients and full helper cost. Saturation via generic nonnegative defect sums is close to q's finite minimum saturation; current native_mask_saturation is already compact. |
| CurrentPackingRank.rank_gt_twice_window via `2u ≤ 3u < 2^(3u)` | **Narrowly promising residual.** No exact target/full-exponent specialization found. u's old source rank bound assumes source/Pell data; the fresh constructed rank bound precedes those premises. Existing Nat.lt_two_pow_self is background library reuse, not a claimed new exponential theorem. Preserve the fourBlocks_cast subtraction guards. |

The positive decisions are bounded nonduplication judgments, not compiler validation or claims of mathematical priority. They must be revised if a precise earlier passage is found or the proposed implementation merely reproduces a previously assumed contract.


## Final strict audit of the retained shortlist

The exact paths, line ranges, SHA-256 hashes and pinned Git blob IDs are recorded in `prior_art_final_novelty.json`. Each materialized evidence file was compared to its Git blob at the review commit. The incoming taxonomy is identified by both the archive hash and the member hash.

1. **Retain exact split-half shape balance.** The new obligation is equality of operation-labeled trees after leaves are erased, and the diagonal invariant for expression-generated `SplitSize`. It is not the earlier generic metadata-fold, count-projection, or max-plus depth mechanism. Preserve `SplitSize` operations on arbitrary off-diagonal records; compute only the reachable expression metadata through one scalar. If its definition changes, explicitly prove equality to the old recursion and disclose the definitional-equality impact.
2. **Retain monotone-window uniqueness only as qualified shared architecture.** The incoming additional-certificates taxonomy at lines 245–249 already mentions generic ordered-semiring division uniqueness. Its elimination of `quotient_not_lt` earns no fresh line-saving credit under the all-applied assumption. The residual is the common monotone-boundary theorem and its square-pairing client. Compare against packet y's already reduced branch proof, charge the whole shared helper, and show division as compatibility/reuse evidence. No earlier common-window abstraction was located, but this proximity must be disclosed.
3. **Retain the full-exponent rank comparison as a modest local cleanup.** In the newly introduced constructed-rank theorem, `2*u <= 3*u < 2^(3*u)` removes the intermediate positivity/base-square detour. Packet u's native envelope assumes source equations and positive coordinates unavailable at this construction stage. Preserve the cast and subtraction guards and count only the narrow exponent-proof delta.
4. **Reject the proposed four-block eliminant as new.** `NativeSourceMask.lean:87–95` already states the exact once-shifted polynomial identity and proves it by `linear_combination q * h`; the fresh client already invokes it. The proposed `linear_combination (-q) * hb` merely reverses that same residual after casts. Packet zj's `evidence/novelty_inventory.md:40–48` explicitly excludes shorter rank cast handling, and packet u likewise excludes cast-interface savings. Do not include it in the novelty/savings total; optional ordinary cleanup can be labeled accordingly.

No result here certifies compilation of a proposed patch or simultaneous integration of all competing prior proposals. The all-applied rule is used for novelty and savings accounting.
