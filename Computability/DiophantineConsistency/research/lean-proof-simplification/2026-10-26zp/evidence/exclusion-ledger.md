# Exclusion ledger for the 26 October 2026 review

**Late supplement:** `late-refresh.md` supersedes this initial inventory at
cutoff `ae736b383e59c32c3c3f81910ef1c1197cbfbd44`: 36 packets a–zj,
with eight newly reviewed packets and no remaining incoming ZIPs.
The search-space notes below are historical observations at the original pin,
not final novelty clearance. In particular, the full coordinate/control-update
direction is excluded by w and newly placed zd.

## Scope

Repository pin: `e1c8914bc7064d9a8e7c06171a18069a949badd0`.

The exclusion set is the 23 placed packets `2026-10-26a` through
`2026-10-26w`, plus all five ZIP files present in `docs/incoming` at that
pin. Every proposal counts, including alternatives, deferred work,
uncompiled examples, design-only notes, and further-research suggestions.
The adoption record is useful evidence of prior work, but does not narrow
this exclusion set.

`corpus-index.json` records 82 TeX input files (1,086,021 bytes), all 28
packet identities, the incoming archive hashes, and the 1,042 incoming
nondirectory member names/sizes. These are inventory counts, not counts of
independent ideas. The audit inspected proposal headings, delivery notes,
exclusion ledgers, mechanism descriptions and supporting notes; candidate
clearance additionally requires searching the exact mechanism through the
text and Lean proposals. It does not claim a line-by-line review of every
duplicated baseline snapshot, or global mathematical novelty.

In the table below, a letter means the placed packet under
`Computability/DiophantineConsistency/research/lean-proof-simplification/`.
The JSON index provides report paths and heading line numbers. Entries may
overlap: they are a conservative exclusion map, not a disjoint taxonomy.

## Already-proposed mechanisms

| Family | Mechanisms that must not be proposed again | Representative evidence |
|---|---|---|
| Recursion and lists | Congruence below `Nat.rec`; standard `getElem?`, membership and `Option.map` facts; specialized zero/successor/fixed-state iterator laws | a, b, e, h |
| Assignment transport | Assignment naturality, `Sum.map` witness renaming, witness regrouping/splitting, placing projection lemmas earlier | a-d, g, h |
| Checker simulations | Raw-code soundness, exact numeric Boolean acceptance, history folds, shared scanner kernels, supplied `iterateFrom` programs | a-e, g, h |
| Rule dispatch | Shared finite tag dispatch and unary/binary semantic form constructors; one syntax of rule schedules compiled to numeric and supplied-PR backends | b/e/h notes; r |
| Proof fragments | `Produces` append/step, generic unary/binary fragments, arbitrary-premise reversed-history collection and finishing | b/c notes; p |
| Decoder invariants | Successful-bind inversion; quotation/depth fused graph theorem; total parent decoding and re-encoding; identify standard list codec before length/raw-parent proofs | h, i, j, n, t |
| PR proof automation | Scoped `fun_prop` for extensional Primrec closure, separate from supplied program syntax | i |
| Compiler correctness | Shared residual sum-of-squares semantics/zero criteria/degrees/counts; natural/semiring gate specializations; topological DAG induction | a-h |
| Generated circuits | Existing power-label checker, indexed/lazy named facade, generation templates, local gate specialization, semantic blocks and register cutpoints | a-h |
| Circuit structure | Shared 99-node free-carrier tail; positive/natural simulations including commutative node swaps; append/frame invariants; typed earlier-node views | a/c/e/f/g |
| Degree proofs | Move structural degree lemmas earlier; weighted/profile/prefix certificates; cancellation-aware normalization; degree-bound tactic | a-h; ADOPTION |
| Representation depth | Affine/max-plus depth and cost budgets, two-number certificates, binary composition bookkeeping | j, k, n |
| Evaluator context | Support-restricted congruence/frame/overwrite laws, certified schema rename-map normalization | j supporting notes |
| Packing coordinate views | Nine-coordinate equivalence, named conjunction fields, coherent source/window certificate, lower current-base import layer | e/f |
| Graph enumerators | Common direct/native graph-enumerator control flow while retaining separate witness counts; extend the same frontend to Scalar | e |
| Euclidean certificates | Positive-denominator quotient/remainder/slack specification and canonical uniqueness | e, k |
| Pairing | Inverse-coordinate graphs via existential projection/product equivalence; canonical selector/slack/max witnesses; branch from output threshold | k, m, p; incoming Further Deltas |
| Fork certificates | Prove successor-output cases first and isolate predecessor/zero boundary | p |
| Digits/carries | Scaled half-radix division identity; exact carry decomposition; derive recurrence and modular projection; named carry certificate | a-h |
| Modular reuse | Project stronger congruence to weaker divisors; cyclic field residue and wrapped temporal translation interface | a-d, f-h |
| Native geometry | Aligned-cell equivalence with `ZMod`; off-origin placement; no-borrow origin decrement; direct physical selector sums | a-h and notes |
| Finite sums | One-hot `sum_le_one_iff`; finite-fiber weighted pushforward; injective sparse placement separately; standard mask/intersection/convolution facts | b/d/f-h/k |
| Coefficients | Envelope schema, finite dispatcher, monomial majorant, naturality, sparse quadratic normalizer, local quadratic-fiber theorem | c/d/h/t |
| Polynomial support | Support envelope before coefficients; rotation as convolution by point mass; support separation through quotient homomorphism | i, p |
| Normalization | Fixed-length packing injectivity; finite-maximum carry uniqueness; exact least/greatest cyclic carry formulas; cyclic packing ring/monoid-algebra map | i/j and supporting notes |
| Arithmetic domains | Keep large powers symbolic; existing remainder/subtraction laws; supported cast handling; integer-only norm proof | h/l |
| Signed algebra | Signed congruence as a transitive relation, `natAbs` invariance, abstract divisibility witnesses, exact rational-root integral descent preserving signs | i-m |
| Units and minima | Product-unit decomposition, uniform small-ordinate Pell criterion, negative Pell obstruction via positive units, residue obstruction reuse, heterogeneous minimum saturation | e/i/l/m/q |
| Pell estimates | Odd-index criterion, simultaneous base monotonicity, positive-coordinate recurrence, variable error-factor/scale envelope, natural perturbation kernel, exact half-binomial quotient | k-r, s/u |
| Pell thresholds | Fixed index-six anchor rather than the general exponential detour | incoming Structural Simplifications |
| Rank bounds | Stronger shared `(2q-1)(q^2-1)` envelope; rank affine comparison through `C+qF` | u; incoming Additional Simplifications |
| Finite invariance | Invariant finite subsets closed under inverse/permutations; avoid explicit periodic predecessor iteration | i/l |
| Object arithmetic | Definable induction transport, arbitrary-model axiom extraction, validity/completeness/sealing bridge, arity-polymorphic closed-sentence transport | a-h |
| Internal code graphs | Constructor/no-confusion views, unique-existence induction, recursive graph preservation/fusion with explicit definability witness | j |
| Internal simplifier | Exact formula specifications compositionally by semantic fold; finite-index/list quantifier normalization | c/g/h/s |
| Internal induction deletion | Use `nat_zero_or_succ` when induction hypotheses are unused | l/q |
| Internal certificates | Monotone local-certificate calculus; union/insert closure of observed certificate sets | q/s |
| Internal order | Strict multiplication from additive difference plus no zero divisors before successor discreteness; construct non-strict order from strict total order | incoming Proof Refinements; incoming Further Deltas |
| Formula/list codes | Outer-constructor minima for `formCode_ge`; `head_cons` plus addition monotonicity for list-head bound | incoming Proof Refinements; incoming Further Deltas |
| Binary words | South offsets 19/20 specialize the existing prefix law; hoist `binaryWord_congr`; exact signed-prefix quotient/remainder | n/o; incoming Additional Simplifications |
| Cell propagation | Use existing aligned translation as reachability witness; zero-base specialization of arbitrary-base propagation | n/o |
| Tile colors | Guarded north/south equality-indexed high-color fibers; color-indexed boundary views | n/o |
| Selected assignment | Characterize alternate assignment by original selected bits; preserve exact canonical band witness before existential erasure | o; incoming Proof Refinements |
| Wang row geometry | Translated/centered integer interval induction, least first failure with valid prefix, Fin 3 wall-bound cleanup, absolute-value trace bounds | t/u/v; incoming Post-Adoption |
| Wang machine cases | State/action halt via existing injectivity, split at write site, exact absolute-value view | v |
| Wang row construction | Shared horizontal edge field/pulse; certified run rows and boundary-to-boundary composition | u/v/w |
| Helical geometry | Period-one orbit, two-dimensional lattice period/group law, shear of coordinates, twisted-band quotient equivalence and equivariant descent, seam time invariance | w and incoming packets |
| Strip width | Derive `L+R <= N` from seam-free strip and positive period; obtain `N>2` without early halting | incoming Further Deltas |
| Canonical operating rows | Receiver causality, complete interior equality to `stepTile`, canonical row recognition, local tile determinism with finish exclusion | incoming Post-Adoption and Structural Simplifications |
| Tile signal sums | Affine mass formulas through sufficient color statistics, four-client pilot | incoming Structural Simplifications |
| Refinement identities | Formal polynomial identity via injective exponent dilation instead of choosing complex roots | w |
| Sparse span | Settle all non-extremal rows by a uniform exponent bound before inspecting row support; Sidon polarization supplement | incoming Further Deltas |
| Local arithmetic reuse | Coprime combined divisibility, geometric bound from exact geometric sum, positive quadratic margin as interval | incoming Additional Simplifications |
| Methodology | Stable simp boundaries, profiling, certificate sharding, axiom audits, generator synchronization, compatibility wrappers and honest helper-inclusive accounting | all; not a new mechanism |

## Incoming packet names (exact)

1. `Lean_Proof_Simplification_Post_Adoption_2026-10-26.zip`
2. `ProveIt_Additional_Lean_Simplifications_2026-10-26.zip`
3. `diophantine-lean-further-deltas-2026-10-26.zip`
4. `diophantine-lean-proof-refinements-2026-10-26.zip`
5. `proveit-lean-structural-simplifications-2026-10-26.zip`

## Promising search space, not cleared proposals

A name-level search over report/notes text found no substantive mention of the
newer current-controller and construction modules including
`CurrentWordTopBounds2011`, `CurrentWordPadding2011`,
`CurrentWordCopies2011`, `CurrentControllerUnits2011`,
`CurrentDummyMutation2011`, `CurrentWordConstruction2011`,
`CurrentControllerData2011`, `CurrentWordClause2011`,
`CurrentWordScalarWitness2011`, `ControllerOrbitTransport`,
`ControllerIntervalSums`, `PrimePowerOrder`, and `ControllerResidueLift`.
This suggests where to look; a module-name absence is not enough to clear a
proposal whose mathematical mechanism is already listed above.

## Counterfactual rule

An old proposal remains excluded when implemented with a different tactic,
generalized only cosmetically, moved to a nearby module, or newly compiled.
New validation is useful evidence but is not a new simplification idea.
For a retained proposal, identify the exact remaining obligation after the
nearest prior abstraction is assumed present, and charge every new helper
and compatibility bridge before reporting a source reduction.
