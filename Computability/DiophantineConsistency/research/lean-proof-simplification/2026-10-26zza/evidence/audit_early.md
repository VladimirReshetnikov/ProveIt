# Novelty exclusion audit: packets a through m

Snapshot: `96520cd1a5179f470b4da127bd47bc26a8d808ff`.

Scope: `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26a` through `2026-10-26m`. Primary reports were read/scanned in full; their heading inventories and exact text are available in the shared repository. Packet m contains a detailed 57-family audit of a–h and earlier incoming material, at `2026-10-26m/audit/novelty_audit.md`. Packet l additionally includes ancillary-note exclusions. Status is irrelevant to the user's novelty condition: proposals, optional directions and uncompiled sketches count as already applied.

## Early foundational exclusion map (a–h)

The following mechanisms are all prior work. The E identifiers match packet m's detailed audit and provide an exact lookup into that source.

| IDs | Prior mechanisms | Main targets |
|---|---|---|
| E01–E03 | Core list lookup/membership reuse; congruence through `Nat.rec`; assignment naturality and witness-block splitting | Annotated checker/rename/bound; PRCode; Representation/QuarticCompiler |
| E04–E07 | Generic finite sum-of-squares zero and degree criterion; `Sum.exists_sum` regrouping; generic residual cost bound; weight-one syntax degree reuse | DAGQuartic; NaturalDAGQuartic; QuadraticRegisterSystem |
| E08–E14 | Existing power certificates; local node equation specialization; shared topological invariant; commutative node correspondence/simulation; register append invariants; indexed/typed circuit facades; identical 99-node tail extraction; semantic blocks and preserved cutpoints; shorter register rewrite lists | Split/Gap circuit families |
| E15–E18 | `Nat.rec`/iteration bridge, terminal-state laws, encoding fusion; guarded history folds with different row/judgment types; exact 0/1 checker values; tag dispatch; code-valued PR iterator constructor | Annotated scanners/checkers/contexts |
| E19–E20 | Option-map decoder proof shortening, decode/depth fusion; parse-then-check composition; partial-decoder left inverse gives injectivity | AnnotatedProofCode; AnnotatedParents |
| E21–E25 | Exact half-radix quotient/remainder identity; weaker congruence from divisor modulus; full cyclic-field residue/support interface; exact carry equation derives recurrence; conditional padding witness | Cyclic rotation/carry; current clauses/window/padding |
| E26–E32 | Coefficient envelope schema and finite majorant certificates; coefficient naturality/common syntax; arbitrary collisionful finite-fiber pushforward; origin correction and mask blocks; checked finite chunk assembly, including final partial block; four-direction packed layout; Word/Fin/ZMod/padded-list bridge | Native coefficients/digits; Wang tables |
| E33–E36 | Small staged native facts; aligned-cell/geometric facts; coherent source/window witness; lower base interface below completeness | Current native layers |
| E37–E42 | Nine-coordinate packing; named long-conjunction accessors; parameterized Split/Gap degree profiles; source-register arithmetic/cast boundary; guarded existence transport (not bijections); elementary residual row operations | Source and carrier families |
| E43–E46 | Definable internal induction transport; model-validity/completeness/sealing helper; common ZFC-model-to-ZF-axioms bridge; finite quantifier and arity normalization | Object arithmetic/syntax/sealing |
| E47–E53 | Common guarded DivMod certificate; local positivity/canonicality proof compression; integer-unit library facts, common constructor branches, whole-conclusion Pell casts; finite-set intersection and sum-at-most-one APIs; predecessor powers and symbolic huge powers; remainder/cast cleanup; convolution sum distribution and finite-switch cleanup | Register/quadratic arithmetic; carriers; finite digits |
| E54–E57 | Parameterized direct/native graph builders preserving cost models; sparse low-degree reflection; generic semiring compiler specialization; audit/import/certificate engineering | Graph enumerators/compilers/checks |

Additional exclusions explicit in ancillary notes or later early audits:

- An aligned-cell equivalence with `ZMod`, including the nearby additive-equivalence strengthening, is already proposed (i report explicitly rejects it as too close).
- A semiring witness for object evaluator totality, then uniqueness to characterize `evalRel`, is already suggested in prior notes (l report excludes its own attempted refactor on this basis).
- Cancellation-aware polynomial degrees and preserving code/data/witness-cost equalities are existing constraints, not independent new proposals.

## Additional exclusions introduced by i–m

| Packet and section title | Mechanism already proposed | Concrete targets |
|---|---|---|
| i: Preserve rational roots when descending to integers; m: Preserve the exact rational root during integral descent | Prove the denominator of the already chosen rational root equals one; retain its sign/relations; share separated finalizer theorem below two clients | NearSquareFinalizer; MarginFinalizer |
| i: Decompose the product's units once | Recursively decompose `IsUnit` of a product, then integer unit alternatives instead of separately constructing complementary products | ShortSystem |
| i: Describe the tree decoder by its exact graph; j: Fuse syntax-decoder correctness into one graph theorem | Simultaneously prove re-encoding equality and fuel/depth bound, derive projections and exact success iff; `Option.bind_eq_some_iff` avoids impossible failure cases | AnnotatedProofCode.Tree |
| i: Use finiteness to recover an invariant predecessor; l: Use inverse invariance of a finite set | Finite injection restricted to forward-invariant predicate becomes surjective; inverse predicate transport replaces orbit/period proof | NativeFieldCycles2011; offset-19 exclusion |
| i: Prove the support envelope before individual coefficients | Establish global univariate degree bound first and derive coefficient vanishing rather than duplicating support arithmetic | SelectiveCarry |
| i: Rotation is convolution with a point mass | Specialize existing convolution at a Dirac/impulse word rather than prove a rotation sum separately | NativeCyclicRotation |
| i: Automate extensional primitive-recursiveness composition | Register `Primrec` as a compositional function property and automate via existing closure lemmas, distinct from code construction | Computability |
| i: Canonical normalization from a finite maximum principle | Compare bounded carry solutions by maximal discrepancy, then recover unique digits/carries given exact normalized word and boundary conditions | NativeCyclicCarry/window layers |
| j: Treat Pell sign ambiguity as a compositional relation; k: Make congruence up to sign compositional; m: Compose congruence up to sign as a relation | `a ≡ b or a ≡ -b` transitivity/symmetry/sign-product transport; no quotient-witness reconstruction | NativePellStepDown; SignedPellResidue |
| j: Constructor views and one internal unique-existence induction | Known-constructor graph elimination views; strengthen internal totality/functionality to one definable `exists unique` induction | ObjectBoundStep/internal code graphs |
| j: Preservation and fusion for internal recursive graphs | One reusable graph-iteration preservation theorem based on seed/step closure; fusion under a commuting map; retain definability of the exact invariant | Object `ThetaG`; three naturalness/code clients |
| j: Synthesize representation-depth bounds with small certificates | Certificate `(required baseline, excess depth)` with max-plus composition; build proof-producing traversal respecting let sharing | BoundedForallDepth, factorial/product/finiteRep |
| j: Explicit cyclic carries | Explicit least/greatest cyclic carries from rotated weighted sums, positive remainders, telescoping, and full two-solution classification; budget selects least witness | NativeCyclicCarryWord |
| k: Use the existing finite-support classification | Reuse existing finite support classification instead of enumerating support again | Native support exclusions |
| k/l/m: Reuse the exact Pell parity theorem/odd-index theorem | Replace local proof that a base-divisible Pell x-coordinate implies odd index with existing `odd_index_of_base_dvd` | NativePellStepDown |
| k/m: Derive inverse graphs from a product equivalence/existential projection | Obtain first/second inverse pairing graph specifications by projection from a pair equivalence, and normalize finite witness tuples separately | PairingRepresentation; QuadraticNatPairing; RegisterNatPairing |
| k: Share the positive-denominator Euclidean certificate | Identical `DivMod` specification across quadratic and register backends; uniqueness extension under positive denominator | QuadraticDivMod; RegisterDivMod |
| k: Factor the arithmetic budget behind composition | Small reusable numerical composition budget, revealing an unnecessary hypothesis; distinct from degree abstraction | Representation budget modules |
| l: Remove two specialized inductions | Use internal `nat_zero_or_succ` because the old step ignores induction hypothesis; delete private defining formulas/specifications | ObjectAdditionCancellation; ObjectNaturalZero |
| l: Keep divisibility witnesses abstract | Compose `dvd_add`, `dvd_sub`, `dvd_neg` instead of constructing quotient witnesses in Pell sign cases | NativePellStepDown |
| l: Compare Pell bases instead of exponentials | Simultaneous x/y monotonicity in base parameter followed by strict index monotonicity | NativePellFirstIndex and related comparisons |
| l: Prove the norm fact entirely over the integers | Square-root divisibility and nonzero-square cancellation remove rational-square detour | Integer nonsquare norm arguments |
| m: A uniform small-ordinate criterion for Pell minimality | General criterion for positive Pell solutions with y = 1,2,3, using classification/least ordinate instead of discriminant-specific proof | NativePellBootstrap fundamental unit |
| m: Consume the Boolean certificate before constructing a conditional | Expose quadratic Boolean graph specification before conditional graph assembly; preserve all representation data | Quadratic Boolean graph consumers |
| m: Recognize the physical permutation as a positive tail | `Fin.cons` zero-head/positive-tail injection replaces manual Fin cases | WangTiles942 physical positions |

## Caution for the current report

Do not claim a novel idea merely because an early prototype was uncompiled, not adopted, or covered a slightly different client. The user explicitly assumes all those ideas have been applied. A credible fresh proposal must explain its residual benefit after these abstractions and local refactors exist. Likewise, a helper that is just the same proof with one more parameter does not clear this bar.

## Possible unexplored search directions (not yet endorsed as novel)

The early packets leave untouched many concrete arithmetic witness-generation proofs, but later packets may cover them. Candidate searches should concentrate on exact source lemmas with no semantic match in the entire a–zq corpus, e.g. redundant completeness/soundness strength in very recent machine/tile endpoints, factorization through existing finite-support equivalences, or a newly added module absent from all packet baselines. No fresh headline recommendation is asserted solely from the a–m audit.
