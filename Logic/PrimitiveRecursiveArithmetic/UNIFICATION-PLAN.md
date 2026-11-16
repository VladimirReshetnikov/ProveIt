# ProveIt iPRA unification plan

This plan covers the repository's published intuitionistic primitive recursive
arithmetic (iPRA) interfaces, reusable proofs, and the projects that consume
them. The baseline is commit `441e729baa`. The bridge and its two example
replays are checked at that baseline. The work below describes proposed
deliverables and their acceptance criteria.

## Target architecture

Use [ordinary ConciseIPRA](ConciseIPRA/Lean/ConciseIPRA/PR.lean) as the
canonical presentation for new portable iPRA statements and use
[IPRADerivations](Derivations/README.md) as the home for reusable object-theory
arithmetic proofs. A portable lemma should be usable under local hypotheses
and at arbitrary terms, or have an explicitly universally closed form.
Maintain one proof of each shared lemma and expose translated corollaries at
the symbols and judgments that consumers already use.

Keep Foundation's intuitionistic first-order calculus as the backend for
developments that use its model theory, syntactic arithmetization, or exact
published Foundation sentences. Keep ConciseIPRA's scalar calculus and
certificate checkers as the backend for concise proof research. Its ordinary
language `Prf PRAAx` is the shared interface. The scalar judgment `NPrf` and
the Foundation theory called `nativeTheory` name different systems. The
equivalences in [NativeBiInterpretation](ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean)
and [IPRAStandardTheory](../../Computability/DiophantineConsistency/Lean/DiophantineConsistency/IPRAStandardTheory.lean)
already serve their respective backends.

Layer imports so that ConciseIPRA and its arithmetic library build
independently of application proofs. The Foundation arithmetic syntax, axiom
schemes, and reusable logical transport should depend on Foundation and their
own arithmetic prerequisites. The bridge joins these layers. Clients that need
both can import a small bridge module and the specific arithmetic lemma.
Application endpoints, tables, polynomial data, coding-specific proofs, and
their replay drivers sit above that join.

`IPRABridge` imports Foundation arithmetic currently housed in
`DiophantineConsistency`. At baseline, the path through `IPRAStandardTheory`,
`IPRASuccessorInductionConverse`, `IPRASuccessorInduction`, and
`IPRAOpenDisjunctionWitness` reaches the deep witness development and
eventually `BusyBeaver.ZFC.WFTheory` and `ZFCinPA.ZFDelta1`. In the other
direction, `BusyBeaver.PA196.IPRAAssembly` already imports
`IPRAStandardTheory`. Check individual module closures before moving a
lower-level consumer. Imports from a leaf endpoint can start immediately.
Preserve public import names through forwarding modules when moving
implementation files.

## Baseline and migration scope

The [endpoint inventory](ENDPOINTS.md) records theorem types, data bindings,
and replay commands. The [dependency inventory](DEPENDENCIES.md) traces
the standalone and root source paths and the pinned providers.

| Area | Existing interface and evidence | Migration boundary |
| --- | --- | --- |
| [ConciseIPRA](ConciseIPRA/README.md) and [Derivations](Derivations/README.md) | `PR`, `PTm`, `Fm`, `Prf PRAAx`, and checked arithmetic from semiring laws and cancellation through order, bounded search and number theory | Use the ordinary calculus for shared statements. The scalar calculus, article, checker formats, and experimental size comparisons keep their own versioned interfaces. |
| [Bridge](Bridge/README.md) | `standardToConcise`, `conciseToStandard`, `conciseProvable_iff`, `standardOrderRoundtrip`, an additive-cancellation import, and the exact PA194 export | Extend capability at the level where a consumer needs it. The public theorem transports currently take closed sentences. |
| [BusyBeaver PA](../../Computability/BusyBeaver/Research/PA/README.md) | Published Foundation `standardTheory` endpoints, shared arithmetic and machine coding, and staged Lean replay scripts | Keep theorem names, exact consistency predicates, literal table bytes, halting semantics, proof assumptions, and replay provenance. Track external, conditional, and unconditional object-theory results separately in the migration inventory. |
| [BusyBeaver ZFC](../../Computability/BusyBeaver/Research/ZFC/README.md) | Literal K215 Lean/Rocq verification, alternative machines, and separately typed internal arithmetic endpoints | Reuse common arithmetic above pinned verification closures. Preserve the theory stated by each theorem. A K215 semantic replay and an internal PA or `IΣ₂` result provide different evidence. |
| [DiophantineConsistency](../../Computability/DiophantineConsistency/README.md) | Foundation standard and candidate iPRA, equality-only reference arithmetic, classical PRA and HA transfer, and audited object-level equation endpoints | Extract reusable arithmetic and transport theorems at exact equation and consistency boundaries. Keep provenance for the chosen variables, domain, coefficients, equation representation, and proof predicate. |
| [HilbertTenthProblem](../../Computability/HilbertTenthProblem/README.md) | `Diophantine` supplies Lean/Mathlib results on `ℕ`, including MRDP and universal-polynomial constructions | Treat these as mathematical and semantic dependencies. Build an object-language representation and two derivations for each concrete reduction selected for iPRA reuse. |
| [ZFCinPA](../Interpretability/ZFCinPA/README.md), [bounded PA consistency](../PeanoArithmetic/BoundedConsistency/README.md), [bounded ZFC consistency](../../SetTheory/BoundedConsistency/README.md), and [PA list coding](../PeanoArithmetic/ListCoding/README.md) | Foundation PA, related fragments, model-internal formula and proof coding, and the `PAListCoding.ExactTrace` interface used by H10 | Keep the exact theories and coded interfaces. Migrate shared arithmetic only at a recorded call site. Changes to coded provability require their own correctness and strength review. |

The tracked Lean import scan at the baseline places direct consumers of
`ConciseIPRA`, `IPRADerivations`, `IPRABridge`, and the
`DiophantineConsistency.IPRA*` modules in the three primary project areas
above. Phase 0 audits transitive consumers, nested Lean and Rocq packages,
scripts, and generated modules as well as explicit imports. Delivery archives,
frozen input bundles, and historical hash-bound replays enter through their
maintained indexes and release interfaces.

## Phases and dependencies

| Phase | Depends on | Reviewable deliverable |
| --- | --- | --- |
| 0. Inventory and reproduce | Existing checked bridge | Endpoint and dependency inventory with baseline replay receipts |
| 1. Specify names and split dependencies | 0 | Canonical interface guide and application-independent bridge prerequisites |
| 2. Complete formula and sequent transport | 1 | Foundation round-trip biconditional and public open-sequent transport for the needed contexts |
| 3. Share the arithmetic library | 1, with the relevant transport from 2 | Checked comparators and migrated arithmetic call sites |
| 4. Migrate consumers | 0 and the relevant slices of 2 and 3 | Parallel project pilots followed by incremental migration of proven endpoints |
| 5. Switch defaults and retire duplicates | Successful consumer and replay checks | Canonical docs and imports, documented compatibility, and removal of proven duplicates |

A closed endpoint export can proceed after its own baseline replay using the
existing bridge. Arithmetic comparison proofs and the formula round trip can
proceed in parallel once their import boundaries are known. A change to an
object-level proof coding is a separate work item under the strength and
encoding rules below.

### Phase 0 · Inventory and reproduce

- [x] Create a maintained endpoint inventory beside this plan. For each
  public theorem or proof family, record the module and declaration, exact
  judgment and outer theory, direction or biconditional, quantified variables
  and parameters, additional premises, input table or equation identifier,
  and check command. Record whether the result is a current-source Lake
  build, a staged replay with identified providers, an external semantic
  theorem, a conditional derivation, or open work.
  The [endpoint inventory](ENDPOINTS.md) covers the bridge and arithmetic
  proofs, the PA variants and scheduler boundary, the BusyBeaver ZFC
  clients, the maintained equations, and the adjacent provider APIs.
- [x] Trace source imports, standalone package manifests, generated import
  headers, and staged `LEAN_PATH` receipts. Use `git grep` over the Git tree so
  the inventory covers sparse checkouts. Start from `ConciseIPRA`,
  `IPRADerivations`, `IPRABridge`, and the Foundation iPRA modules. Follow
  actual import edges rather than inferring them from mentions of PRA or iPRA.
  Identify forwarding modules, old versions used only as replay inputs, and
  duplicate module names across providers.
  The [dependency inventory](DEPENDENCIES.md) records the parsed import
  scan, the generated table provider checks, and the ordered pinned replay
  scope. It also records the input comparison for the literal K215 lane.
- [x] Capture reproducible baselines for the bridge, PA194 exact literal
  endpoint, one ZFC equation endpoint, and representative arithmetic modules.
  Record toolchain and package revisions, theorem types, axiom audits, source
  and resolved object hashes for staged builds, and cold and warm time, peak
  memory, and disk usage. Record checkpoint provenance when the build relies
  on a staged provider.
  The [endpoint receipts](ENDPOINTS.md) give the fresh and warm measurements
  and record the package and checkpoint providers used in each run.
- [x] Identify the direct and transitive import closures for standalone
  BusyBeaver and the ProveIt `Diophantine`, ConciseIPRA, and Foundation
  targets. The [dependency inventory](DEPENDENCIES.md) records the
  closures and the archive indexes. The [endpoint inventory](ENDPOINTS.md)
  maps active consumers to their verification commands.
- [ ] Review the inventory with the affected project maintainers. Record
  their review of the import and archive boundaries, active proof judgments,
  and verification commands. The inventories contain the implementation and
  replay evidence for that review.

### Phase 1 · Specify names and split dependencies

- [x] Publish a short interface guide in [Bridge](Bridge/README.md) with
  canonical names for ordinary iPRA judgments and shared lemmas, explicitly
  qualified names for backend theories, and examples for selecting a closed
  statement, an open proof, or a translated Foundation corollary. Use
  `standardTheory` for new Foundation iPRA endpoints. State the precise
  theory when discussing `nativeTheory`, classical PRA, HA, PA, or fragments
  such as `IΣ₁`.
- [x] Separate Foundation's finite PR codes, language, defining equations,
  quantifier-free syntax, and generic intuitionistic proof transfer from
  ZFC/PA equation and machine modules where the dependency graph permits.
  Start with the smallest importable slice and keep old module paths usable
  through forwarding imports. Preserve declarations that affect exact syntax
  or pinned builds. Where a transfer proof pulls in a heavy application
  closure, isolate its arithmetic obligation. First trace the generic helper
  calls used by `IPRASuccessorInduction`. Start with
  `IPRAReferenceCloseFamily.closeFamily` for generalization and the
  closed add-one and symmetry lemmas in `IPRAAddOneDirect` and
  `IPRAEqualitySymmetryGG` for instantiation. Expose a small target for
  the `standardTheory` statements and keep the native equivalence
  available through its old import. Check whether the standard transport
  can go directly through the equality-only reference axioms.
  The [smaller syntax providers](Bridge/README.md) and the standard axiom
  layer now have independent imports. The bridge goes through the
  equality-only reference proof rules, and the PA replay checks keep the
  original declaration owners when loading pinned objects.
- [x] Keep syntax translation, reference proof transport, standard Foundation
  transport, and application examples at separately importable boundaries.
  Keep the root and standalone Lake build targets usable on their existing
  toolchains. A lightweight Concise arithmetic import should remain
  independent of Foundation, `BusyBeaver`, and `DiophantineConsistency`.
  The normal root bridge targets and the standalone BusyBeaver package
  both passed. The portable library has its own source closure gate.
- [x] Check representative old imports after each move, inspect import cycles
  and transitive application imports. Add a focused closure check for the
  extracted core that excludes BusyBeaver, ZFCinPA, bounded-consistency
  endpoints, and polynomial certificate data. Compare baseline replay costs
  and document any purposeful dependency change.
  The [dependency inventory](DEPENDENCIES.md) and
  [endpoint receipts](ENDPOINTS.md) record the closure and the checked
  root and pinned provider paths.

### Phase 2 · Complete formula and sequent transport

The baseline included the exact Concise-to-Foundation-to-Concise round trip
and Foundation's provable order-erasure biconditional. The
[closed reflection theorem](Bridge/Lean/IPRABridge/FoundationNormalization.lean)
now also reflects provability of every original Foundation sentence through
its Concise translation.

- [x] Prove an object-level extensional equality between each Foundation PR
  code and its round-trip image, at arbitrary parameters. Use the defining
  equations for the positive-arity zero case, the unchanged successor and
  projections, and substitution and congruence for composition. In the
  primitive-recursion case use quantifier-free induction on the counter with
  all remaining parameters in scope. A proof about the evaluator on Lean's
  `ℕ` is a separate test of the implementation. Use the existing exact
  Concise PR code round trip to show that Foundation code normalization is
  idempotent.
- [x] Lift code equality to term equality and then to a provable biconditional
  for formulas, including equality atoms, implication, both quantifiers, and
  arbitrary parameters. Combine with `standardOrderRoundtrip` for primitive
  `<`. Derive the following public theorem shape and test it on nested
  recursion containing an arity-positive zero and on a quantified order
  sentence.

  ```lean
  (standardTheory ⊢ φ) ↔ Prf PRAAx [] (toConciseSentence φ)
  ```

- [x] Expose standard-theory transport for explicit finite open contexts. Use
  [the existing reverse environment theorem](Bridge/Lean/IPRABridge/ConciseToFoundation.lean)
  and [Hilbert transport under free-term assignments](Bridge/Lean/IPRABridge/FoundationToConcise.lean).
  Specify how the context, free variables and bound indices map. For
  preservation, allow arbitrary term assignments. For reflection, assign
  the finitely occurring free variables distinct fresh indices so the
  translation retains their identities. Check substitution, weakening by
  adding hypotheses, and closing and reopening a sequent. Make the
  existing closed interfaces corollaries where this simplifies their
  implementation and preserves their theorem types.
- [x] Test an open sequent with two hypotheses at nonvariable terms, an
  induction instance with a parameter that stays in scope under a binder,
  and existential elimination with a fresh variable. Include both directions
  and reuse a translated theorem under a destination theory's local context.
  Review every axiom image and verify the resulting object derivations.

### Phase 3 · Share the arithmetic library

The [arithmetic symbol table](Bridge/SYMBOLS.md) records existing checked
comparisons, including Foundation addition, multiplication, predecessor,
truncated subtraction, and strict order.

- [x] Make a symbol and theorem correspondence table. Start with zero,
  successor, numerals, addition, multiplication, predecessor, truncated
  subtraction and order. Extend it on demand to comparison bits, bounded
  search, division with remainder, pairing, sequence coding, and finite
  sums/products. Record arity, recursion argument, argument order, the
  current consumers, and the Lean theorem used to rewrite between
  formulations. Mark entries as definitionally equal, provably equivalent,
  or needing a comparison proof.
- [x] Prove the first nontrivial comparisons at arbitrary terms in the object
  theory. Include Foundation `addCode` as well as `addCore`, the analogous
  multiplication aliases, and Foundation's `ltBitCode = 1` versus
  ConciseIPRA's truncated-subtraction order. Include strictness at equal
  arguments and at zero. For division and bounded search, specify the
  zero-divisor and failed-search conventions before identifying symbols.
  Retain the existing
  [cancellation check](Bridge/Lean/IPRABridge/Checks/Arithmetic.lean) as a
  direct-match regression test.
- [x] Migrate one arithmetic client in BusyBeaver PA and one in
  DiophantineConsistency from a parallel local lemma to the shared proof.
  Suitable first families are a successor/addition identity, an order
  comparison used in a bounded loop, and a bounded-search contract. Pick
  actual call sites from the inventory and keep the previous public
  Foundation statement as a checked corollary. Verify reuse under an
  arbitrary parameter environment before consolidating a local proof.
  The checked uses of `not_succ_le_self` are the literal PA1944L endpoint
  and the explicit ZFC equation, both through the exact `subCode` inequality
  and the original universal Foundation statement. The
  [endpoint receipts](ENDPOINTS.md) identify the production proof paths.
- [x] Repeat in dependency order. Prefer the smallest shared lemma set
  demanded by the next clients. Keep PR programs, proof predicates, and
  reduction-specific arithmetic local when their statements depend on those
  definitions. Completion for a lemma family means one maintained proof,
  comparison lemmas for the supported vocabulary, and checked public
  corollaries for its existing consumers.
  After the subtraction and zero-test pilots, the finite selector now
  shares the portable search proof. The native equality path also shares
  the portable successor and subtraction proofs. Both exact ZFC exports
  and the literal PA1944L replays passed with these changes.

### Phase 4 · Migrate consumers at their verified boundaries

| Project | First changes | Acceptance before expanding |
| --- | --- | --- |
| BusyBeaver PA | Keep the primary PA194 export as the reference client. Migrate shared arithmetic in one distinct checked PA194 variant and reuse it through the exact published Foundation endpoint. For PA195 and PA196, start at the strongest theorem actually present for each table, such as a command-level equivalence or one object-theory implication. | Reproduce the exact PA194 formula in both systems with its original table, blank start, and PA refutation predicate. Compare a second literal table independently. Preserve directions and premises for PA195/PA196 and label their provenance. Add a new equivalence export when the corresponding literal object proof is available. |
| BusyBeaver ZFC | Inventory existing object-theory endpoints separately from the K215 Lean/Rocq semantic proof. Migrate a common clock, order, or bounded-run lemma where a precise iPRA judgment is already available. If a proposed endpoint belongs to a stronger theory, first identify the iPRA sublemmas it actually uses. | Replay the pinned K215 verification according to its maintained guide when its inputs change. Preserve exact bytes, witnesses and checks of the endpoint used. Type-check the parallel migrated object lemma in its stated theory and keep any separate PA or fragment theorem as a distinct entry. |
| DiophantineConsistency | Export `IPRAExplicitZFCFinal.standard_equivalence` through the bridge. Select a second exact, audited maintained equation client from the inventory, such as `IPRANineCurrent.standard_equivalence`. Use a shared arithmetic lemma in one proof supplying a reduction obligation. | Replay the chosen Foundation proof and Concise export with the same object-language consistency sentence, exact equation and positivity/domain conventions. Preserve the rank, coefficient and variable conventions of any certificate. Keep any published Lean/TeX/PDF alignment at its documented check level. |
| HilbertTenthProblem | Select a small concrete configuration or polynomial gadget used by one consistency reduction. State the exact represented graph and its witnesses and formalize the two open or closed iPRA directions needed by that client. Put the adapter downstream of `Diophantine` in the consuming project. | Build `Diophantine` independently and replay its MRDP axiom audit. Keep its existing isolation from Foundation's conflicting `Matrix` lemmas. Check the new iPRA statement and witness translations at its use site. General internal MRDP can proceed as a separate project if a client needs that stronger interface. |
| Logic and coding clients | Preserve the exact exported PA and ZFC arithmetization and interpretability APIs. Add a thin comparison only at a confirmed call site. Let new arithmetic contributions target the portable interface and let scalar-checker work keep its own verification commands. | Rebuild the affected coding endpoint in its actual theory. For a theorem about all model-internal codes, the check quantifies over the ambient model, including nonstandard inputs. Record which proof encoding and compiler the endpoint uses. |

For exact work on these boundaries, start from the
[PA194 replay](../../Computability/BusyBeaver/Research/PA/verification/pa194/ipra/native-endpoint/README.md#conciseipra-export),
the [PA195 iPRA record](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa195/ipra/README.md),
the [PA196 iPRA record](../../Computability/BusyBeaver/Research/PA/verification/other-machines/pa196-vs-u208/ipra/README.md),
the [K215 verification record](../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md),
the [ZFC equation proof plan](../../Computability/DiophantineConsistency/IPRA_PROVABILITY_PLAN.md),
and the [MRDP proof guide](../../Computability/HilbertTenthProblem/Lean/MRDP.md).

### Phase 5 · Switch defaults and retire duplicates

- [x] Give new shared lemmas and public examples canonical imports. Document
  how each project obtains its backend statements, including one example
  for closed transport and one for a sequent with hypotheses. Let existing
  public endpoints use their translated proofs without changing the formulas
  or output interfaces that reproduce them.
  The [bridge guide](Bridge/README.md#choosing-an-ipra-interface) gives the
  open and closed forms. The native selector, literal PA and equation
  replays, and the C222 and C254 evaluator checks cover their existing
  published interfaces.
- [x] For each proposed removal, list its active callers, forwarding import
  or theorem alias, replacement proof, and regression check. Remove duplicate
  implementations only when their two logical interfaces, exact published
  theorem types, and reproducibility requirements are covered. Preserve
  reference-cited historical paths through immutable objects or explicit
  compatibility, depending on how they are used.
  The [forwarding inventory](ENDPOINTS.md#forwarding-imports-and-shared-proofs)
  records the signum and native equality replacements, the other forwarded
  proofs, and the corresponding current and historical checks.
- [x] Review the endpoint inventory for coverage. Each active consumer should
  have a verified migration or a documented backend boundary and checker.
  Close the migration after the targeted checks, standalone builds and
  retained replay commands pass, and after the dependency scan confirms that
  portable arithmetic remains independent of application imports.
  The [endpoint inventory](ENDPOINTS.md) records the checked bridge, literal
  PA endpoints, exact equation exports, C254 proof path and coding clients.
  The standalone BusyBeaver smoke build, independent H10 library and MRDP
  audit, exact Pell use-site checks, and portable import gate passed.
  Historical replay evidence remains tied to its recorded providers.

## Proof strength, exact statements, and provenance

- **Object judgment.** For each theorem promoted as iPRA, require a checked
  judgment in `Prf PRAAx` or `standardTheory` with the needed context.
  `#print axioms` audits Lean's metatheory separately from the object
  axioms. Inspect both the conclusion and the assumptions. A Lean theorem on
  standard natural numbers, a classical PRA proof, and a proof in HA or PA
  supply their respective interfaces.
- **Proof encodings.** Keep the literal machine, predicate, input convention,
  and equation constants fixed while changing a proof's backend. If a
  project proposes replacing a Gödel numbering or proof predicate, specify
  total translations and their preservation of valid proofs in each claimed
  direction. Prove the needed correctness internally in the weakest claimed
  base theory, at arbitrary coded inputs, with the formalization covering
  nonstandard models when the statement ranges over them. Derive a
  biconditional between the two advertised consistency sentences under that
  base before changing a public endpoint. Metatheoretic proof transport
  supplies a different contract.
- **Executable certificates.** Preserve the byte format and size baselines
  of existing scalar and machine checkers. If a shared certificate format
  is needed, version its codec, prove checker soundness for the canonical
  judgment, and prove the translation obligations for existing certificates.
  Replay accepted fixtures and confirm unrelated or malformed certificates
  are rejected. Measure serialized sizes with the original settings when
  reproducing prior comparisons.
- **Bounded formulas.** State the quantifier-free characteristic formula
  used for induction and prove its connection to any bounded formula with
  literal quantifiers. Check arbitrary parameters, substitution and the
  clauses at zero, successor and the bound. Use Lean's classical facilities
  to construct or check proof objects only through a justified object-theory
  inference.
- **Replay.** Keep source-current builds and historical staged replays
  attributable to their inputs. Preserve provider precedence, resolve
  duplicate module names explicitly, and check matching
  `.olean` companions and recorded hashes before reuse. An existing cached
  success can serve as baseline evidence with its provider receipt.
  Updates to a module path or object build require a fresh matching replay
  for any guarantee tied to that module. Leave upstream Git submodule
  revisions, archived delivery contents and Rocq certificate formats pinned
  unless a separate change has its own review.

## Verification routine

Use the root [Lean workspace instructions](../../README.md#lean-workspace).
The iPRA libraries have opt-in targets. Run relevant commands serially.
Stage-heavy PA and ZFC checks use their published inputs and commands.

```sh
lake build +ConciseIPRA.NativeBiInterpretation
lake build IPRADerivations
lake build +IPRADerivations.Checks.Axioms
lake build IPRABridge
lake build +IPRABridge.Checks.Arithmetic
lake build +IPRABridge.Checks.ComparisonBits
lake build +IPRABridge.Checks.BoundedSearch
lake build Diophantine
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
```

For PA, run `check-literal.sh` and `check-concise-export.sh` from the
PA194 replay guide with their ordered pinned providers. Check
`+BusyBeaver.PA196.IPRAAssembly` if changing shared PA interfaces, and
smoke-test the standalone BusyBeaver Lean workspace if moving a dependency.
For the ZFC equation pilot, build
`+DiophantineConsistency.IPRAExplicitZFCFinal` and replay the chosen
source and object receipts. For the current 14-variable endpoint use
`+DiophantineConsistency.IPRAStandardCurrentEndpointChecks` and
`+DiophantineConsistency.IPRAReferenceCurrentEndpointChecks` when their
stated providers are available.

For a first migration change, add small Lean checks with named public
statements for the new contract and explicit `#print axioms` for theorems
crossing a backend boundary. Flag added axioms such as `sorryAx` or
`Lean.ofReduceBool` in migrated proofs and review any existing documented
trusted computation separately. Reproduce the affected old and new imports.
Reviewers need the exact commands, inputs, proof assumptions, and outputs
for each changed endpoint. Use focused checks on each change and run the
larger staged replays when a dependency or published claim changes.
If a replay exceeds the baseline resources, record the size of the closure
and the failing stage before deciding whether to shrink the import, split
the proof, or update the checkout instructions.

Track each implementation change by module, prerequisite, proof or replay
deliverable, and reviewer. Review changes to transport with the Logic
maintainers, changes to endpoints with the relevant project maintainers,
and changes to build or replay inputs with the owners of those checks.
Keep a consumer's existing import and proofs available until its own gate
passes, so that a failed migration can be reverted independently.

The first implementation series can be reviewed in four changes.
Inventory the endpoint types and record the existing replays. Isolate one
cycle-free Foundation arithmetic slice with a compatibility import. Add a
comparison between two real arithmetic symbol definitions and migrate one
call site. Then export the selected ZFC equation theorem and record its
exact statement and provenance. The full Foundation round trip and open
sequent transport can advance in parallel with the closed exports.
