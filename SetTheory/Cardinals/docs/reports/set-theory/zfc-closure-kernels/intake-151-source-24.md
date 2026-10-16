# Batch 151 source 01 / local source 24: complete intake review

Accept this new manuscript as an addition to `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`, with its source preserved and the SK compiler input-domain correction below appended in reconciliation. It continues EPSC, equality elimination and complete implementation controls. No earlier repository claim requires retraction. It supplies neither a new sub-253 machine nor an internal ZFC machine endpoint.

## Provenance and review boundary

The original is `/tmp/zfc-intake-151-gkntyfry/zfc_consistency_proposal/zfc_minimal_theory`; it remained untouched. All local executable work used `/tmp/zfc-review151-source01-tfdq5cw4/package` or the independently copied SK directory documented below. The report audits ProveIt `2178c3885423f923021d4aaf1dbf52b4e2060837`; its requested earlier commits are `6d8bc7f1ba02c83e54757366f019f61b966ed0b7` and `63c83cf79986f8a92bb75460848a1d4f863b7b15`. The original 254 reference is pinned at `297ab8df7e5de329605c3875b4934643b371a5e3`, and the attributed public 253 reference at `0d544f2a2e3c18f12278441a74b7879f31cbe856`. The latter was open/unmerged at the author's inspection; this is historical provenance, not a claim about today's PR status. Mira-Cult, mira-emmy, Jeff and Wade retain their roles and the copied Wade MIT-0 license.

I read the entire main manuscript: `report.tex` and all seven sections, every theorem/proof, the bibliography, all READMEs, the supplementary SK proof, the delivered executable checks and their generated evidence. The SK source/tests received an additional independent read by the compiler agent. The review is ordinary mathematical/code review and finite execution, with no Lean or Coq build. Root independently checked all pages of the 28-page PDF. No checksum manifests, line endings or release-integrity checks were investigated. Hash-enforcement guards embedded in functional suites were bypassed in memory only; their exact bypasses are logged. Delivered sources were not repaired.

## Mathematical findings

**EPSC and the equality proxy (section 2).** EPSC keeps arbitrary first-order matrices and parameters, the empty-input initial condition and unrestricted support witnesses. It is an axiom schema, not a finite single sentence. The prior EPSC/PSC/hereditary-domain consistency comparison is cited as inherited ordinary work.

The false matrix gives an empty object. For a globally subset-bounded definable predicate, the constant-input matrix supplies an exact represented class: the empty object triggers closure, while support removes surplus members. This does not require Extensionality, literal functional uniqueness or choice of representatives.

Full incoming-and-outgoing observational equivalence O is an equivalence and a congruence in both membership coordinates by pure first-order reasoning. O(y,a) implies y is a subset of a. Exact classes for this predicate therefore yield exact O-singletons. Testing outgoing inclusion `E(a,b) := forall z, (R(a,z) -> R(b,z))` on the O-singleton of a gives O(b,a), and symmetry gives O(a,b). Conversely O gives E. This proof is noncircular: O and its singleton representation precede E. Incoming inclusion instead expresses subset inclusion and would not work. The four-node metric counts one quantifier, one implication and two atoms, excluding variable encodings and the logical engine.

The raw O quotient is set-coded, has a well-defined membership relation and transfers EPSC with actual equality by translating equality to E and using the quotient's surjectivity. This is equality of observational classes, not raw Extensionality and not the separate hereditary-domain interpretation of extensional ZF. Forgetting primitive equality gives the reverse ordinary consistency comparison. The counting proof that no finite structure has an empty object plus exact O-singletons for every object is valid: k observational classes need k distinct nonempty singleton profiles and an additional empty class. Finite diagnostics accordingly do not purport to be full EPSC models.

**Reserved falsity and proof transport (section 3).** The map shifts every source variable/binder by one, sends Bottom to `F=R(0,0)`, and expands equality as `forall 0, (R(i+1,0) -> R(j+1,0))`. The equality macro contains no translated Bottom and its endpoints are positive, so its local zero binder is safe. At an empty designated object (or, for local diagnostics, a false point) and with E=O, structural induction gives the stated satisfaction transport. Capture-avoiding substitutions lift by fixing zero and shifting every other index; noninjective substitutions are included.

Every source binder-producing rule, substitution and parameter closure must obey the lifted convention. Merely removing an instruction named GEN0 would not establish this. The supplied two-cycle capture counterexample and unrestricted-zero generalization counterexample correctly detect the two hazards. Arbitrary EPSC matrix payloads may themselves bind zero internally; this does not capture the wrapper's external falsity occurrence. The stated fresh-code arithmetic concerns the numerical frontend and must still be bridged to a complete operational enumerator.

The designated-refutation argument is correct for the specified source calculus and its line-by-line translated certificates. The reference translated checker is an abstract specification retaining source proof data. `proxy_kernel.py` implements formula translation, finite semantic diagnostics and an iterative prefix parser; it is not a complete executable proof checker. The numerical machine codec is also distinct from this prefix code. Bottom-free first-order consistency alone is unsuitable, since a one-point all-true relation is a model; designated-F derivability is the relevant target.

**Finite combinatory carriers (section 4 and proof_sketch.tex).** For a closed SK term P, universal SK equations plus `P != K` are consistent exactly when P is not convertible to K. Orthogonality gives confluence; K is normal; the closed-term conversion quotient is a set-coded countermodel when the designated terms differ. Basic bracket abstraction has the needed application property without eta. Primitive K in the halt branch matters: the basic abstraction of a lambda term extensionally equal to K need not reduce to literal K.

The Scott encodings, lookup and four tape cases implement the intended finite transitions. Finite halting traces reduce the emitted term to literal K. The converse uses the lambda interpretation, confluence and normal-order behavior of the fixed-point simulator: an infinite sequence of recursive calls cannot produce the head normal form of K. This is an ordinary construction for correctly validated machines, not a proof-assistant compiler certificate. The one-constant rules with `k=(o o)` and `s=(o (o o))` are likewise orthogonal; encoded codewords are distinguished from encoded applications. Every forward contraction from an encoded term is an encoded SK contraction, and global confluence prevents extra identifications via reverse-rule excursions outside the encoding image. No hidden extensionality is assumed.

The full payload includes the literal table and closed term, rather than an omitted DAG or external input. The emitted sizes reproduce, but an evaluator, parser/checker and blank initializer have no measured binary state cost. Its connection to the user's exact Con(ZFC) sentence inherits a separate machine calibration obligation. See the concrete generic-input defect below.

**Literal quotient and compiler controls (section 5).** The all-pairs separating-word certificate establishes injectivity of any strict action-preserving quotient of the literal 253 table with a distinct terminal image. The induction is on read words and does not require every word to occur along one actual tape run. This is not a lower bound for machines with the same blank halting behavior. Omitting row (0,0) admits precisely the indicated 0/2 identification, but blank execution uses that row, so the runtime-only quotient is not a 252-state blank machine.

The O-erasure controls retain cross-variable logical transport. Optional symmetry/combined variants have separate proof scopes: they are modelled with global IR and unrestricted GEN0, rather than being silently substituted for the pointed raw-EPSC interface. Propositional transformations deriving transitivity and combining the two membership-transport consequents are valid within that scope. The strict EPSC result is 288 states, not a new improvement. The state prices are actual generated tables; the varying dispatcher/framework costs are charged, rather than assumed fixed.

**Programme, scope and references (sections 1, 6, 7).** The report correctly separates ordinary calibration, finite tests, exact compiler controls, local formal results and the unfinished endpoint. Its proposals for proof enumeration, payload decoding and whole-machine simulation are open tasks. The paper does not establish Con(ZFC), an infinite computation, or a new minimum. Tromp's primary presentation confirms the basic bracket-abstraction clauses and Definition 3's K=00, S=01, application=1 convention; its nearby prose interchanges the atom labels, a discrepancy explicitly acknowledged by the supplied README. See [Tromp's primary PDF](https://tromp.github.io/cl/LC.pdf), pages 7–8. The artifact consistently uses the definition and states that convention.

## Concrete correction: accepted negative start

The theorem at `sections/04-combinatory.tex:125–132` says every finite table accepted by the compiler; the supplementary theorem at `experiments/sk_carrier/proof_sketch.tex:148–154` has the same domain issue. `build_carrier.py:243–264` validates transition labels but fails to reject a negative declared start. The accepted input

```text
#! start -1
1 0 0 R 1
1 1 1 R 1
```

halts immediately in the source semantics, since state −1 has no row. At `build_carrier.py:285`, Python's `states[start]` instead selects the final encoded state, here state 1. The compiled machine writes zeros and moves right forever. Thus the unrestricted parser-domain implementation claim is false. The ordinary construction is repaired by restricting to validated nonnegative start labels or rejecting such starts. The frozen public-253 input starts at 0, and all of its payloads regenerate exactly; it is unaffected. Previous source 13 supplied an abstract carrier specification without this executable parser, so no earlier repository statement needs retraction.

Independent SK dossier and reproducible counterexample:

- `/tmp/zfc-batch151-machines-ld5qdq5b/source01-sk-review.md` and `.json`.
- `/tmp/zfc-batch151-machines-ld5qdq5b/negative_start_repro.py`.
- `/tmp/zfc-batch151-machines-ld5qdq5b/negative-start.tm` and `negative-start-evidence.json`.

## Functional reproduction

All commands were run on copies with `uv run --no-project python`; the non-SK suites were executed through `run_functional.py` to omit hash-only guards in memory. The five default non-SK jobs and the independently copied SK job all passed. Full optional families were also executed:

| Check | Result |
|---|---|
| Profile/translation/prefix codec | 66,066 relations, 62,329 local singleton roots, 248,729 E/O comparisons, 51,968 translations, 32,767 words through length 14, 1,054 complete parses, both binder counterexamples detected. Exact frozen semantic evidence reproduced. |
| Eight fixed proxy recipes | All costs, symbolic words and formulas reproduced. |
| Full 264 compiler trials | All eight 33-trial families and every frozen histogram reproduced in 6.54 seconds. All 16 word/formula JSONs and eight named action maps equal the frozen artifacts. |
| Helper/literal audit | 405 scalar/push/offset and 144 base-three constructor cases; all original actions retained under totalization; all eight numeric action maps and label maps equal the frozen artifacts. |
| Quotient certificate | 32,131 complete-table pair words and 32,130 partial-table pair words independently replayed. Regeneration gives the same certificate/summary. Six functional certificate mutations are rejected for the expected semantic reason. |
| Bundled macro corpus | 187 cases; 70,968 moves; 505 observed runtime rows and all 253 states. Blank prefix adds the remaining row. |
| Full pinned-program macro census | All 8,391 cases; 2,849,408 moves, maximum 484 per case; same 505 runtime rows, 253 states and union 506 after the 312,975-step blank prefix. End state 33/head −17. This is finite coverage, not an arbitrary-state simulation proof. |
| SK checks | 101 complete halting runs, 72 boundary cases, 200 cyclic configurations, 300 literal-table transitions, 550 terms/360 one-constant contractions; both full/packed roundtrips. All supplied validation fields reproduce. |
| SK regeneration | All four payload files and metrics regenerate byte for byte: 128,181 tree nodes; 192,272 BCL bits/24,034 packed bytes; 302,419 one-constant bits/37,803 bytes. |

The full measurements' sole schema difference is a newly written `fixed_recipe_replay:false` metadata field, absent from the frozen output. This is not a cost/artifact discrepancy. No hash fields were compared. Strict EPSC has decision nodes 225 + framework 63 = 288. Other minima: CG strict 287 for both row orders; EPSC symmetry 289 for both; EPSC combined 288 for both; the other strict EPSC order gives 292. Framework costs range 62–64 and are included.

The six extra quotient mutations replace a word by empty/nonbinary text, remove a pair, change the exception list, change the maximum and change the histogram. All fail in the independent verifier at the intended check. An initial scratch harness-path error was corrected before these semantic mutation results were recorded; harness exceptions are not counted as certificate rejection.

Commands, timings and logs: `functional-jobs.json`, `additional-jobs.json`, `functional-comparison.json`, `table-functional-comparison.json`, `certificate-mutation-results.json`, `profile-replayed.json`, `full-macro-replayed.json`, `full-search/proxy_measurements.json`. The supplementary SK dossier preserves its own logs. All paths are under the two review directories cited above.

## Comparison with the present tree

The source pin is older than significant current Lean progress. At review head `65c776f4be6ca6ada7e1408ea2674e57c2770377`:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RawPSCProfile.lean:22` already defines `Full` as incoming sameness and outgoing equivalence; lines 25–29 define twin singletons, and lines 34–67 prove congruence and obtain those singletons from explicit closure instances. The report's short E-collapse can reuse this spine, but no existing theorem there supplies its complete EPSC formula adapter.
- `Computability/BusyBeaver/Research/ZFC/raw_psc.md:10` records the ordinary raw PSC calibration; lines 22–50 distinguish full-profile resources, hereditary incoming saturation and the still separate uniform interpretation. New EPSC/native controls since the paper pin are recorded at lines 263–286. These do not remove the report's full-schema/machine bridge obligations.
- `Computability/BusyBeaver/Research/ZFC/tarski_logic_layer.md:115` already proposes outgoing inclusion as equality in extensional models. Source 24 adds a raw-EPSC singleton proof and measured reserved-zero controls; the general proxy idea is related prior repository work. The note's unmeasured model/binder proposal and this actual pointed frontend must remain distinguished.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean:510` now derives `Tarski.classical`; line 518 proves unconditional `Tarski.complete`. The logical basis gap is closed for that named full calculus. `TarskiFalsity.lean:73` transports its rules to relative falsity, and line 184 gives completeness for bot-free targets/theories in irreflexive models. Neither is a proof of this report's reserve-zero compiler or its matrix enumerator.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NamedNumeric254.lean:37` now transports all named rules into the exact original numerical relation. Lines 56–73 define Q and prove its refutation equivalence and IR code 610. Q is explicitly the theory of encoded numerical theorems; its calibration with the set-theory schema/ZFC remains open. This finite adapter is not a theorem about the new 288-state tables.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NoQuotient254.lean` concerns the original 254 table. This report's independently verified 253 certificate is a different literal object and is not thereby Lean-certified.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Boot253.lean:958`, `Prefix330.lean:44` and `BootstrapFrame253.lean:106` now prove the full literal bootstrap, register prefix and whole-tape relation of their endpoints. This is stronger than the finite state/head census here, but still not arbitrary instruction simulation, enumerator correctness or an internal ZFC endpoint.

No earlier reduced-logic 248–252 candidate is rehabilitated: the existing typed countermodel status remains unchanged. The present complete 268-state retained-word control is still smaller than these new measured controls and larger than the attributed 253 reference.

## Actionable next step

A short new conditional Lean lemma can derive outgoing-inclusion collapse directly from the existing `RawPSCProfile.TwinSingletons`: choose the singleton of a, use reflexivity to place a in it, apply inclusion to b, then use singleton specification and symmetry. This isolates the actual new local proof. Connecting EPSC to that semantic resource, transporting all captured-variable operations through the reserved-zero frontend, certifying numerical decoding/enumeration and proving the binary compiler remain substantive independent obligations. No optimization should drop the cross-variable logical rows merely to lower the table count.

## Repository evidence map

The independent carrier review is preserved as
[intake-151-source-24-sk.md](intake-151-source-24-sk.md).
Its counterexample is `code/intake-151-negative-start.py`, with input
`data/intake-151-negative-start.tm` and result
`data/intake-151-source-24-negative-start.json`. Other reviewed JSON outputs
are preserved under `data/intake-151-source-24-*.json`. Scratch paths above
record execution provenance; use the offline recovery helper to recreate inputs.

The portable negative-start reproducer accepts the recovered package explicitly:

```sh
uv run --no-project python code/intake-151-negative-start.py --package /tmp/RECOVERY/24/zfc_minimal_theory
```

Run the command from this report directory, after offline recovery. It writes
only to a new scratch directory and independently reproduces the native halt
versus compiled loop's first transition. It passed again at intake.
