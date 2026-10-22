# Contracts and shared implication review: arrivals 02, 04, 06, 08

This is an independent ordinary mathematical/source review, not a fresh proof-assistant run. The four main reports and their relevant Lean changes, clients, and submitted receipts were read. No delivered program, proof compiler, producer, or research search was executed. `compare.py` is our own read-only parser/hash census. All 510 extracted members match the root intake inventory; no canonical source or Git state was changed.

The preliminary independent phase11 saved-reader check passed with current repository source comparison. Its separate receipt is `/tmp/k215-phase11-publication-peer/saved-review.json`, SHA d0801a9d9924b03f32a14f21f9447a0faa60dd960f4e560de65532ac8c9ed724. That historical check is not evidence for any incoming replacement.

## Recommendation

The clearest immediate mathematical simplification is the shared unrestricted/dominated basis in 06/08. Reuse the maintained dominated proof with `below := True`; expose its existing K and Peirce instances and derive S with five further MP applications. This removes Lukasiewicz's independent proof. Retain current phase11's two inlined aliases, all retained public signatures, the unchanged numerical adapter, and the exact Tarski tail. Use a reviewed successor of the strict maintained producer rather than copying either package's older whole producer over current files.

For the runtime, 08 supplies the cleanest reusable interface: `SiteContract M entry Q e` parameterizes the actual entry configuration, and `SiteSpec` packages the common path bound. Its `prepend` lemma composes exact decoder prefixes with positive suffixes. Combine that design with 02's concrete suffix attachment, rather than adopting four parallel variants. 04's explicit mixed-coverage theorem and 06's exact-leaf constructor are small useful conveniences. None removes complete site obligations yet. A first real selector, such as the held CB1 family, must prove its complete prefix/primitive/return contract before an old check is bypassed.

The newer origin change `e79d52decb` (present in `88c8114d21`) is a valid competing simplification: it replaces the old 107-helper Lukasiewicz proof with a separate 56-step proof. It is not the shared-basis refactor and should not be described as stacking additively with it. The shared route supersedes that second derivation while preserving its source/history as research.

## Exact arrivals and baseline

| Packet | Arrival SHA-256 | Members | Main focus |
|---|---|---:|---|
| 02 Proof Contracts | 05e057ab70390a7a8b90d1ac815ebe112b6f85090007525b44baee68ba43e5f1 | 146 | Semantic simulator, real prefix/suffix attachment, generic Rocq rendering |
| 04 Proof Simplification | 32c128cc37784ef8f86accad9ddee163cbe700e194f6c32268ced1f918c6a3ae | 172 | Semantic/mixed coverage, generic Rocq rendering, reachability screen |
| 06 Shared Proof Core | e8aff5052f8734b7dc90c8754171f1d09e5f3f11ec4186544eb154ea2e909081 | 137 | Shared K/S/Peirce basis, separate pure basis module, semantic coverage |
| 08 lower-case proof simplification | c47f6c0ab71d92bb68af29841b13f352fa0782349169de0017f2e5221ca6aadd | 55 | Shared basis, entry-parameterized semantic contracts, diagonal obstruction |

The reports use 2ca3a5c16f or 6f0d42d368. Our comparison uses current KSim SHA 3904e060d4ed082c2b7c0db56ebd820cab4d123a20b8f1ef387eee814fc7c2df, current phase11 generic core a128ddd54eebe7a49f75ea25c513c6229f1304fb51a9d9b07539a89b8a094656, and the still-maintained old Lukasiewicz 5bae5186d702414adc6f1f7006d241a48ef9f24e53de48c90f84394ce3c500d3. The reports' generic core e91f5cf8 is the raw58 predecessor of current a128; it must not silently replace the two accepted inlinings.

`comparison.json` pins the incoming sources, member counts, old/new definition and header comparisons, exact Tarski tail, and current 197-module reverse-import census. Its explicit-source header comparison does not itself elaborate implicit section parameters; submitted typed clients are read separately.

## Semantic contracts: common sound argument and important differences

All four implementations preserve the 15 original KSim definition bodies, including all executable functions, and the 22 original explicit theorem headers after comments/whitespace normalization. The existing `Covered` remains available. The old `sim_step`, `sim_halt`, and `halts_iff` become wrappers around one semantic simulation. `sim_stop` retains its independent short structural proof, so its old type does not acquire `BoxLemmas`.

The new semantic hypothesis must quantify over each actual source walk, its returned primitive and consumed length. It uses `consume P d`, including implicit zero padding, not an arbitrary representative word. Every returning branch quantifies all natural gap values and all register lists satisfying the old `Valid` predicate. Increment retains its spare extension; decrement has two separate zero/nonzero contracts; every target retains the exact path, physical register map, gap/growth, and overflow expression. An internal `.node` is false as an executable edge. The common length bound is 48 and the logical register bound is 9. The code does not replace a complete tape contract by a state-only or register-only assertion.

The reverse halting argument is the old strong induction on physical time. Each simulated source step consumes `j+1`, so after determinism aligns the physical run prefixes, the remaining time is strictly smaller. Dropping positivity would be invalid: a source self-loop can be zero-step-related to an already halted target. Packet06 includes a small exact Lean counterexample (`explanatory/ProgressBoundary.lean`), whose source proof is sound. Positivity is needed for the complete returning edge; a decoder prefix itself may have zero length.

There are two legitimate halt interfaces. 02's `HaltPortSpec` and 06's `ReachesTerminal` give a reachable complete configuration with q=230, leaving terminal rows to the eventual halting theorem. 04's `HaltContract` and 08's `.halt` contract directly promise halting conditional on both state-230 rows being absent. These propositions are not definitionally interchangeable for arbitrary M, and the second is weaker when the terminal premise fails. Both suffice for the retained theorem, which explicitly assumes that premise. This difference is an integration choice, not a soundness defect.

The strongest reusable API is 08's `SiteContract M entry Q e`: the physical entry is separated from the full source word determining the target. Its `SiteContract.prepend` is a six-case composition using `Reach.trans_reach1`, or `Halts.of_reach` for halt; it introduces no hidden checker completeness premise. `SiteSpec.length` is stored once, outside the branch match. `semantic_covered_of_allSites` accepts any Boolean classifier with a separately proved semantic soundness implication. Its typed mixed-selector client does not assert the selected sites are proved merely because their selector returns true.

04 provides the same mixed route as a named theorem with `shared Q e || checkEdge M Q e`. 06 provides `semanticCovered_of_allLeaves` with source equality, a purely structural totality gate, and a semantic proof for each `LeafAt`. Both preserve all occurrences. The exact relation between these interfaces is straightforward; adopting their implementations side by side would add redundant APIs and proofs.

References: 02 report lines142–305; 04 report95–199; 06 report360–481; 08 report317–545. Full candidate definitions and their semantic simulation bodies were read, with 06/08 compared against the fully read 04 body.

## Packet02: real suffix attachment, but only two branches closed

`KSimPrefix` defines uniform `PrefixSpec` from an arbitrary gap/register input, positive `RunFromSpec`, and a halt-port suffix. `runToFrom` and `runHaltFrom` invoke the existing Home-ready symbolic executor at a supplied entry rather than the dispatcher. Their soundness is exactly the old executor theorem with the initial symbolic configuration generalized. `checkEdgeFrom` retains every target and both decrement branches. `checkEdgeFrom_start` is definitionally the old checker; `prefix_refl` permits a zero-length prefix.

`KDecoderSuffix215.leaf_spec` obtains a single source-determined `pre,bit,q,op,arg` from the maintained `leaf_prefix`, then composes its all-input run with suffix evidence. The port is fixed before quantifying arbitrary n/vs. The all-source constructor explicitly retains both `allSites (fun _ _ => true) [] t215 = true` and `CheckedLeafSuffixes`. The latter quantifies every exact leaf and its full routed entry, not just a physical q/read pair. Neither global premise is proved by this packet.

The concrete word000/CD8 example is meaningful. It proves the source membership, the exact two-step prefix 84→95→27 with complete left frame, and both suffix branches using the actual fast table and its checked equality to tm215. `semantic_site` then applies actual box lemmas. The prefix is manually proved for that literal word; the generic `leaf_spec` route is checked but remains conditional on all suffixes. This is two of 6,176 branch cases, not a first complete shared primitive family or full coverage migration.

All 29 delivered module source/log hashes in its receipt match extracted files and every recorded exit is zero. These are attributed delivered Lean4.32 component results, not new execution here. The receipt includes inherited dependencies and the example; no closed machine/ZFC endpoint was rebuilt. The implementation adds 4,359B/104lines to KSim plus additive modules. It may reduce repeated decoder computation later, but no actual whole-site or endpoint speedup follows now.

## Shared implication basis in06/08

The generic language remains arbitrary carrier, arbitrary implication, a reflexive relation closed under insertion into either operand, MP, and the restricted row. It assumes no bottom/truth element, injectivity, decoder, order transitivity, or classical completeness. The unrestricted adapter sets the relation to metalanguage `True` and reorders the unrestricted rho8 field's arguments. This is not a diagonal-only restriction.

The retained core already proves K at d12, Peirce at d18, evaluation `b→((b→c)→c)` at d36, and the useful d47 schema. Current public `composition` remains available after d58 was inlined.

06's short ordinary proof is particularly readable. Given a theorem H:a→(b→c), set D=(b→c)→c. Composition with H proves D→(a→c). Composition with evaluation proves `(D→(a→c))→(b→(a→c))`. One final MP exchanges the antecedents, for three MP applications. Compose the existing formulas `(a→b)→((b→c)→(a→c))` and `((b→c)→(a→c))→((a→(b→c))→(a→c))`, using two MP applications, and exchange to obtain S. This has no circular use of S, deduction theorem, or discharge of hypothetical T-proofs. 08 encodes the same five-step opportunity as d59–d63, with every MP substitution explicit.

06 exposes a pure `ImplicationalBasis` module importing only the generic core; the old `Lukasiewicz` module becomes the unchanged Tarski bridge. 08 keeps the adapters inside the old module, avoiding an extra file. Both retain the original Implicational fields and public k/peirce/composition/s types. Both keep the entire 1,358-byte Tarski namespace tail identical, including its explicit use of rho6 for ex falso. Thus neither improperly claims rho8 proves explosion.

Measured delivery totals are 18,668B/426lines across06's three proof files and 19,674B/435lines across08's two, versus their42,715B/819line old pair. Those exact totals use raw58, not current inline a128. The mathematical shared MP count is63 versus58+106=164, excluding the one unchanged `lift_right` application on both sides; including it is64 versus165. These are source/shared-schema metrics, not expanded proof-term sizes, run times, or optimality claims.

The common a128 private d12/d18/d36/d47 are retained, so the five-MP extension stacks directly with current phase11. Do not restore private d56/d58 simply to apply the package. Use public composition in the extension and preserve existing unrestricted-rho8/composition/lift_right signatures and numerical adapter. The current strict producer pins raw input and final output, so adding the basis requires deliberate producer/output-pin updates and reproduction rather than invoking the packages' old whole renderer in place.

06 has stronger submitted integration evidence: a15-module logic slice through unchanged KCodeDom plus two typed clients, with generic basis reports empty and downstream standard axioms. 08 checks an exact Init-only projection of its changed core and generic adapters, plus the countermodel; it explicitly has not compiled the complete replacement Lukasiewicz/Tarski closure. Neither supplies a new full K215 endpoint check. I read source clients and receipts; no new kernel invocation occurred here.

## Origin88c811/e79d52 comparison

The new origin file is SHA eb7533e716479259389dc9b0aaa081fecba0feb8e568cf7222e361cc2895eca2, 15,764B/314lines. It has56 private derivation lemmas plus the one private Tarski adapter, all from unrestricted rho8. Its four public theorem headers and exact Tarski tail agree with current. It imports only the original TarskiComplete; it does not reuse DominatedImplication. The generator adds `--luk` and `--rocq-cd`, and `--luk` rewrites its supplied target in place while retaining the tail after `end ...Lukasiewicz`. It is an untrusted renderer, not a strict maintained provenance gate. Its output target must be an existing expected source, and reproducibility should bind the preserved tail explicitly.

The source math appears coherent and removes50MP applications relative to the old106-step route. Its commit reports builds of Lukasiewicz and direct clients, but this review neither reruns them nor treats the commit summary as a full current endpoint receipt. Combining it unchanged with current a128 leaves two derivations totaling29,487B. Shared06/08 is a larger reduction by reusing the stronger core, not by demanding a weaker target. Preserve the origin proof as a legitimate independent alternative; select one maintained route rather than claiming both savings cumulatively.

Current explicit consumers include Code254, KCode222, Numeric254, KThmK, and TarskiFalsity. They use the retained structure and K/S/Peirce interfaces. No external caller of the old private helpers was found in the maintained BusyBeaver Lean tree. The import-closure census of the accepted197 union gives48 affected modules for Lukasiewicz alone and49 for a joint generic-core/shared-basis change; this is a source-invalidation estimate, not a fresh build. An extra pure basis module changes the inventory as well. KSim affects15 current modules, including all nine site batches. Proof-object byte equality does not excuse transitive source invalidation.

## Other useful results and limitations

04's finite reachability screen is a soundly designed overapproximation, read as source: each register is a product of exact values below a cap and a high interval; increment and positive decrement overapproximate the interval, zero branch filters zero, joins are bitwise unions. It reconstructs full occurrence control flow, independently compares the3326 arithmetic/halt-node CFG, and checks a post-fixpoint. Fifteen cap/initial-counter combinations reportedly exclude only five of6,176 obligations: dead leaves4672/4673/4734 and positive decrement outcomes4671/4733. This is a limited negative prioritization result. It neither proves a kernel source invariant nor excludes stronger relational invariants; no branch should be removed from the current all-register theorem on that basis. I did not execute the search.

08's three-element diagonal countermodel is correctly scoped. Designated value0 and its supplied implication table preserve MP and every diagonal row; rho8(1,0,2,2) evaluates to1. The exact source proof establishes failure of the universal abstract rule. It does not refute our growth-closed restricted interface, the unrestricted `True` adapter, numerical calibration, or ZFC. It also does not prove each growth axiom independently necessary.

02/04's common58 Rocq core and06's basis extension are useful historical cross-language proposals, but their submitted Coq8.18 compatibility checks, namespace shims/rewrites, and small calculus/coqchk scope are distinct from maintained Rocq9.1 endpoint evidence. 08's Rocq semantic interface is explicitly an uncompiled proposal. No new Rocq implementation or execution is recommended in this Lean-only iteration.

There is no mathematical blocker found in the reviewed Lean contract refactors or five-MP extension. The material gaps are stated integration obligations: choose one API, synchronize the maintained generator, compile the actual changed/current dependency closure and typed endpoints, and prove nontrivial suffix coverage before claiming a runtime-check reduction. All four packets retain the external halting iff finite-ZFC-refutation target and do not establish a new encoded internal PA/ZFC derivation or unconditional nonhalting.
