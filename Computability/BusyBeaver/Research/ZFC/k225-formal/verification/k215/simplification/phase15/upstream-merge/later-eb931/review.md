# Source review: eb931b07ad, one weak quotient with a CP/GIC adapter

This is a useful next proof refactor, with no mathematical blocker found in the ordinary source read. It is a proposal, not part of the accepted phase 15 checkpoint. I read the complete proposal README, all thirteen resulting Lean modules, the submitted build summary, the changes against the currently adopted phase 15 files, and the relevant Source188/direct-seed interfaces. No submitted script, Lean compiler, producer, or Rocq tool was executed; canonical files were not changed.

The immutable input is commit `eb931b07ad8de83ba1a1d21dc84abe5a1c98364e`. `inventory.json` binds all seventeen changed research paths to Git blob, mode, SHA-256 and local snapshot. The two preceding placement commits concern reports already reconciled as Sources193/194; they do not create a second mathematical intake or another payload-copy obligation here.

## What is new relative to phase 15

The proposal makes the existing weak `KQHyp.QHyp` development the only bisimulation quotient construction. The strong CP/GIC lane becomes an instance through `QuotientModel.ofCPGIC`, with thin wrappers under its retained public theorem names. This removes duplicated proofs for the quotient, Separation, Pairing, Union, Power, Replacement and collection, and makes the six KQ1 modules maintained sources rather than generated forks.

This is the concrete resource-interface factoring suggested in Source188, including the required resolution of the import cycle. Phase 15 had already shared the syntax and shortened both `relSat_congr` proofs. Those improvements remain: the weak congruence proof equates quotient valuations by `mk_eq_iff` and `funext`, then rewrites through `sat_quotient`; the strong proof forwards it. The syntax block changes owner from `QuotientModel` to `KQ1Model` and remains one copy. Its movement is not a second syntax-saving claim.

The complete current graph remains 176 endpoint modules, or 181 with the decoder prefix. All thirteen proposal roots are acyclic in the overlay. The proof-source reduction is real, but this change does not remove modules from the selected endpoint graph.

## Adapter and proof obligations

`ofCPGIC` supplies the existing nine fields of `QHyp`; the structure is not weakened or enlarged. It uses the GIC half of the premise, the four CP/GIC bisimilarity/extensionality laws, and profile pairs. The raw CP container then gives interpreted union, power and singleton-closed containers using the existing resource lemmas.

The critical staging point is `KQ1Power.trace_instance`: it is available from GIC and the translated formula before either the strong quotient or its power theorem is constructed. The adapter therefore imports the weak development, rather than depending on the theorem it is meant to instantiate. The order `KQHyp → KQ1Model → KQ1Separation → KQ1Power → QuotientModel` is acyclic. A tagged structure satisfying only QHyp is never silently given the stronger raw CP premise.

Strong `Domain`, `mk` and `quotientMember` become abbreviations at `ofCPGIC`. Both setoids use the same relation `Eqv mem`; their law fields are proofs, so proof irrelevance supports the claimed definitional identification. This ordinary argument should still receive external typed/kernel checks in the eventual integration. It introduces no new transport axiom or relation-identification assumption.

The arbitrary-formula semantics are retained. Replacement keeps its output slot0/input slot1 convention and its explicit functionality premise. GIC is the original formula-indexed collection interface; the adapter does not replace it with collection for all arbitrary semantic predicates. Singleton-closed containers are not silently identified with von Neumann Infinity. The CP-specific literal subset/container and strong-trace conclusions stay in the strong lane. The proposal does not transport raw membership or internal regularity across bisimilarity without their existing hypotheses.

## Public interfaces and integration details

The source comparison found 114 retained declarations across the thirteen files, with no changed retained theorem header after comment/whitespace removal. Twenty-five old helper declarations disappear. A token shortlist across the maintained BusyBeaver Lean tree, followed by comment-aware checks and a check of all accepted external typed clients, found no use of those removed names outside the thirteen replaced files. The exact per-module list is in `comparison.json`. This is a source/caller census, not an assertion that every downstream module has been compiled under the proposal.

One actual client import needs updating: the accepted `QuotientSharing15Api.lean` imports only `KQ1Model` but refers to both weak and strong namespaces. The reversed sharing direction removes `QuotientModel` from that import's transitive closure. Add an explicit `import BusyBeaver.ZFC.QuotientModel`; its seven statements and proof bodies can remain unchanged. This is an import-boundary repair, not a weakening of a theorem.

Keep the phase 15 explicit `FirstOrder.Completeness` import in `KQ1ZF`; that file is outside this thirteen-file proposal. A later checked adoption should preserve the current complete source graph, force the full source-transitive changed closure, rerun the endpoint/compatibility clients, and add a concise old/weak quotient-carrier and constructor specialization client if useful. The raw delivered twenty-five-module build is not a substitute for those checks.

Retiring `generate_kq1.py` is coherent because there is only one proof implementation left. The current producer is 5,990 bytes/103 lines, SHA-256 `8837ba3cbe0a82c4f166160f58d39ef35bd9d5d50adcac5078d4cf26eaaf7e42`. Its old bytes and generation history should be retained explicitly when retired. The maintained README's generator description must change; historical receipts and proposal references should remain historical. No such retirement or README change was made in this review.

## Exact comparison against the adopted checkpoint

| Scope | Current phase 15 | Proposed | Reduction |
| --- | ---: | ---: | ---: |
| Thirteen Lean files, bytes | 76,405 | 57,566 | 18,839 |
| Thirteen Lean files, lines | 1,699 | 1,271 | 428 |
| Same files plus current producer, bytes | 82,395 | 57,566 | 24,829 |
| Same files plus current producer, lines | 1,802 | 1,271 | 531 |

The README's 601-line reduction is measured against an older phase 14 baseline. It must not be reported as an additional phase 15 saving. These figures compare maintained source bytes, not compiled object size, kernel time, or total repository storage. Keeping immutable proposal/history evidence means the repository-wide byte delta would differ.

## Relation to the direct-seed follow-up

The separate direct-seed design and this proposal address different quotients. The direct-seed design removes the early `KIndisc222` quotient by same-members/same-memberships used to obtain seed semantics. The later tagged/QHyp bisimulation quotient remains part of that route. The present proposal unifies that weak bisimulation construction with the strong CP/GIC implementation. They are compatible in mathematical purpose and do not overlap the direct-seed source edits, but their combined dependency graph and endpoint must be checked before claiming combined savings.

Neither this adapter nor the direct-seed design licenses `enc (dec n) = n` for arbitrary raw formula codes. The degenerate/zero-alias numeric cases and semantic freshness conditions remain those of the existing seed interfaces. There is no new arbitrary-code round-trip premise in the thirteen-file overlay.

## Submitted evidence and next step

`evidence/build.txt` reports twenty-five successful serial component builds from a fifty-one-module reverse closure, with twenty-six modules skipped because other machine-specific imports were stale. It explicitly excludes `KEndpoint215`, other machine endpoints, WFTheory and the facade. The summary reports the standard strong quotient assumptions, weak `propext`/`Quot.sound`, and axiom-free syntax. These are submitted observations read as data; this review does not certify their executable provenance, reproduce them, or promote them to an accepted exact-machine proof.

Recommendation: queue this as a substantial next Lean-only integration, preserving the exact thirteen proposed sources, the current KQ1ZF repair, an explicit strong import in the existing sharing client, and an explicit producer-retirement record. Keep the completed phase 15 checkpoint and its publication unchanged meanwhile.

The bounded census has a small retained metadata history: an initial local-root count omitted twelve shared project providers; a subsequent tracked-only count omitted a newly adopted uncommitted provider. The final census binds the accepted inventories and all 199 canonical project source hashes, obtains 176/181, and uses a targeted caller search. Neither correction involved a proof compiler or proof-source change.
