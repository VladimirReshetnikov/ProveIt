# K224 source-layout research

Status as of 2026-10-20 02:32 UTC: no verified machine below 224 states has been found in this lane. Raw source-DAG counts, finite instruction probes, and local folds are different obligations and are reported separately.

## Distinct conditional-K 224-state candidates

The theory sources `../theory/k_shapes/10000_0/sites.json` and `10000_1/sites.json` use the conditional-root K formula. Each has 210 distinct source nodes, 4,799 leaf instructions, maximum depth 38, and maximum zero run 6.

`compile_current.py` allocates each to 225 physical states. The resulting tables are in `compiled_repaired/10000_0/` and `compiled_repaired/10000_1/`. Applying the exact local fold recorded in each `fold_0/recipe.json` merges physical state 18 into 180, using state 119 as the read-0 helper and the direct read-1 action. Each final `fold_0/candidate.tm` has 224 working states. The proof in `fold_0/local_proof.json` is an all-tape positive block-simulation proof of that local fold, relative to its 225-state input.

Both folded tables pass every one of the 6,238 zero/positive source-instruction probes (`finite_probe.json`). The engine lane reports exact sparse/dense blank startup to the inherited seed in 409,829 steps and a fresh source-bucket induction for each. Universal instruction proofs are being run independently in `../engine/source_candidate_10000_{0,1}/`; consult those current receipts before making a complete machine-correctness claim.

Native labels: initial state 0, source dispatcher 84, halt 254. Both repaired conditional224 tables use only labels through 229, so the archive's existing `portable/machine/reference/legacy_state_map.json` suffices. Larger experimental allocations sometimes add 230; those need a fresh legacy label if passed to an old-label driver.

## Further physical rotations

`general_rotations.py` permits literal physical rotations of `((A,B),C)` and `(A,(B,C))` when A has no escaping forward break and C has no escaping backward continue. It permits primitive outer actions, and reuse of an already available pair decoder. It does not introduce cloned states.

Every currently retained neighbor is checked against the intended semantic-node/physical-state association by `binding_ok`. Merely obtaining some decoder map is insufficient: an earlier exploratory zero-run walk exposed that mistake and its unverified best-28 artifacts must not be used.

`conditional3/` completed depths 0, 1, 2, 3, with 1, 14, 97, and 455 layouts respectively. The tested local fold families found no further reduction. `conditional4/` resumes the same search at depth 4, with 1,663 distinct valid-prefix layouts. Its saved checkpoint includes 787 partial depth-5 neighbors generated before the search budget was narrowed; this is not a completed depth-5 result. No startup restriction is imposed on these layouts, so every future hit still needs a full startup and runtime check.

`multi_rotations.py` additionally checks a literal simultaneous rotation across all semantic roles of a shared physical state. No valid one-step instance was found on either conditional224 table or on the frozen-startup best-40 layout.

## Fewer six-zero addresses, still 224 states

`zero_walk_frozen/` made 491 accepted physical rotations from 11,451 examined neighbors in ten bounded walks, retaining all 250 original startup transition rows and checking intended decoder bindings. Its best candidate has 40 leaves whose address contains six consecutive zeroes, down from 43. It does not permit removal of the six-zero scanner.

`zero_walk_frozen/best_040/probe.json` verifies the exact original 409,835-step blank startup and complete tape equality, equality of the source control-flow graph, and all 6,238 finite instruction cases. The source now has maximum depth 39. No universal runtime proof was run for this alternative.

`zero_walk_valid/best_040` is a different, startup-unfrozen layout. It passed finite instruction probes but failed to recover the intended startup seed within the examined run. It is not a valid construction receipt.

## Other searches and rejected combinations

* Native equality-helper binder variants were exhaustively enumerated within the eight tested atom families and six-block parenthesizations (`helper_variants/summary.json`). Fixed-alias optimistic pricing was 224 for Rel(a,b), 225 for All(a,b), 226 for Imp(a,b), Imp(b,a), Rel(b,a), and 227 for the other three. These are bounds for that scoring model, not machine lower bounds.
* The 14 selected equivalent K-shape sources were passed through the current allocator (`compiled_repaired/summary.json`). Conditional-root variants supplied the new 224 basis above. Other source layouts cost more or conflict with a retained decoder alias. A raw 210-node source is not evidence of a 224-state machine.
* Combining the seed-relative NIP specialization with five K shapes retained 210 source nodes but had incompatible primitive entry contexts (`combined_nip/`). The unscreened conditional combination allocates 226 physical states and fails a concrete CB1 instruction at source index 4657 after 6,051 passing finite cases. It is rejected, not a candidate.
* Searching every single transition into an existing baseline state for the new NIP CD5 prefix (896 write/direction/target actions) found none that passed the tested values 0, 1, 2 (`discovered_cd5.json`). This is a finite interface search only, and does not exclude adapters or a different source shape.
* The first strengthened-rho1 logical source has 218 source nodes and currently fails a new CI1 entry in the allocator (`compiled_strengthened/R_0_0_0/compile.json`). Further logical-basis variants belong to the theory lane.

## Reproduction and proof scope

Always use `python -B` (or `PYTHONDONTWRITEBYTECODE=1`) when importing anything from the immutable authenticated intake.

`compile_current.py` is an experimental allocator. Its helper-row catalogue was discovered on finite original source frames; it is not itself a universal correctness certificate. `finite_probe.py DIRECTORY` is a reusable counterexample screen. The allocator, decoder-prefix checks, local fold proofs, exact source control-flow comparison, blank startup, universal instruction proof, source seed invariant, and logical theory calibration must all be combined before certifying any new smaller machine.
