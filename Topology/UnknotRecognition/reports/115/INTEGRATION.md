# Integration contract

## Placement and isolation

Suggested intake: a new self-contained report directory under `Topology/UnknotRecognition`, with its number assigned during intake. Keep this research kernel opt-in until the native tests below have passed. The delivery does not patch or replace production dispatch. It changes neither the existing sparse private-column peeler nor the original zero/one forest.

The source checkpoint is `e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39`. The local model is the raw unsigned source-core matrix whose rows are two-handles and whose columns are the retained one-handles after a **fixed** primal forest. The same row IDs label the dual endpoints. Additional bundle-interface rows cannot simply be inserted into this model without establishing their corresponding geometric dual endpoints and cancellation interpretation.

## Exact source sequence

1. Obtain authenticated source parallelity/core geometry and freeze its primal zero/one forest. Reconstruct exact unsigned incidences and the two occurrences of each dual endpoint. Preserve loops, duplicate endpoints, zeros, heavy entries and original row identifiers.
2. Normalize those records with `integration.records_adapter`. Supply the boundary as `None` and preserve the complete interior-three-handle ID list. The record adapter checks contiguity and matching labels; it does not infer geometric validity from them.
3. Run the local selector, preferably after the existing cheap tree trial. Independently verify any result. A digest binds the local data but is not a geometric certificate.
4. Convert only a verified positive tree into a native `core-three-handle-reduction-v1` proposal. The adapter preserves the complete `dual_endpoints`, records each `two_handle`/`three_handle` cancellation in boundary-outward order, and supplies the sorted original `surviving_two_handles`.
5. Pass that proposal to `fastunknot.core_three_handle_reduction_verify.replay_core_three_handles(geometry, certificate, ...)` on independently authenticated original geometry. That maintained checker derives owners from source link triangles and weights from unscaled local coordinates. The adapter must not replace it.
6. Let native replay renumber surviving rows. Reconstruct and replay the downstream core cancellation, annulus/bundle ports, pattern data and whole-cut certificate. A different legal peeling schedule can leave a different surviving column basis; copying old port words or a prior certificate without transport is not justified.

The five-row loop example selects original row 1. The new local peel uses original columns `(3,8,5,6)`, whereas the previously documented alternative uses `(3,8,7,6)`. The tree alone does not determine all subsequent basis-dependent data. The adapter deliberately exports only the top-handle reduction proposal, not an unverified downstream proof.

## Failure semantics

Malformed data are rejected. An interrupted callback does not produce a partial proof. A sampled failure, boundary cap or transition cap produces `UNKNOWN`, never a negative certificate. A valid `BLOCKED_EXACT` record rules out only the fixed local strategy, not a ball, handlebody, unknot or nontrivial knot. A fallback must remain available. Uncapped repeated sampling is a terminating expected-time procedure only on a promised positive input, not a total recognizer.

The theorem's probability bound requires complete independent rounds. Arbitrary deterministic seeds in regression runs and capped timeouts do not satisfy that hypothesis automatically. Parallel deployments need separate fresh random streams, not a copied fixed PRNG state.

## Native validation still required

Reconstruct the full empty-loop and boundary-link-loop source fixtures from the maintained pairing and coordinate records. Authenticate their matrices and endpoints independently. Feed the new proposals through the unchanged native source checker, rebuild downstream source-bound proofs, and compare explicit Regina cuts on small inputs. Add non-handlebody controls, source relabelings, duplicate endpoints, self-loops, three-handle-free inputs, forged source bindings, cancellations and all existing regression tests.

Measure complete native preparation + selection + independent source replay, and compare matched literal/incumbent trials. Preserve all controls and refusals. The delivery's existing seven adapter tests validate only the record contract; these proposed native experiments were not run here.

## Parity diagnostics

`integration/parity_audit.py` checks `V_D (N mod 2) = 0` for **exact** unsigned counts under the stated handle-chain model. It also decides whether saturated categories admit any compatible parity lift using connected components of the heavy-edge graph. A lift is only a necessary consistency witness, not manifold realization and not permission to alter an authenticated count. The unanchored choice family uses heavy value 3 where needed and passes exact parity, but no geometric realization is asserted.

## Bounds to retain at the caller

Record local encoded size, exceptional boundary `b`, mandatory count `q`, graphic rank `r`, sampling count, transition count, result status, source-preparation time, and downstream replay time. A local `2^{O(b)}` theorem does not bound surface discovery, admissible geometry repairs, number of hierarchy calls, restart frequency or pattern transport. A quasi-polynomial whole-run claim requires simultaneous bounds on all of these quantities, not only small matrices in one experiment.
