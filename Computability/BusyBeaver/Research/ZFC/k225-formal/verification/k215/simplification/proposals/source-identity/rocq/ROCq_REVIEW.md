# Rocq K215: current status and one immediately local simplification

Review pin: `VladimirReshetnikov/ProveIt@cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Result

The earlier 89-node macro-transport proposal has now been implemented in archived,
component-checked prototypes, but it has not replaced the maintained macro libraries.
Do not present the same transport theorem as a new discovery. The smallest additional
change justified by the maintained source is to reuse the existing generic loop proof
for `ProgLibPerm.z465`, rather than prove this counter-clearing loop by induction again.
This is a modest cleanup: **9 to 5 lines and 475 to 171 bytes per proof declaration**,
with exactly the same public statement. It removes one bespoke induction, not a machine
state, an entire macro library, or a dependency. The proposed proof has not been compiled.

## Already done, versus still open

- The maintained `ProgLibPerm.v` still has 780 lines / 37,951 bytes; `ProgLib219.v`
  has 779 lines / 37,829 bytes. Their bodies beginning with “Determinism of the
  big-step semantics” are exactly equal after `dag219` is renamed `dagPerm`:
  753 lines / 36,213 bytes. The earlier duplication measurement remains true.
- `verification/k215/simplification/proposals/common-macros/rocq/README.md`
  now records a canonical 89-node library and transport of all 58 literal-node
  declarations, with Coq 8.18.0 component and recursive-checker evidence. Its
  eight new modules total 1,300 lines / 61,524 bytes. These are upstream-reported
  results, not checks rerun in this review.
- `proposals/collection-first/code/rocq/macro-slice/README.md` records a second,
  six-module checked slice prototype for the same 53 roots and 89 rows, comparing
  Perm, Dom and 219. Again, this is an archived prototype, not maintained integration.
- Both packets explicitly leave production API/producer integration open. In particular,
  `MacroLibrary.St` is a different nominal record from `ProgLibPerm.St`; generated
  wrappers are not yet an audited drop-in replacement. Candidate-specific `sem`,
  `seqx`, expansion and the changed dispatcher must remain tied to the actual DAG.
- The old unused `s0` enumerator lemmas are no longer present in the inspected
  `rocqperm` sources. They are not a new removal target.
- The current maintained tree also contains `DominatedCore.v`, with short `CD222.v`
  and `DomRho8.v` adapters. The earlier shared-implication extraction is no longer
  accurately described as missing from production.

## Exact local change

The maintained declaration is in
`rocq/rocq-extension/coq/215/ProgLibPerm.v`, lines 670–678:

```coq
Lemma z465 a : forall m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0).
```

Its proof performs induction on `a`, explicitly reconstructing the zero and successor
cases. But `sem_while` (lines 198–214) already proves precisely that iteration pattern;
`while_tac` (lines 320–322) packages its six obligations. The existing `w199` proof
(lines 346–347) uses it to clear register 5.

The literal DAG rows are identical:

```coq
| 199 => (EDecnz 5, EContinue 1)
| 465 => (EDecnz 5, EContinue 1)
```

Replace the proof of `z465`, not its statement, by:

```coq
Proof.
  intros m _. revert m.
  while_tac (fun m : St => m) (fun m : St => set m 5 0).
Qed.
```

The premise `get m 5 = a` is unused because the generic theorem already works for
every initial register value. Keeping it avoids changing existing clients, notably
both calls inside `r466`. This does not invoke `w199` at the wrong node: it applies
the already-proved generic `sem_while` directly to node 465.

## Complete mathematical obligations

Instantiate `sem_while` with node `n = 465`, tested register `r = 5`, body
`b = EContinue 1`, state transformer `g(m) = m`, and post-state
`P(m) = set m 5 0`. The obligations are:

1. `dag_nodes 465 = (EDecnz 5, EContinue 1)`, by reduction of the literal DAG.
2. `5 <= 8`, preserving the nine-register update bound.
3. For every `m`, `sem (EContinue 1) m (XContinue 1) m`, by existing `sem_cont`
   at `k = 0`. The continue level is essential: `EContinue 2` would not qualify.
4. `get (g m) 5 = get m 5`, by reflexivity.
5. If `get m 5 = 0`, then `set m 5 0 = m`, by destructing the finite `St`
   record and rewriting that field. This is record equality, not functional extensionality.
6. If `get m 5 = S v`, then
   `set m 5 0 = set (g (set m 5 v)) 5 0`, by overwrite of the same field.

These are exactly the obligations discharged by the maintained `while_tac` proof
of `w199`. No new theorem, semantic assumption, arithmetic identity, well-foundedness
measure, compiler, or machine transformation is required. All exits and register
effects remain the original ones. In particular, the outer node converts its final
car-side `XBreak 1` into `XNormal`; the body has `XContinue 1`, which restarts the
same node. Those are already the cases handled by `sem_while`.

## Production route and acceptance gate

The exact old proof also occurs in the `NEW_EQ` template in
`rocq/rocq-extension/regenerate218.py`, lines 115–123. That is the owned source
to change, rather than hand-editing only a generated K215 library. The 215 and 217
producers copy/rename the 218 library, so all affected generated outputs must be
refreshed together under the authorized production workflow. Do not rewrite historical
proof snapshots or their receipts to make this patch appear already checked.

The supplied `z465_producer.proposal.patch` changes only that template. It is a
proposal, not a complete committed generated-output patch. `z465_replacement.v` is
an uncompiled standalone comparison client showing the replacement proof and exact
type of both the old and proposed declarations.

Acceptance must include:

1. Compile the comparison client, then the affected regenerated macro libraries and
   `L2RootPerm`, with the production Rocq 9.1.0 / rocq-stdlib 9.0.0 toolchain.
2. Verify that the retained `z465` statement and both `r466` call sites elaborate
   without changes; print assumptions for the replacement and affected endpoints.
3. Rebuild/check the exact sparse and dense K215 endpoints and producer output
   consistency. The literal machine/DAG tables must not change.
4. Count actual maintained bytes after integration. The reported 4-line / 304-byte
   reduction is a static declaration comparison, not an endpoint compile-time or
   proof-term measurement. Additional affected copies are not multiplied into a
   claimed total because their generation and post-patch build were not run here.

## Reproducibility and limits

Run `python audit_reuse.py` for the independently written static audit. It verifies all
15 saved input byte strings against their pinned Git blob hashes, checks both old
macro bodies, checks the producer's exact old proof, measures the replacement, and
rejects a negative-control row that incorrectly changes the continue level to 2.
It does not execute any downloaded program, generator, proof compiler or checker.
`REUSE_AUDIT.json` and `SOURCE_AUDIT.json` record the results. No `coqc` or `rocq`
executable was available on this review's PATH; no compiled-patch claim is made.

The strongest larger Rocq next step remains completing the already-implemented
macro-transport integration with a shared state/interface and one parameterized
contract provider. That is open integration work, not a newly proposed abstraction.
The local `z465` reuse remains useful whether or not that migration is chosen.

## Pinned links

- [Current macro library](https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/ProgLibPerm.v#L670-L678)
- [Existing generic loop rule](https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/coq/215/ProgLibPerm.v#L198-L214)
- [Owned producer template](https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq/rocq-extension/regenerate218.py#L115-L123)
- [Existing macro-transport prototype](https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/common-macros/rocq/README.md)
- [Existing slice prototype](https://github.com/VladimirReshetnikov/ProveIt/blob/cbf94cb552a3b49509e0eee80e7455d4eb5974c6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/collection-first/code/rocq/macro-slice/README.md)
