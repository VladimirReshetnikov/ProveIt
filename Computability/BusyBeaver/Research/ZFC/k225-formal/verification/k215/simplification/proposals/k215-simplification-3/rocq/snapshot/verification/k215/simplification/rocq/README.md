# Compact Rocq dominated-rule proof

**Status: `PASS_INCREMENTAL_ENDPOINTS_FOCUSED_KERNEL` (2026-10-21).** The
compact `DomRho8.v` and all six dependent modules compiled afresh. The sparse
and dense K215 endpoints again printed four closed assumption reports in total.
A recursive `coqchk K215F.DomRho8` also passed, reporting no axioms or unsafe
features in that focused dependency closure.

This phase reused 230 source/object pairs from the hash-bound
[full 237-module baseline](../../rocq/README.md). It did not repeat the earlier
recursive check of the complete set-theory endpoint. The
[result](actual/result.json), [reuse ledger](actual/reuse.json),
[baseline bindings](actual/basis.json), and [kernel log](actual/kernel/output.log)
record that boundary explicitly. The literal machine, theorem statements and
public `DomImp` / `rho8_all` API are unchanged.

## What became simpler

The generated proof shrank from 921,691 bytes / 12,897 lines to 23,678 bytes /
1,239 lines: **97.43% fewer source bytes**. Thousands of individual generated
term and proof declarations became a small generic soundness proof and finite
instruction data. The original 3,728-node certificate is reduced to 674 retained
nodes, expanded into 780 interpreter instructions using 297 shared term entries.
The [comparison record](comparison.json) gives the exact source hashes and counts.

The [generic template](../../../../rocqdom/DomRho8Reflection.v) proves that the
symbolic interpreter produces a valid formula for every instruction stream.
Substitution is justified uniformly over all valuations. Invalid references or
unmatched rules fall back to truth; this cannot establish the final theorem
unless the kernel also checks the exact final symbolic output. That output is
the fully general four-variable `rho8`, checked by ordinary `vm_compute` and
`reflexivity`. No additional axiom, admission, or native-computation shortcut is
used. Both the generic soundness theorem and `rho8_all` print closed reports.

The [renderer](../../../../generate_domrho8_rocq_compact.py) reuses earlier
theorem schemas by explicit substitution, prunes dependencies and emits the
finite data. Its optimizer is outside the trusted argument. The final kernel
check validates its output. The earlier-schema reuse idea came from the parallel
Lean simplification; this Rocq interpreter, template and rendering path are
separate. The original certificate is retained unchanged.

## Recorded checks

- [Seven fresh module records](actual/records/) and their
  [exact source snapshots and logs](actual/attempts/).
- Closed endpoint reports: [sparse](actual/attempts/K215F.Correct215/output.log)
  and [dense](actual/attempts/K215F.CorrectDense215/output.log).
- [Focused recursive check record](actual/kernel/record.json): 20.944 seconds,
  with no `-admit` or `-norec` option.
- [Exact regeneration of all 42 K215 sources](actual/regeneration-review.json)
  and [emission metadata](actual/generation.json).
- [Current source bindings](source-bindings.json) and
  [three literal metadata-pin replacements](metadata-update.json). Their
  [predecessors](history/metadata-before-compact/) retain the original formatting.
- [Compressed experiment history](history.tar.gz) and
  [index](history-index.json), including the interrupted whitespace-predecessor
  build. Final records bind only the whitespace-clean source.

The final `DomRho8` compilation took 1.432 seconds; the earlier expanded proof's
recorded compilation took 8.174 seconds. These are individual invocations,
excluding lock waits, rather than a controlled performance benchmark.

## Reproduction

From `Computability/BusyBeaver/Research/ZFC/k225-formal`:

```sh
python3 -B generate_domrho8_rocq_compact.py --output /tmp/DomRho8.v --metadata /tmp/DomRho8.json
python3 -B rocq/rocq-extension/regenerate215.py --reference /tmp/k215-reference --output /tmp/k215-regenerated/215
```

The reference checkout must be the pinned K230 commit documented in the
[full-build instructions](../../../../rocq/rocq-extension/README.md#the-215-build-route).
The unchanged [portable full-build driver](../../rocq/build.py) can compile the
current source closure afresh and recursively check the complete endpoint:

```sh
python3 -B verification/k215/rocq/build.py --reference /tmp/k215-reference --jeff-reference /tmp/k215-jeff --output /tmp/k215-full-compact --switch proofs-rocq91 --kernel
```

The recorded phase instead ran [rebuild_dependents.py](rebuild_dependents.py)
against the preserved audited baseline cache, copying its objects before
rebuilding the changed dependency closure. With that exact cache available,
run from this directory:

```sh
python3 -B rebuild_dependents.py --baseline /tmp/k215-rocq-complete --output /tmp/k215-compact-new --driver ../../rocq/build.py
```

This incremental script intentionally requires the baseline's audit, sources,
objects and matching `proofs-rocq91` toolchain. It is not a substitute for the
full-build command on a new machine. Both routes serialize proof invocations
through the shared Lean/Rocq lock. The [publication helper](publish_simplification.py)
copies completed evidence into a fresh directory and does not run a compiler.

