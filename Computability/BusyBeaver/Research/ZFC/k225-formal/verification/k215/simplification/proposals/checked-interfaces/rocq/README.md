# Direct checked lookup for the current K215 source proof

This component completes the previously proposed lookup-coverage boundary for
the normalized Rocq source certificate. Its exact exported conclusion is

```coq
forall R, rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R)
```

The literal current programs, normalized 1,426-entry certificate and path codec
are copied byte for byte from ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. The component preserves the public
`K215F.Source215.p215_dagPerm` type through a compiled facade and typed client.
It does not rebuild the binary-machine/ZFC endpoint or change any machine.

## The simplification

`LookupNormalized.v` proves the terminating-run argument for an arbitrary lookup
function. The sole global lookup obligation is: every successful lookup supplies
a pair of program paths admitting a locally checked row. Nothing refers to a
list position, finite cardinality, tree balance, or subtree-size invariant.

`CheckedTree.v` supplies this obligation by structural induction: a successful
lookup returns a leaf, and `allTree` checked every leaf. Its cuts may be arbitrary.
The final theorem is consequently

```coq
check (ptree p1) (ptree p2) T = true ->
forall R, rm_halts p1 ([], R) <-> rm_halts p2 ([], R)
```

There is no `validb T = true` premise and no conversion through an external
flattened list. Both directions follow from the one semantic check, using a
mirrored lookup in the generic theorem. A wrong cut can reject the certificate
or route to a different locally verified row. It cannot bypass a row check.

The normalized path utilities are copied verbatim into `PathEq.v`. Infinite
zero-padding equivalence is retained; it is not replaced by literal path
equality. The finite halting induction consumes an actual decrement step before
recursing, even when its following segment takes zero steps. No functional
extensionality or extra classical axiom is used.

## What is inherited and what is completed here

The general idea is already present in the repository's `guarded-core` and
`sharing-interfaces` proposals, and Lean already uses the coverage principle in
`RMBisim.lookupC_all`. Balanced normalized checking and the 1,426-entry
certificate are also prior work. This component supplies the previously missing
Rocq proof, its current literal source instance, compatibility facade and fresh
compiler evidence. It is not a new bisimulation principle.

The older balanced implementation establishes exact list indexing by proving
cut validity and flattening. Those theorems remain useful if a client actually
needs ordinal indexing. The new halting theorem only needs checked lookup
coverage, so those representation theorems are absent from its proof chain.

## Source-size comparison

The comparison excludes the common register semantics, source programs,
certificate data and other unchanged prerequisites on both sides. It includes
all source-proof adapters and facades. Exact file sets and hashes are in
`source_metrics.json`.

| Scoped implementation | Bytes | Lines |
| --- | ---: | ---: |
| Current production normalized list checker and facade | 9,571 | 224 |
| Prior checked balanced-refinement stack | 21,768 | 575 |
| Direct checked-lookup stack | 12,601 | 327 |

This removes 9,167 bytes and 248 lines relative to the prior balanced stack.
It adds 3,030 bytes and 103 lines relative to the current list lane. These are
selected source-file counts, not total repository size, object size or proof
kernel cost. The balanced backend should remain optional until production
measurements justify changing the default.

## Reproduction

With Coq 8.18.0 / OCaml 4.14.1 installed, choose a fresh output directory:

```sh
python3 build.py --out /absolute/fresh/output --baseline --recursive
```

The driver freshly compiles the prerequisites, the unchanged current list
baseline, the new generic proof and exact instance, eight small representation
controls, the facade and a public-type client. It records source, object and log
hashes, tool versions, elapsed times, peak memory and assumption reports.
`--recursive` separately runs `coqchk` on the concrete client and its complete
dependency closure. The accepted receipt and raw logs are under `evidence/final`.
The final recorded run passed all 18 fresh module compilations and recursive
`coqchk` of `SourceClient`; the recursive audit took 259.463 seconds. The
recorded assumption reports are closed. These results apply to the source
equivalence component and its dependencies. No executable or compiled proof
object is bundled.

The Coq 8.18 lane inserts the inherited `Compat818` import in a private copy of
`RMEquiv`. It supplies proved aliases for library lemmas renamed in Rocq 9.1;
no executable definition changes. The delivered and compiled hashes remain
separate. The driver's Rocq 9.1 route is provided but was not executed here.

`verify.py` verifies the packaged source/evidence bindings; it does not run a
proof assistant. Mathematical validity comes from the compiler and recursive
audit, rather than the hash checker.

## Performance experiment

The packet retains one focused packed-row variant under `history/packed`.
It generalizes the tree payload and supplies an arbitrary row decoder; the
generic proof and exact current instance compiled with closed reports. The
local concrete-module invocation took 10.665 seconds, compared with 10.246
seconds for the simpler expanded-row variant in that experiment. The two
recorded `vm_compute` commands took 4.745 and 3.857 seconds respectively.
The packed variant was not selected. `backend_experiment.json` records these
individual invocations and their source/log hashes.

The final fresh run measured the unchanged list source module at 8.968 seconds
and 456,896 KiB peak resident memory, versus 11.135 seconds and 527,844 KiB for
`Source215Direct`. Its recorded `vm_compute` command took 4.221 seconds. The
module timings include different proof construction work and are individual
local invocations, not a repeated controlled benchmark or whole-build
comparison. They show no local speedup for the selected tree instance. Faster
lookup alone does not make tree construction and proof elaboration free.

## Integration boundary

For production adoption, qualify the new helper modules consistently, update
the maintained source generator and its manifests, and rebuild the complete
affected endpoint closure with Rocq 9.1. Recheck both exact sparse and dense
endpoints and their assumptions. Keep the list backend available if it remains
the simpler or faster production choice. No source theorem or table should be
replaced on the strength of a Python integrity check alone.

The accepted external proof-assistant equivalence remains distinct from a
separately encoded internal PA or ZFC derivation. This packet does not supply
that additional internal derivation.
