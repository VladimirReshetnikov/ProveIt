# Smaller K215 source-correctness proofs

This packet shortens a remaining part of the **existing, formally verified K215
machine proof**. It does not alter the machine, its source program, or the
ZFC-refutation predicate. The base repository revision is
`e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad`.

## Results and scope

The new theorem in `Source215Simple.v` is

```coq
Theorem p215_dagPerm_simple R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
```

It holds for every natural-valued register file `R`. The literal `p215` and
`dagPerm` definitions are the repository's existing definitions. Its proof
uses an ordinary register-segment bisimulation, a compact certificate, and
one evaluation of the forward checker. There is no consistency premise.

This is a source-correspondence theorem. The full 237-module Rocq ZFC endpoint
is not rebuilt here. In the endpoint pipeline, it can replace the theorem
`p215_dagPerm` in the existing `Source215.v`; every other mathematical layer
remains available from the existing proof. Full endpoint rebuilding and an
endpoint assumption report remain the integration check.

The supplied `build.py` rebuilds the small dependency closure from source,
prints assumptions, and recursively invokes `coqchk` on the exact
certificate-equality theorem and the generic offset-mirror theorem. A separate
`--recursive-source` option also requests recursive checking of the source
correspondence dependency closure. The recorded default run kernel-checks the
source theorem during compilation and reports it closed under the global
context; it does not claim a completed separate recursive source audit.
The final `verification/result.json` records compiler hashes, source hashes,
timing, and raw log hashes. Compiled objects are excluded from this packet.

## Three simplifications

1. **Remove the unused signed-offset layer.** Every one of the 2,240 entries
   in the K215 offset certificate has offset zero. The new source proof uses
   the existing plain `K230P.Bisim230` checker instead of
   `K215F.OffsetBisim230`. In this certificate, matching segments increment each
   register equally often, and related tests examine the same register.
   Integer-offset bookkeeping contributes no information.

2. **Check one direction.** `BisimMirror.v` proves for all trees and
   certificates that a successful forward check implies the successful check
   of the mirrored certificate. `check_one_sided_iff` combines this result with
   the existing checker's soundness theorem. The analogous general result for
   nonzero offsets is supplied in `OffsetMirror.v`. The current Rocq
   `Source215.v`, lines 8-13, still independently evaluates both directions.
   Lean already has the corresponding symmetry principle.

3. **Encode paths instead of spelling out bits.** A finite Boolean list is
   encoded by a positive integer: the empty list is `1`, a `false` head doubles
   the tail code, and a `true` head doubles it and adds one. The leading one
   preserves every trailing false bit and the exact list length. `PathCodec.v`
   proves both round-trip equalities by structural induction. `Cert215Exact.v`
   proves that expansion yields **exactly the original ordered certificate**,
   including both paths, zero offsets, and both successors in every row.
   This is a kernel-checked equality, not a hash-only assertion.

| Data source | Bytes |
| --- | ---: |
| Original `Cert215Offsets.v` | 1,499,170 |
| `Cert215Compact.v` | 171,678 |
| Reusable `PathCodec.v` | 1,325 |
| Compact data plus codec | 173,003 |

The last row is **88.4601% smaller** than the original certificate source.
These are uncompressed UTF-8 source sizes. They do not measure proof-object
size, kernel workload, or total endpoint build time. `certificate_metrics.json`
is the machine-readable measurement. The maximum path lengths are 45 and 176
bits. The packet includes both an offset-compatible expansion for the exact
equality audit and the simpler zero-offset expansion used by the new theorem.
Both expansions use `Eval vm_compute` at definition time, so generated objects
contain the expanded value rather than a transparent deferred `map`.
The exact-expansion theorem still guards the generated data independently.

## Reproduction

Run from this directory with `coqc` and `coqchk` on `PATH`:

```sh
python3 build.py
# Optional additional recursive source audit:
python3 build.py --output verification_recursive --recursive-source
```

The recorded run uses Coq 8.18.0 and OCaml 4.14.1. Upstream's complete endpoint
uses Rocq 9.1.0. The only compatibility adaptation to the extracted dependency
closure is a `Require Import Compat818` added to the private build copy of
`RMEquiv.v`. The module supplies four renamed list-library aliases and a proved
`nth_firstn` lemma. It adds no axiom and changes no executable definition. The
exact original file is preserved as `deps/K230/RMEquiv.rocq91.v`.

The driver also recognizes Rocq 9.1 and then uses that original file without
the compatibility import. That branch is provided for integration but was not
executed in this session; only the recorded local 8.18 run is claimed.

The `history/transparent-expansion/` directory preserves the first build receipt,
logs, and the former compact source that deferred decoding to later conversion.
All module compilations and the exact-certificate recursive check passed in that
run. The separately requested recursive source check was deliberately terminated
after 409.2 seconds (exit status -15) without a logical rejection being reported.
The final sources materialize the decoder result; their default reproduction
records compilation and exact-certificate recursive checks. The history is kept
so the interrupted optional check cannot be mistaken for a completed result.
No overall kernel-speed or endpoint-build-time improvement is claimed.

To regenerate the compact data from the repository input:

```sh
python3 pack_certificate.py /path/to/Cert215Offsets.v
```

The generator checks its pinned input hash and rejects any nonzero offset or
unparsed input row. Its output is nevertheless untrusted until
`Cert215Exact.v` and the source checker compile. The generator never serves as
an extra logical premise. `OriginalCert215.v` is the unmodified original
certificate under a different file/module name.

## Integration

For the smallest initial change, place `OffsetMirror.v` in the `K215F` namespace
and apply `integration/mirror_only.patch`. It retains the old certificate and
public theorem, replacing only the second finite evaluation with the generic
mirror theorem. The patch is an integration proposal, not a claim that the full
upstream endpoint was rebuilt here.

Retain `PathCodec.v`, `Cert215Compact.v`, and `BisimMirror.v` under the chosen
project namespace; adjust their `Require` declarations to that namespace.
Replace `Source215.v`'s two certificate-check lemmas and final theorem by the
proof in `Source215Simple.v`, retaining the public name `p215_dagPerm`.
Maintain the old certificate's exact-expansion audit in a separate audit target.
Rebuild `Correct215` and `CorrectDense215` and rerun their assumptions reports.

The plain checker does not require `OffsetBisim230.v`. That module and
`OffsetMirror.v` are bundled as a separately checked generic improvement for
other candidates with nonzero offsets. They are not dependencies of the new
K215 source theorem.

The analogous Lean change should use `RMBisim.check_halts_iff`, which already
has one-sided symmetry. Its ordinary decoder has a fuel bound of 128 recursive steps,
whereas the K215 source comparison needs a path of 176 bits. Parameterize the
ordinary checker by a sufficient decoder bound, or supply a 512-step decoder
instance, before migrating the source data. Simply changing `OTree` to `CTree`
without addressing the bound is incorrect.

A further dependency refactor is promising but is not implemented here:
`Prog215.v` imports all of `K230.Prog230` to reuse the generic `cedge` type and
`cv` decoder defined near its beginning. Factor those definitions into a small
shared encoding module. This can allow clients to avoid importing the
unrelated 5,124-node K230 program and its well-formedness certificate. Check all
transitive clients before claiming a reduction in the complete endpoint closure.
The present build deliberately retains the exact existing dependency instead.

For checker performance, the Rocq checker retrieves successors with
`nth_error` on a certificate list. With two successor lookups per test entry,
the worst-case indexing cost for N entries is quadratic. A verified balanced
lookup representation, already used by Lean's `CTree`/`OTree`, can reduce that
indexing component to O(N log N). This is a proposed representation change;
the present packet makes no measured speedup claim for it or for the complete
endpoint build.

## What was already present upstream

The current repository already has four proof-simplification checkpoints. In
particular it has shared guarded implication lemmas, AX-word composition,
one general enumerator theorem, symbolic enumerator contracts, shared site
coverage, and Lean offset-bisimulation symmetry. The current Lean endpoint
closure is reported as 185 modules; the original full run had 204.
This packet does not claim those earlier changes as new results.

## Provenance and licenses

`dependency_manifest.json` records every retained dependency and its source.
The K230 sources were extracted byte-for-byte from the repository's preserved
Rocq build-evidence archive. Their upstream reference is Elliot Glazer's
`k230-rocq` at `3142e4dd980f0be12f4abb636c4ae2528afc17eb`, with the reference
ancestry in Jeff's `busy-beaver` at
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`. The K215 files are from the pinned
ProveIt revision above. Existing file headers remain intact.

Original notices and available license texts are in `licenses/`, including
the upstream file-level licensing scope. No blanket license is assigned here
to third-party adapted files. New material follows ProveIt's MIT No Attribution
terms.
