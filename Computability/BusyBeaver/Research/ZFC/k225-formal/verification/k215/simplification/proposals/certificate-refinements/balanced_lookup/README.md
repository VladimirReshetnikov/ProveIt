# A balanced Rocq certificate checker for exact K215

This packet adds a **checked optimization of the existing source-correspondence
proof**. It does not change K215, its source program, the numerical calculus, or
the ZFC-refutation predicate. The inspected repository commit is
`53269bcab1efc0f82d3022645bd7cf0c22d84959`.

## New result

`Source215Balanced.p215_dagPerm_balanced` has compiled with Coq 8.18.0, with
closed assumptions:

```coq
forall R, rm_halts p215 ([], R) <-> rm_halts dagPerm ([], R).
```

The new checker uses a binary-indexed tree instead of `nth_error` over a list
of 2,240 certificate entries. The original plain checker's semantics and
soundness theorem are reused. `checkTree_flatten` proves exact equality with
the ordinary checker on the flattened tree, assuming its explicitly checked
size invariant. `tree215_exact` proves that flattening the constructed tree
returns the exact existing plain certificate; `tree215_valid` proves the size
invariant. The complete concrete forward check is evaluated and checked by
the kernel. Both programs are the unchanged repository definitions.

The new generic proof has **194 lines / 6,480 bytes**. The concrete exact-data
wrapper has 23 lines and the source theorem 21 lines. This is reusable proof
infrastructure; it is not advertised as a reduction of total proof-source
lines. Its purpose is to simplify the *checking workload* while preserving
the existing mathematical proof.

## Prior work retained rather than claimed again

The input packet `docs/incoming/ZFC215_Proof_Simplification_2026-10-21.zip`
already supplied compact positive-integer path codes, zero-offset ordinary
bisimulation, and a one-sided symmetry theorem. Another incoming packet
already supplied a complete ordinary Lean lane; a third normalized 2,240
checkpoints to 1,426. The present result adds the **Rocq balanced lookup** that
the first packet described as future work. It retains that packet's
`PathCodec.v`, `Cert215Compact.v`, and `BisimMirror.v` with attribution.

## Concrete reduction of lookup work

There are 2,239 decrement checkpoints, one halt checkpoint, and 4,479 queried
successors including the initial checkpoint. For these exact references:

| Representation | Traversal nodes visited |
|---|---:|
| List with `nth_error` | 5,018,706 |
| Balanced tree | 54,514 |

The ratio is **92.06**. This counts list/tree constructors visited in the
lookup component, not bit operations, program-path walks, segment simulation,
kernel work, or total runtime. The worst tree lookup visits 13 nodes, including
the leaf. `tree215_lookup_bound` proves that bound for **every** binary index,
including out-of-range ones. `lookup_metrics.py` reproduces the finite census;
the census is not an assumption of the correctness theorem.

For a balanced N-entry certificate with O(N) lookups, tree traversal has
O(N log N) node visits versus O(N^2) worst-case visits for the list. Here cuts
and indices are binary `N`, avoiding a hidden unary conversion at each lookup.
Charging linear cost for comparisons/subtractions on O(log N)-bit integers
gives O(N log^2 N) indexing bit operations. These bounds concern the indexing
component; program decoding and register-segment checking remain unchanged.

## Measured local comparison

On the shared execution environment, one matched run gave:

| Check | Plain list | Balanced tree |
|---|---:|---:|
| Coq `Time vm_compute` transaction | 16.008 s | 11.314 s |
| Complete source-module `coqc` process | 33.103 s | 24.772 s |

These illustrative observations correspond to 29.3% and 25.2% lower wall
time, respectively. They are **single observations in a shared environment**,
not stable benchmark claims. The balanced tree also takes 13.159 s to compile
its construction/exactness module. Therefore the data do not establish an
end-to-end first-build speedup, nor a complete endpoint-build speedup. A
production generator can emit the balanced tree directly while retaining the
exactness check as an independent audit target; that proposal is not measured
here.

## Verification scope

All dependencies used for this experiment were compiled from source during
this task; unchanged objects were reused only within this task while iterating
on the new module. Every selected new proof has a successful `coqc` kernel
check and a closed assumption report. The generic `BalancedBisim` module and
its dependency closure also passed recursive `coqchk`. The separately checked
recursive target does **not** include the large concrete source certificate.

The exact current `Prog215.v`, `DagPerm.v`, and original `Cert215Offsets.v`
were compared byte for byte with the corresponding incoming inputs; all three
match. The current bindings are recorded in `evidence/current_repo_binding.json`.
The source theorem itself needs no trust in the certificate generator: any
tree passing the verified checker proves the stated equivalence.

This packet does **not** replay all 237 Rocq sources, the complete binary/ZFC
endpoint, or the pinned Rocq 9.1 toolchain. The reported external theorem is
not an encoded proof in PA or ZFC's own proof syntax. The full endpoint's
mathematical composition remains available from the repository; production
adoption requires rebuilding the affected endpoint clients.

## Reproduce and integrate

With Coq 8.18.0 on PATH, from this directory:

```sh
python3 reproduce.py --output /path/to/empty/build
python3 lookup_metrics.py
```

Add `--benchmark` to compile the incoming plain-list baseline, or
`--check-generic` for the recursive generic audit. Proof compilers run serially
under the same lock. No Mathlib, network, binary proof cache, or complete ProveIt
checkout is required. The original Rocq 9.1 dependency source is retained; the
driver's 9.1 branch is an integration convenience and was not run here.

For integration, put the new modules in the desired K215 namespace, keep the
public name `p215_dagPerm`, replace its proof with the body of
`p215_dagPerm_balanced`, update the maintained generator, and rebuild
`Correct215` and `CorrectDense215` with assumption reports. Reuse the input
compact certificate and symmetry modules rather than maintaining duplicate
copies. The table, source program, and endpoint statements remain identical.

## Attribution

The new balanced checker and experiment are this packet's contribution.
The source semantics, original checker, K215 construction, numerical calculus,
set-theoretic calibration, compact path codec, ordinary source proof, and
symmetry theorem remain contributions of their respective authors. Existing
headers and the incoming packet's notices and license boundaries are retained
in `licenses/`. New material may be incorporated under ProveIt's terms.
