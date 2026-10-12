# Integration contract

## Mathematical input

`compile_kernel_packed` accepts:

```python
(size, residual_pairings, terminal_occurrences, edge_mass,
 port_owners, certified_boundary_counts, oracle)
```

`Pairing(a,b,c,d,reverse)` uses **inclusive** interval endpoints. Weight intervals `(start, stop, mass)` are **half-open**. Each port has two ordered terminal entries, even when they occupy the same actual corner or identical namespace point. Terminal labels are implicit: entries 1 through 2p. Port owners use zero-based owner indices.

The residual relation must be vertex-occurrence equivalence plus unmarked boundary-edge connectivity. The source, not the moment decoder, must certify that the quotient boundary is a union of circles and that the marks are distinct whole source edges.

`edge_mass` must place unit mass at exactly one authenticated endpoint occurrence of every actual unmarked boundary edge. Add overlapping owner images. Do not give mass to every alias, retain mass for a removed marked edge, or replace this nonnegative mass by a signed invariant.

The resulting `Kernel` supplies first-return pairs, exact lengths, and active/passive counts. Retain component types, coherent surface orientation frames, fibre information, source charts, and source fingerprints outside this small derived record. It is not a complete patterned-hierarchy certificate.

## Native weighted oracle

With both the delivered `code/` and the repository's `Topology/UnknotRecognition/fast/` on `PYTHONPATH`:

```python
from moment_kernel import compile_kernel_packed
from proveit_adapter import make_oracle

certificates = []
oracle = make_oracle(max_cycles=100_000, certificates=certificates)
# packet is the six-field tuple supplied by your authenticated source adapter.
kernel = compile_kernel_packed(*packet, oracle)
```

The adapter requests a weighted certificate and invokes the maintained independent weighted verifier by default. It returns the histogram stored in that checked certificate. A caller-supplied `verify` override must preserve the same exact source-binding responsibilities. The `check` callback is passed to generation and independent replay so cancellation can propagate.

A non-complete native status raises `Incomplete`, never a negative knot certificate. The default-branch API can evolve: inspect the recorded signatures before integration. The delivered API mocks passed; actual native execution was not performed here.

An opt-in smoke test, including binary stress cases, is supplied:

```sh
python code/native_smoke.py --fast-dir /path/to/ProveIt/Topology/UnknotRecognition/fast
```

This file's presence is **not** evidence that the native test was run. Its output is created only after a successful local invocation.

## Source adapter still required

Use the verified parallelity packet's actual free-edge families and ordered endpoint maps. Construct the all-corner vertex relation; add unmarked free-edge relations; split family intervals at selected singleton marks; place each remaining edge's mass at one canonical endpoint. Supply verified owner boundary counts and preserve source orientation/fibre frames.

Test cap-only components, aliased corners, one-edge loops, nonorientable bases, singleton fibre flips, empty marks, relabellings, and very large normal multiplicities. Compare complete first-return kernels against explicit source boundary walks, not only Euler totals.

The standalone `CircleSource` is a genuine degree-two interface model, **not** a triangulated knot exterior or this missing adapter.

## Reuse and transport

Compile a maximal finite set of candidate edges once, retain that fine kernel, and call `forget_ports` for arbitrary subsets. The kept port IDs are zero-based and may be reordered. Unmarking a unit source edge adds one to the coarse path length. A macro-port needs its actual edge mass instead.

For a fixed finite group, `transport_census` uses a regular lift and one scalar census by default. It expects the convention `(x,h) -> (y,h*t)`; deck transformations act on the left. `forget_transport` composes factors in path order. It returns active transport, not unanchored passive-cycle holonomy.

## Search and complexity scope

The article's all-subset / signed-pairing search theorem is a mathematical consequence of this compiler and the predecessor's corner-aware surgery algorithm. A new full surgery enumerator is not delivered here. Neither compiler nor enumerator supplies geometric realizability, patterned admissibility, a small-reservoir theorem for arbitrary knots, hierarchy depth/reset bounds, or a general quasi-polynomial recognizer.

Integrate as a research operator behind explicit contracts and retain the existing exact recognition fallback. Establish native correctness and complete-query performance before changing default recognition behavior.
