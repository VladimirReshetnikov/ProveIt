# Proposed opt-in integration

## Destination and safety boundary

Place this directory under a newly allocated `Topology/UnknotRecognition/reports/` continuation directory, or another repository research directory chosen by the maintainer. No existing report number is assumed. Do not overwrite current source or change ordinary `recognize` dispatch. No repository mutation was performed for this delivery.

The package is an exact **abstract interface query**, not a knot decision stage. A local unsuccessful or incomplete calculation must never become a knot verdict.

## Source checkpoint

Inspected native checkpoint: `ed166080d7db14dd7a91d07788996f02947dd92a`. The maintained `parallelity.tex` already provides a source bundle, <=30T inherited core handles, and <=66T singleton core-facing arcs. It also retains actual source charts and attachment positions; this proposal compiles, rather than invents or replaces, that information.

The inspected `sparse_incidence.py` already contains subset coning. The new compiler's role is degree-two first-return recovery and corner/gap detection, not a replacement coning or AHT algorithm.

## Geometric factory contract (not delivered)

Given a validated source-parallelity packet:

1. Retain a common corner-occurrence universe. Derive V from source quotient-vertex identifications. Derive F from V and all actual free-boundary edges. Derive R by excluding the named core-facing edges from F, splitting affine families at each marked singleton rank. Interior corner classes may remain silent in both R and F.
2. Supply each port's source label, active-component owner, both endpoint occurrences, and coherent induced frame. A loop has two endpoint occurrences even if they carry the same point ID. Preserve fibre reversal separately from rank-map slope.
3. Supply independently verified connected base statistics `(chi, boundary, orientable)`. Aggregate port-free repeated profiles; the explicit kernel API enumerates active components, not a binary number of identical components.
4. Bind all data to the source packet's fingerprint and all endpoint/cyclic data to actual attaching charts. Validate local links from the source; terminal-count consistency checks alone do not prove that arbitrary relations describe a surface.

The compiler can then use three native count factories, sharing one budget:

```python
from corner_kernel.compiler import compile_boundary
from corner_kernel.upstream import SharedBudget, upstream_oracle

budget = SharedBudget(max_cycles=None, max_queries=None)
vc = upstream_oracle(universe_size, V_pairings, budget)
rc = upstream_oracle(universe_size, R_pairings, budget)
fc = upstream_oracle(universe_size, F_pairings, budget)
kernel, query_log = compile_boundary(
    active_surface_types, source_ports, vc, rc,
    full_boundary_count=fc,
)
```

`universe_size`, V/R/F systems, surface types, and source ports must come from the factory above; this code is not a substitute for constructing them. The optional wrapper follows the inspected `count_orbits` signature but was not run against the upstream repository. Native endpoints are inclusive and zero based; singleton point pairings are the correct augmentation form.

## Independent verification

Verify each native orbit certificate with the repository's maintained proof-only verifier, including the augmented input system. Reconstruct the terminal matching, corner bits, cyclic words, source ownership, and coherent frames independently. Verify the finite gluing result using a separate implementation or a small certificate checker.

The delivered `verify_count_transcript` reruns count callbacks. It checks recorded count answers, not all source data, and is not independent AHT proof replay. Underlying proofs can be much larger than the final O(p)-edge kernel; charge their full bytes and verification costs.

## Actual interval-bundle moves

Before treating a base gluing as a 3-dimensional bundle operation, verify normalized fibre charts and the article's corner-holonomy criterion. Retain or prove the global orientation-bundle character. A matching surface genus inventory is not a certificate that an arbitrary manifold is that bundle. The spherical boundary of the orientation bundle over RP2 is the retained counterexample to boundary-only ball inference.

Likewise, preserve source reconstruction programs on suppressed paths when future discs must be lifted. The compiler's gap length one means positive length, not a source path of one edge.

## Native experiments after the factory exists

Use source-derived small cuts and independent explicit boundary reconstruction first; then test large normal multiplicities. Include adjacent core-facing arcs and selected two-handle bases, not just prism-only examples. Compare full source conversion, count discovery, proof replay, and serialization on identical packets. For repeated candidate surgeries, measure both one-shot and compile-once workloads under one total budget. Keep regressions and interrupted cases. Only after these checks should any optional native stage be proposed.

The current measurements compare to literal expansion on abstract surface data. They are not evidence of a native regression-suite pass or of faster complete unknot recognition.
