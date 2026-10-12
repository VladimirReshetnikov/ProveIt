# Integration contract and remaining obligations

## Operator supplied

The supplied operator transforms an explicit finite graph tile and a positive binary exponent into a finite graph preserving the complete clipped marked boundary-cut signature. It is valid for disconnected tiles and includes private, input-only, output-only, and through components.

The main mathematical result is Theorem 5.1 of the article. The relative source graph is reconstructed before any capping in Theorem 4.3. The distinction matters: decomposition is an isomorphism; capping is only query equivalence.

## What a native exporter must authenticate

A native descriptor must identify every source graph edge occurrence, including parallel occurrences and loops; every named source vertex/corner; every ordered input/output port; and the exact equality at every repeated seam. Copies have fresh edges. Ports within a list are distinct and input/output lists are disjoint. Tile repetition cannot be inferred from an Euler characteristic, component genus, unmarked incidence matrix, or product count alone.

An exporter may use the maintained raw-cut and source-parallelity charts, but must prove that its descriptor describes the **transported boundary pattern**, not merely the frontier of a nearby product region. In particular, it must cover two-handle-only base pieces and keep corner order and fibre/attaching data separate.

For geometric essentiality, independently authenticate the original ball and the spherical source embedding. The query kernel is not a replacement manifold or an isotopic embedded graph. The graph criterion is applied only to the original valid cubic pattern after separate handling of empty patterns and vertex-free circles. A subdivided circle is not to be mistaken for a cubic graph pattern.

## Suggested certificate layers

1. Native geometry: original triangulation/cut provenance, ball certificate, pattern embedding, and source-edge inventory.
2. Graph export: finite tile/assembly descriptor with exact source charts and fresh-edge ownership.
3. Stable normalization: boundary partition, short stable exponent, checked right-division identity, complete seam pieces, and declared input/output interfaces restricted to through-component vertices.
4. Query reduction: individual cycle lengths, binary period counts, short remainders, capped detached counts, and endpoint bindings.
5. Finite graph proof: either a low-cut coloring or complete bounded-flow exclusions for every disjoint edge-anchor pair.
6. Counterexample transport: kernel coloring to binary source runs, then source-edge addresses, then an embedded noose and transported violating disc.

Layers 3 and 4 have a supplied producer and a mathematical proof. Layer 5 has independent search-free replay. CLI source binding reconstructs layers 3 and 4 using the same code as production. That is deliberately not labeled independent compression replay. Local lifting primitives from layer 6 are implemented, but its global exporter and geometric stages remain open implementation tasks.

## Independent compression replay: minimum requirements

Do not validate only component counts or boundary connectivity. Verify source edge occurrences, seam equalities, the absence of unintended vertex sharing, both external endpoint bindings, and the private/internal ownership of every nonthrough seam component. In a bridge, only vertices of the actual partner through component are output ports; cap vertices in the same bridge remain internal.

A checker should bind all binary quotient/remainder identities to the original exponent. It should verify each claimed component cycle and retain residues independently, rather than accepting a common-period truncation. Detached graph multiplicities must preserve exact empty/singleton/both mark cases, not merely the existence of some monochromatic edge.

## Dispatch and fallback

Retain the existing connected four-copy shortcut. Small literal inputs can be cheaper than normalization; the completed three-copy negative benchmark regressed. A size-aware or empirically tuned dispatch policy needs its own end-to-end measurement before becoming default.

Unsupported interfaces, exhausted caps, unknown geometric provenance, or failed source reconstruction must lead to a fallback/unsupported state, never to essentiality. The existing complete recognizer remains the correctness fallback.

## Complexity accounting

For a flat descriptor of explicit size Q, the new graph kernel is polynomial in Q and the encoded repetition data. For a formula tree, charge the multiplicative width factor at every power level; do not ignore power depth or DAG reuse. The new quasi-polynomial graph-description result assumes polynomial size/width/bit length and logarithmic power depth.

An unrestricted unknot theorem still needs a source-complete exporter, an appropriate depth/size bound, hierarchy query-count bounds, admissible pattern transport, repair/reset accounting, and complete geometric certificate replay. The O(T) source core and core-facing port bounds do not by themselves establish these additional facts.

## Status of this delivery

No upstream files were changed. No native adapter was implemented or benchmarked. The native maintained test suite and knot corpus were not run. The artifacts are intended for a new numbered report intake and subsequent reviewed integration, with the prior connected report retained and cited.
