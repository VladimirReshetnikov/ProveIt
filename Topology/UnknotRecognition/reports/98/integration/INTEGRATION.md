# Additive integration plan

## 1. Intake and preserved boundaries

Place the complete bundle in a new `Topology/UnknotRecognition/reports/<next-number>/` directory. No fixed number is assumed. This delivery changes no production defaults and includes no automatic upstream patch. The inspected source commit is `d5c9a97fac1803258ea675297e4a7b22b78dd79b`.

The immediate connection is report 91's `proveit.graph-grammar.v1` schema. `src/report91_adapter.py` translates accepted inputs to this delivery's grammar. It preserves selected roots, capacities, ordered terminals, fresh edge occurrences, self-identifications, and forgetting. The adapter checks explicit vertex inventories before allocating lists. Its acceptance is not a claim to support arbitrary future schema changes.

Run the supplied fixture using `PYTHONPATH=src python integration/query_report91.py examples/report91_triangular_prism.json`. The recorded result is in `data/report91_adapter_result.json`. Neither the complete report-91 software suite nor native topology tests are inherited as this delivery's validation.

## 2. Proof interface

Call `compile_grammar(source)` and then `verify_packet(packet, expected_grammar=source)`. Treat every checker failure or exhausted resource budget as uncertified/inconclusive. Retain graph provenance separately from the certificate's embedded grammar; a self-consistent graph packet does not establish that the graph came from the intended manifold.

At a terminal-free root, `MARKED_CUT` means that a two-coloring of cost at most `k` has a monochromatic edge of each color. `NO_MARKED_CUT` means absence through the specified threshold, not absence at larger costs. The complete packet contains all exact costs; report 91's old response table stores minima. Comparing the two requires minimizing exact costs by actual boundary coloring and actual global flags, not comparing raw row lists.

To certify a positive row without complete replay, export `build_recipe(packet, row_index)` and run `verify_coloring_recipe(recipe, expected_grammar=source)`. This verifies one family of colorings for all visible component-root assignments. It cannot justify a negative query, a minimum, or a complete atlas. Cut and mark occurrence addresses are recipes in the graph grammar; native chart addresses require an additional map.

## 3. Necessary native geometric exporter obligations

For a ball-pattern use, authenticate the source manifold piece and its ball certificate; its spherical boundary embedding/rotation information; the actual unit-edge cubic pattern and vertex-free-circle inventory; ownership of every edge occurrence; every terminal quotient identification; and source charts for returned occurrence addresses. All future attachment vertices must remain terminals until their final use. The graph language does not promote a private vertex after forgetting it.

An exported graph that merely shares selected scalar invariants with the pattern is insufficient. Cubic metadata checks abstract degrees, not spherical embeddability or a 3-ball. In particular, the graph result must never be implicitly cast to a knot verdict.

## 4. Performance integration after semantic review

Keep the existing explicit/minimum-state backend available. The tested atlas removes the component-factor asymptotically, but loses on some small-width power cases. A future dispatcher should compare conservative candidate/state estimates or try bounded work; switching backend must not change response semantics. Document whether comparing exact-cost or minimum-only modes.

The first optimization proposed by the article is to precompile the fixed interface's XOR cycle constraints and root shifts once. The second is a new minimum-only gauge schema, justified by descriptor dominance. Neither is implemented here, and neither has a measured speed claim.

A native benchmark should time the complete chain: source chart extraction, graph production, compilation, complete/positive replay, graph-address lifting, and geometric disc construction. Use the same source-certified instances and query outputs in both paths, include failures and negative timings, and charge hierarchy invalidations separately.

## 5. Global complexity target

At `k=3` the new supplied-grammar query is polynomial without component-count or grammar-depth restrictions. The remaining global estimate must bound total emitted grammar data, source discovery/normalization, valid ball terminals, disc transport, and hierarchy resets. Logarithmic graph-description depth is no longer a premise here; small *causal hierarchy depth* is a different, unproved geometric requirement.

No end-to-end quasi-polynomial recognition theorem follows merely from replacing the graph-query operator.
