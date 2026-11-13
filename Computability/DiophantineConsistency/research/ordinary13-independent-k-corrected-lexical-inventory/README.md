# Corrected independent-k composition: bounded lexical source inventory

This is a **read-only partial source-selection inventory**, not a Lean environment, build plan or proof. Its root is `IndependentKPositiveCorrectedComposition`, and it traverses local import names while preserving source hashes and a dependency-first order in `manifest.json`.

The scanner follows the earlier fixed85 lexical approach, with these explicit JSON-only choices:

* The corrected composition root is the named research source.
* For a logical name present in the earlier fixed85 selection, it uses that JSON plan's pinned source when its hash still matches; this accounts for 691 selected names. None of those reachable names uses one of that plan's nine alternate files.
* For other bare names, it scans `research` for matching `.lean` or `.lean.src` basenames and selects only when observed bytes form one class. Dotted project names are looked up at their corresponding path under the local `Lean` directory. Missing names and multiple distinct candidates stop traversal.

At this snapshot the partial closure contains 821 selected names, including the corrected rank helper, child unit graph and bridge, child J-positive source, fixed compact client, zero-k graph facts, corrected first-rank client and main-norm helper. It has no local lexical cycles. The bounded scan observed no byte-distinct collisions among these selected names and no ambiguous frontier; this is **not** a global uniqueness statement. It does not inspect arbitrary source roots, package resolution precedence or compiled objects.

There are 46 unresolved import names at the traversal boundary: 39 Mathlib, four Foundation and three BusyBeaver names. The separate `frontier_source_observations` field records exact existing source paths and hashes at the named Mathlib, vendored Foundation and BusyBeaver roots, but does not follow their imports or select them as providers. For each of the three BusyBeaver names, the checked canonical source and 31 `reviews/*/sources` copies have identical observed bytes. The observation is bounded to those patterns; other historical copies or compiled objects are outside scope.

The manifest's JSON selections and source observations do not authenticate package roots, source/olean agreement, transitive provenance, object-name collisions, the toolchain, tactic elaboration, `#print axioms`, proof theory, iPRA, the displayed equation or any endpoint. In particular, nine isolated source alternatives from the older fixed85 plan are **not** selected merely because they appear in that broader plan; this inventory traverses only dependencies reachable from the corrected child. The scanner is line-based, not a Lean parser; it can miss conditional or unusual import syntax. Local sources and bounded frontier files must remain byte-identical for the receipt to reproduce.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-independent-k-corrected-lexical-inventory/check.py | cmp - research/ordinary13-independent-k-corrected-lexical-inventory/receipt.json
```

The check regenerates the partial selection, verifies hashes and the local order. It does not execute Lean, stage files, inspect objects or start a build.
