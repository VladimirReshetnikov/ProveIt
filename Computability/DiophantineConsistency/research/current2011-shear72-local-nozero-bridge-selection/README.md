# Isolated local no-zero bridge for the 72/46 endpoint

The historical `OrdinarySphere7160IPRA` source already uses `HAExpressionAssembly.classicalNoZero_iff` and its `PolynomialBridge` interface. The existing `HAExpressionNoZeroEquiv.bridge` proof unfolds exactly that no-zero evaluation equivalence and composes it with the parent polynomial bridge. Thus a separate inert conditional-client alternative defines the identical `SameNoZero` proposition locally and repeats that short source-level argument using the already imported historical 71 interface. The exact `ParentToChild` and `ChildToParent` propositions and native, standard and mapped-GG endpoint statements and bodies are preserved. The joint-client alternative removes the old namespace opening, allowing its same-no-zero type to resolve to the local interface. No map, literal or older source is changed.

`selection.json` changes only those two draft entries and drops `DiophantineConsistency.HAExpressionNoZeroEquiv` from the **direct** draft frontier relative to the preceding order/carrier selection. All other selected paths, hashes, direct headers and frontiers stay identical. This does not assert that the module is absent transitively, or that the historical 71 object was built with the desired provider. The direct parent bridge, no-zero interpretation, name resolution, rewritten proof, source/object selection and iPRA theorem all remain unelaborated and unauthenticated in this combination. This is neither a proof of either consistency sentence nor a proved degree-46 equation endpoint.

The checker reconstructs the exact source edits, verifies the local interface and bridge proof against the existing generic and historical 71 source statements, checks the preserved theorem tail byte-for-byte, and validates every selected draft edge and direct frontier in topological order. It does not parse or run Lean, resolve transitive imports, inspect compiled objects, or produce axiom reports. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/current2011-shear72-local-nozero-bridge-selection/check.py | cmp - research/current2011-shear72-local-nozero-bridge-selection/receipt.json
```

No Lean/build/staging or old-source mutation occurred.
