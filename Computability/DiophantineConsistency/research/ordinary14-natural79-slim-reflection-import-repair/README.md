# Slim divisibility reflection: explicit arithmetic import proposal

This is an inert, source-only alternative to the helper in
[`ordinary14-natural79-dvd-reflection-slim-draft`](../ordinary14-natural79-dvd-reflection-slim-draft/README.md).
The original helper opens the `LO` namespaces and uses `ORingStructure` and
`𝗜𝚺₁` but directly imports only `ModelDifferenceRing` and `Mathlib.Tactic.Ring`.
The checker follows all project-source imports from `ModelDifferenceRing`: it
finds 19 project modules, no missing project source, and only Mathlib leaves.
It also scans the available Mathlib sources and finds no Foundation import.
This identifies a concrete missing source dependency for the model interface;
the earlier import-only provider-cut projection does not include it.

`NaturalDvdReflectionSlim.lean.src` preserves the original bytes exactly after
prepending `import Foundation.FirstOrder.Arithmetic.IOpen.Basic`. The existing
`ArithmeticSignedPairs.lean` uses precisely that direct import with the same
`ORingStructure`/`𝗜𝚺₁` context; the guarded Foundation source's `IOpen.Basic`
publicly imports `Schemata`, which defines the displayed notation. The checker
pins those source observations and the full project closure. The exact Foundation
source inspected resides under the retained `/tmp/ipra-foundation-guarded-v2-cjHUaJun`
workspace, rather than the empty Foundation source directory in this checkout.
This new explicit external import must be added to any future source and
compiled-provider boundary: the previous cut's counts cannot simply be reused.

The fix is a dependency proposal, not a Lean elaboration or proof. It does not
authenticate the Foundation object or companion files, determine its complete
transitive provider boundary, establish instance resolution, check theorem bodies
or tactic execution, or execute the `#print axioms` command. The helper, natural-79
client, overlay, all old receipts, and displayed Carrier65 equation remain
unchanged. This packet does not establish an iPRA proof or equivalence.

An [independent source review](../../reviews/ordinary14-natural79-slim-reflection-import-repair-independent/README.md)
checks the one-import change and the newly exposed external dependency; it
does not establish Lean resolution or provider provenance.

From the repository root, while the pinned temporary Foundation and package
sources remain available, reproduce the deterministic source observations:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-slim-reflection-import-repair/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-slim-reflection-import-repair/result.json
```
