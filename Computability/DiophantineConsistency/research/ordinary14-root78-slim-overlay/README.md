# Isolated source-only slim-helper overlay for root 78

This packet preserves the committed endpoint chain and supplies a separate,
complete copy of its 138 reachable bare draft modules plus the reviewed
`CompactPortBoundsSlim` helper. The files in `source/` use the suffix
`.lean.src` intentionally: they are inert source snapshots, so they do not
collide with the original research-wide Lean module lookup. To use them in a
future isolated build, copy them to a new source root with the `.src` suffix
removed; do not mix their module names with the original chain. No such build
or materialization is performed here.

Six snapshot modules differ from the reviewed originals, solely by four import
replacements and six qualified `port_bounds` references. The four imports now
resolve the bare `CompactPortBoundsSlim` module; its namespace is
`DiophantineConsistency.CompactPortBoundsSlimDraft`. The two clients that do
not directly import the helper reach it through their existing bare imports.
The checker verifies this reachability, the exact source bytes and source hashes,
all module names, acyclicity, and the `Root78Endpoint` dependency path. The
helper itself is byte-identical to the separately reviewed source draft.

`inventory.json` records topologically ordered overlay snapshots, original and
overlay hashes and byte counts of all changed files, direct qualified imports,
and a recursive lexical initial-header inventory of reachable project sources.
This snapshot has 139 draft modules, 27 direct qualified imports, 1,125
reachable project source files, and 92 external names at the project-source
boundary. The parser strips nested comments and recognizes common header
modifiers; this is not Lean's import resolver, so the inventory is a planning
view, not an authoritative full dependency closure. `C44Short15Facts` is absent
from this lexical project-source route. External package/toolchain transitive
imports, generated dependencies, objects, companions, and provider provenance
are not established by this packet.

Run, from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root78-slim-overlay/check_source.py | cmp - research/ordinary14-root78-slim-overlay/inventory.json
```

This is an unelaborated source refactor, not a proof that the new import,
namespace, model bridge, iPRA endpoint, provider objects, or physical byte/PDF
binding work. The current disk floor still prohibits a Lean run. Independent
source review is requested.

Independent source review: [root78 slim overlay](../../reviews/ordinary14-root78-slim-overlay-independent/README.md).
