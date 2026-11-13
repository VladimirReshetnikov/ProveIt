# Natural-80 source materialization blueprint: read-only

This packet derives a **hypothetical source/output path blueprint** from the
reviewed [189-stage natural-80 lexical plan](../ordinary14-natural80-ordered-provider-plan/README.md).
It creates no directory, copies no source, invokes no Lean process, allocates
no resource or output root, and cannot launch a build. Its `blueprint.json`
uses the placeholder `<FRESH_ROOT_NOT_SELECTED_OR_RESERVED>` and must not be
mistaken for a real isolated tree or a reservation.

The inspector rehashes each of the five qualified source files and 184 inert
`.lean.src` snapshots against the ordered plan. It maps a qualified module
such as `DiophantineConsistency.BFS943.Direct80IndexOne` to
`src/DiophantineConsistency/BFS943/Direct80IndexOne.lean`, a bare draft to
`src/<module>.lean`, and each primary object to the corresponding path under
`lib/`. It verifies module-name syntax, safe relative paths, no duplicate source
or primary object names, and no collisions among the **2,457** hypothetical
output names formed using the plan's 13 historical suffixes. The 189 current
source files total **597,347 bytes**; that point-in-time number excludes all
future object files, package/toolchain providers, temporary data, filesystem
overhead and any safety margin. It is not a space estimate or reservation.
The exact source paths, hashes, sizes and proposed destinations are recorded in
`blueprint.json`.

A future separately implemented and independently reviewed materializer could
atomically claim a new private root, create directory components without
following untrusted symlinks, and create each destination exclusively while
streaming and hashing exactly the selected input bytes. It would need to
verify source identity and content before and after copying, reject changes,
protect or revalidate the resulting source and provider files during the
entire run, and retain a receipt for every copy. It must not write into either
the retained P72/base roots or previously captured failed attempts. The
blueprint does **not** implement these operations, prove that a suitable root
exists, reserve disk, or protect inputs from concurrent mutation.

Before any such materialization could serve an actual Lean build, an exact
provider, companion, package/toolchain and runtime plan and an exclusive
resource guard must be independently reviewed; per-stage `lean --deps` must
confirm actual resolution, and all object/companion names and alternate
providers must be checked against the real future roots. A source-only map or
successful copy is not sufficient to establish that the 189 stages elaborate,
that the object chain is coherent, that axiom reports pass, or that an iPRA
proof exists. No physical coefficient or PDF binding is supplied here.

An [independent review](../../reviews/ordinary14-natural80-source-materialization-independent/README.md)
checks the source and output-name projection without materializing a build tree.

Run from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary14-natural80-source-materialization-plan/inspect.py | cmp - research/ordinary14-natural80-source-materialization-plan/blueprint.json
```
