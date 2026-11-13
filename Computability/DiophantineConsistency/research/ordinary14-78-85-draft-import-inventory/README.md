# Static draft import inventory for compact 78↔85

This no-Lean inventory starts at `Compact78To85.lean`, follows only bare
modules in the initial import headers of the source drafts, requires each bare
module name to resolve to exactly one research `.lean` file, detects cycles,
and emits dependency-first order and SHA-256 hashes. At capture it finds 62
draft sources and 19 **directly named** qualified modules whose source paths
exist under `Lean/`; the inventory records those source hashes too.

This is **not** a Lean build plan, provider or object ancestry audit. It does
not recursively traverse the qualified modules' imports, inspect `.olean`
objects, establish search-path resolution, validate source/toolchain versions,
check elaboration, allocate memory or disk, or establish that the proposed
model comparison is true. It is a static source inventory for planning a
future guarded build. The hash receipt will intentionally change when any
captured source changes; review links in READMEs are not captured.

Run `python3 -I -S -B check_source.py` and compare stdout with `inventory.json`.
No Lean is invoked.

Independent source review is recorded in
`../../reviews/ordinary14-78-85-draft-import-inventory-independent/`.
