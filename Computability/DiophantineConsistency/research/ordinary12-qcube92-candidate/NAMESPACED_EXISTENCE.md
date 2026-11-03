# Namespaced positive-existence theorem

A first halt-join build failed with Lean's duplicate-declaration error:
`QCube92Existence` imported the module `FreeJRootBinding`, while the fixed
halt provider imports `DiophantineConsistency.FreeJRootBinding`; both define
the same declaration names. The exact source, runner, stderr, selected
1,292-file union and before/after checks for that failed run are retained in
`observations/halt-attempt01/`.

`QCube92NamespacedExistence.lean` changes the binding import to the same
namespaced module used by the halt provider, and changes its own namespace.
Its remaining proof source is identical to `QCube92Existence.lean`. The
selected namespaced binding object has SHA-256 `58860b9c6f256a15df038991edc682af4b4c831ab0ae3c3565f1f14ea4833b40`:
this is byte-identical to the earlier replay of the unchanged binding source
SHA-256 `5d826d8f1cf5ce4a11c45f4a6762ba0729a5e282a1356bce0aeb02f49c58083b`.

The separately compiled `positive_zero_iff` has the same all-IΣ₁-model,
positive-witness statement and positive-β assumption described in
[EXISTENCE.md](EXISTENCE.md). The guarded author run
`observations/namespaced-attempt01/` exited 0 in 6.9 seconds, with no warnings
or `sorryAx`. Both named reports list `[propext, Classical.choice, Quot.sound]`
as Lean metatheory axioms. The source and runner SHA-256 hashes are
`5b47d82b5ad78815983773588bb6c9822b6646ae0a6595a600b7f639f424c81a` and
`f1f502a77323e2af28cf46224cac2120a4915602d8945774f0242b4530a2b122`.
Two sampled resource observations recorded one Lean process and a minimum
18,506,220 KiB MemAvailable; between-sample changes are not excluded.

The runner checks the 1,288-file fixed-port union, adds the four earlier
92-proof objects, guards the documented search-path overlaps, pins the
independent serialized-ancestor review and all of its inputs, and rechecks
the union and inputs after compilation. These are selected-project checks;
full historical source-to-object, package-transitive and dynamic ancestry
remain inherited. The theorem does not itself establish the fixed-port halt
claim, interpret files or PDF in Lean, or supply an iPRA derivation. A fresh
serialized-import check for the newly compiled namespaced object is separate.
