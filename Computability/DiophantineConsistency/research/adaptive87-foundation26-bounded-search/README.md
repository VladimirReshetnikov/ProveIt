# Bounded search for 26 historical Foundation objects

The recorded search found **no exact hash match** for any of the 26 Foundation
objects identified as unavailable in the pinned
`adaptive87-peer-nonproject-frontier` receipt. It found at least one readable,
differently hashed candidate for every name. The receipt lists each expected
hash, exact matches (empty at this observation), the number of different
physical candidates, and up to two candidate paths and hashes per name.

This is a point-in-time search, not a proof of global absence. The checker
examines immediate `/tmp` children for `Foundation` under each of these five
layouts: `lib`, `package-lib`, `.lake/build/lib/lean`, `lib/lean`, and the
child itself. It also tries the historical `/home/codex/src/Proofs/.lake/build/lib/lean/Foundation`
and this worktree's `.lake/build/lib/lean/Foundation`. It resolves and
deduplicates the resulting Foundation roots before checking the 26 exact
module-relative `.olean` paths. It does not recursively search arbitrary
nested roots, other users' directories, archives, caches or network stores.

At the recorded observation this comprised 2,364 logical `/tmp` roots and
986 distinct roots including the explicit paths, 60 readable physical objects,
and 21,974 broken candidate symlinks. Seven top-level temporary directories
were inaccessible and are listed in the receipt. A broken symlink is counted
per candidate path; these are not 21,974 distinct objects. Readable candidates
include the separate Foundation rebuilds, but different hashes alone do not
prove Lean incompatibility or establish a coherent replacement environment.
The older provider inventories retain the expected hashes; their recorded
historical bytes do not by themselves establish a currently accessible copy.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B research/adaptive87-foundation26-bounded-search/check.py | cmp - research/adaptive87-foundation26-bounded-search/receipt.json
```

The checker pins the prior frontier receipt, reads only, and reports current
filesystem observations. The exact byte comparison is expected to change if
new temporary directories, object files or permissions change; such a change
requires examination rather than being treated as a proof failure. No Lean,
build, staging, copy or mutation of provider evidence was performed.
