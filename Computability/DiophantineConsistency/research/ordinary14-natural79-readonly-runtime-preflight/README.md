# Natural-79 runtime observations: read-only and non-launching

`preflight.py` has exactly two modes and cannot launch Lean, materialize
sources, write an output, reserve disk, or start any subprocess. Unsupported
arguments fail. Both modes state `launch_authorized: false` unconditionally.
This is deliberately **not** an executable build guard or permission to build.

`--static` pins the corrected 201-stage plan; checks each selected source's
hash, simple lexical import order and distinct primary output name; checks the
41 project and six external frontier source/object paths, realpaths and hashes
against that plan; and checks `lean-toolchain` plus the local Lean binary hash.
The Lean executable is only a previously observed local file, not an
authenticated compiler distribution. Its hash does not establish dynamic
library, package, toolchain, transitive object, companion or producer identity.
These source and object checks do not prevent changes immediately afterwards.
The deterministic receipt is `static.json`; no Lean command runs.

`--observe` separately reports `statvfs` available bytes at the workspace and
`/tmp`, applying the **strictly greater than 5,100,000,000 bytes** threshold to
each. It samples `/proc` for processes whose executable or `argv[0]` basename
is exactly `lean` or `lake`, and explicitly counts inaccessible or vanished
process entries. A nonzero inaccessible count makes process absence unknown;
even zero matches and zero inaccessible entries cannot establish durable
exclusivity. It cannot recognize every wrapper, alternate executable or host
process. Disk counts and process results are volatile and are intentionally not
stored in the deterministic receipt. No output paths, files, locks, processes,
resources or input snapshots are atomically reserved. Any future build needs a
separately reviewed guard, full provider/companion and runtime authentication,
actual import resolution, collision handling and ongoing disk/process checks.

Run from `Computability/DiophantineConsistency` while the pinned temporary
providers exist:

```sh
python3 -I -S -B research/ordinary14-natural79-readonly-runtime-preflight/preflight.py --static | cmp - research/ordinary14-natural79-readonly-runtime-preflight/static.json
python3 -I -S -B research/ordinary14-natural79-readonly-runtime-preflight/preflight.py --observe
```

This packet establishes no Lean theorem, proof existence, iPRA equivalence, or
binding to the separately displayed equation. It does not modify prior evidence.

An [independent review](../../reviews/ordinary14-natural79-readonly-runtime-preflight-independent/README.md)
checks the source operations and mocked observer boundaries. In particular,
`--observe` returns success even when space is insufficient; it is an observer,
not an enforceable build guard.
