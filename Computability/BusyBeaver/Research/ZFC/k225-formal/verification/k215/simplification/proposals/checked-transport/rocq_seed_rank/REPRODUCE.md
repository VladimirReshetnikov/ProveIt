# Reproduce

Run with Coq 8.18.0 (the locally verified toolchain):

```sh
python3 reproduce.py --out /tmp/k215-seed-rank-fresh
```

It compiles ten project modules and one typed client, prints six closed
assumption reports, and runs recursive `coqchk`. Only the standard library is
needed. It writes all generated sources, objects, complete raw logs and the
receipt into the specified fresh directory. Compiler calls use the shared
`/tmp/proveit-proof-compiler.lock` convention.

`--baseline` checks the ten preserved original sources and old client interface.
`--skip-kernel` skips the second recursive pass but still performs the ordinary
proof-assistant kernel checking during compilation. Coq 8.x build copies use
the `Coq` spelling of the standard-library namespace in place of `Stdlib`.
No compatibility theorem is assumed. Other toolchain versions are not claimed
as reproduced by the retained local evidence.

The delivered `verification/final-receipt.json` was produced by the original
session runner; it retains the original absolute paths and exact executed
commands. The portable successor above performs the same source edits, module
order, commands and checks in a caller-selected directory. Compiled objects
are intentionally omitted. `verification/first-ranking-check.json` is an
intermediate record before the opacity improvement; it is not the final build.
