# Incremental Lean endpoint check

**PASS:** all 201 current K215 project modules and 14 additional legacy modules
have matching current sources, direct dependency object hashes and checked
objects. Affected modules were recompiled against an independent copy of the
[previous fresh 204-module build](../../lean/README.md); that original cache and
its published receipts are unchanged. This is an incremental validation, not a
new full replay.

Both typed clients passed with zero warnings:
[endpoint output](EndpointAudit215.log) and [component output](K215Audit.log).
Their ten axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The selected project closure retains 31 linter warnings. Its sole external
project-import boundary is the installed Lean `Init` library.

The [result and module ledger](result.json) bind every current source, import,
object and compiler log. The [execution archive](execution.tar.gz) and
[member hashes](execution-index.json) preserve all incremental compiler attempts,
source snapshots, raw logs, actual checker scripts, the final audits and the
five-file [exact generator comparison](generators.json). Failed run-equation
proof drafts and the namespace repair in the legacy Dom root remain in that
history. The [independent source/object and saved-record review](independent-review.json)
checks these bindings without invoking a compiler. No failed attempt supplies a final object. The endpoint, register
contracts and machine are unchanged.

The historical incremental scripts refer to their actual scratch paths. For a
fresh full replay on another machine, use the portable driver from the repository
root with Lean 4.32.0:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py \
  --out /tmp/k215-lean-simplified
```

Use an empty output directory. The portable driver computes the current import
closure and serializes proof invocations with the shared Lean/Rocq lock.
