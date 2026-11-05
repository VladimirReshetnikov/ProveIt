# Independent review of the printed-port extension driver

Reviewed the revised [guarded extension driver packet](../../research/current14-printed-port-extension-driver/README.md)
read-only. No unsafe acceptance defect was found within its stated sampled
guard scope. The review inspected the base watchdog and 1,000-row gate, the
84-source/61-module plan and order checks, Foundation inventory, static and
direct-import guards, namespace shadow refusals, per-module checks, and final
reauthentication. The pinned base manifest has 1,000 unique modules with the
expected endpoint module last. Independently rehashed all six static pins and
the three newly introduced direct Mathlib objects. The actual pinned
source-plan gate passed for 84 rows, 61 extra project modules and 31 direct
external modules, including the expected three new ones; project and external
top-level namespaces are disjoint.

The revised producer checks address two review findings: project imports are
compared against the authenticated base-overlay or earlier freshly compiled
producer guards, and the scanned direct-input and produced-object hashes are
compared with the corresponding recorded hashes. External direct imports are
also compared with the preflight guards. The author added refusal controls for
recorded-input and producer-output capture mismatches. An additional separate
temporary-file check applied the driver's project-producer equality test to a
same-bytes symlink switched to another producer; it refused the substitution.

Reran the revised synthetic controls in a disposable `/tmp` copy of the three
Python files, with the required plan and configuration paths linked to the
repository. The process exited 0 and reproduced all recorded refusals,
including the new input/producer capture mismatches; the copy's driver and
guard hashes matched the reviewed originals. The controls invoked no Lean and
did not edit the author packet. The author's observation receipt also names
the revised driver and guard hashes.

This review does **not** exercise a successful preflight against a completed
base or a successful extension build. The controls are negative-only and do
not prove successful namespace or `lean --deps` resolution. Package-transitive
and dynamic dependencies and transient changes between checks remain outside
the guarded observations. It does not establish an iPRA endpoint, printed
coefficient binding, or TeX/PDF semantics.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `driver.py` | `32e0b09b31d2998cfb7a78a7414b7f3e87c7c836615a958f3df8a97c68fe2e0e` |
| `guards.py` | `e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3` |
| `controls.py` | `2b67a35c1ab2cf8c774a27d8eea82c20bb956cea1b7a1f7fc9bfc2d65796f401` |
| author `controls-observation.json` | `ef28afae145c33670fc682df4c665b655aea22a55978682042dc5ba92c5c82ad` |
