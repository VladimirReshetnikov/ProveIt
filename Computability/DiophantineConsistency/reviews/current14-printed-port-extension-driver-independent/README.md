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
The further base-log change reparses the endpoint's four exact axiom-report
names and values from the hashed target log and compares them with the ledger.
It also explicitly requires the pinned target to be the last base row.

Reran the revised synthetic controls in a disposable `/tmp` copy of the three
Python files, with the required plan and configuration paths linked to the
repository. The process exited 0: it accepted a complete synthetic 1,000-row
base gate, rejected a forged target axiom-report name despite coherent log
and ledger hashes, and reproduced the other recorded refusals. The copy's
driver and guard hashes matched the reviewed originals. The controls invoked
no Lean and did not edit the author packet. The author's observation receipt
also names the revised driver and guard hashes.

This review does **not** exercise a successful preflight against a completed
base or a successful extension build. The synthetic base-gate acceptance does
not prove successful full preflight, namespace or `lean --deps` resolution. Package-transitive
and dynamic dependencies and transient changes between checks remain outside
the guarded observations. It does not establish an iPRA endpoint, printed
coefficient binding, or TeX/PDF semantics.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `driver.py` | `97fabce00462b878ce9c91fd60ffbc54030350b06e564a0578a62dc5550971e1` |
| `guards.py` | `e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3` |
| `controls.py` | `1f726b45adf844e91ca45b218ab106852d03669d39f270021ad333c9af774545` |
| author `controls-observation.json` | `93d0acb229802150500fcb3f151bbc3df7fcddde661a4dc5dc732be13aabf30b` |
