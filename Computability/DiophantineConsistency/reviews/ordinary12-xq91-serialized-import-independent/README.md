# Serialized-import audit for the 91-operation proof objects

The observed selected-project closures of `XQ91` and `XQ91Model` have 30
and 31 names respectively, counting the root. Their actual headers import
`QCube92` and `XQ91`, respectively. Their first-resolved selected project
ancestors match the hashes of the corresponding 92-halt union or the
recorded new 91 proof objects. Neither 91 proof root reaches the older
`FreeJOrdinaryTailWitness` object on its author search path.

The scan also reads the actual headers of the 92 halt object and the selected
`DiophantineConsistency.FreeJRadixAlignment` object. The latter has SHA-256
`ebc83df3fa0343d2e20f265927c715e9bf813b79cb5338c72540ec3f6dfe84e4` and its
header matches the prior captured inventory. It is the namespaced alignment
module used by the proposed fixed-port client. The 92 halt header imports the
namespaced existence bridge and the two existing symbolic and byte-port model
modules.

For the **proposed** client imports `XQ91Model`, `QCube92Halt`, and
`DiophantineConsistency.FreeJRadixAlignment`, the union of captured
selected-project ancestors has 741 names and excludes the conflicting
top-level names `FreeJRootBinding`, `QCube92Existence`, `FreeJRadixAlignment`,
and `FreeJSignedTransport`. It includes their appropriate namespaced
binding, alignment and signed-transport modules. It also includes
`FreeJOrdinaryTailWitness` through the previously accepted 92 halt side: that
module must use the 92 halt union's `3af9bb5c…` object, rather than the
`b36cc3c0…` object on the 91 author path. This is a predicted closure for
those three imports, not a captured header or proof of a subsequently
compiled 91 halt client.

`scan.py` checked the 91 and 92 producer receipts and object hashes, read the
four object headers in one Lean `readModuleData` invocation, and traversed the
previously captured selected-project import inventory. For each root it
resolved project imports in that producer's recorded `LEAN_PATH` order and
checked their hashes against the prior header object and the selected 92
halt union or the appropriate new proof object. The exact complete per-root
paths and hashes, direct headers, planned closure and outside names are in
`observations/attempt01/result.json`, SHA-256
`87f7fad28524346b6921bda2f180f763417e98a0209063a7fae7fb579aea3787`.

The reader exited zero in about 0.51 seconds. Its pre-launch sample saw
18,622,220 KiB available and no Lean process; its post-launch sample saw
18,633,740 KiB and no Lean process. The guard required at least 8 GiB and
fewer than two pre-existing Lean processes; the reader had a 3-GiB Lean cap
and 60-second timeout. Point samples do not exclude overlaps or memory dips
between observations.

`audit.py` independently reparses the captured headers, reconstructs each
closure and the proposed combined closure, rechecks first-resolved paths and
hashes, and reruns the earlier 91 model and 92 halt read-only reviews. Run
`python3 -I -S -B audit.py`; its successful captured output is
`observations/audit01.stdout`. These tools require the recorded absolute
`/tmp` providers and outputs. The scan refuses to overwrite its observation.

The proposed closure has 44 outside names, whose package-transitive imports
were not traversed. Dynamic loading and complete historical source-to-object
ancestry remain inherited. The scan is not a general guarantee that an
arbitrary mixed provider is compatible, a Lean proof of the proposed client,
or an internal iPRA derivation.
