# Draft guarded driver for the printed-port source extension

This packet prepares, but does **not** launch, the 61 additional modules in
the [source plan](../current14-printed-port-extension-plan/README.md). The
[independent plan audit](../../reviews/current14-printed-port-extension-independent/README.md)
identifies three extra Mathlib modules whose direct objects were not in the
Foundation receipt's declared external guard. The existing assembly and
its syntax client are additional modules and are not built by this driver.

[`driver.py`](driver.py) defaults to a read-only preflight. It refuses
before creating output unless the active fresh base watchdog and base
builder have both recorded successful exits, the base is current at its final
source check, the state digest matches the watchdog receipt, all 1,000 rows
exited 0 in the expected order, and the current sources, frozen sources,
objects, logs, direct-input records and recorded companion guards match. It
also rechecks the Foundation inventory and external guards, the 84-source
plan and its 61-module order, compiler and configuration pins, and free
space. The three new Mathlib object hashes are pinned to the independent
point-in-time observations; their paths, all other extension direct external
modules, object companions and possible search-root shadows are guarded.
These checks do not authenticate transitive external or dynamic ancestry.

Only an explicit `--run`, after that preflight and an idle-Lean check, would
create `/tmp/current14-printed-port-extension-20261104`. Its fresh overlay
places guarded symlinks to the one authenticated base's project objects and
newly compiled extension objects in a single project namespace. It freezes
the 61 source files, checks each `lean --deps` result against declared imports
and the allowed roots, checks each project import against its authenticated
producer and guards direct inputs before and after each module,
and records logs, object hashes and exit status. Each Lean module is bounded
to 1,800 seconds, with sampled free-space checks and a 4 GB stop threshold.
The source and all guards are rechecked at the end. These are sampled checks,
not a reservation or protection against transient mutation.
The captured direct-input hash is compared with its companion guard and
preflight provider; each compiled object is likewise checked against the
recorded output hash before its producer guard is saved.

The [real-base observation](actual-base-refusal.json) confirms the current
base was RUNNING: `--check` exited 1 without creating the extension output.
The [synthetic controls](controls-observation.json) exited 0
and demonstrate refusal of an unfinished or historical base, a stale state
hash, a failed recorded row, modified source/object, unexpected companion,
same-bytes symlink swap, project or external namespace shadow, optimized
Python, and mismatches between recorded and captured input or output hashes.
No Lean process was invoked by those controls. Earlier intermediate
control observations are retained with their original driver hashes.

**The successful preflight and build paths have not been exercised.** An
[independent source review](../../reviews/current14-printed-port-extension-driver-independent/README.md)
found no further acceptance defect within the sampled-guard scope and reran
the refusal controls; it did not run Lean. In particular, namespace
resolution, compiler-reported dependency behavior,
and compatibility with the eventual completed base remain to be observed;
a guarded failure is possible. Nothing here proves a source-current iPRA
endpoint, a printed-port join or TeX/PDF semantics. Do not launch while the
base is running or unless its recorded completion passes all guards.

After a base terminal result and review, read-only preflight is:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-printed-port-extension-driver/driver.py --check
```

The refusal controls use an exclusive observation path; to repeat them,
preserve and move aside this packet's `controls-observation.json` first.
All synthetic fixtures are placed in a fresh temporary directory.

SHA-256: `driver.py`
`32e0b09b31d2998cfb7a78a7414b7f3e87c7c836615a958f3df8a97c68fe2e0e`;
`guards.py` `e42ef7c73da49653b1d664b947c3a9ea5fa2ae78206d0988472a948a901fafc3`;
`controls.py` `2b67a35c1ab2cf8c774a27d8eea82c20bb956cea1b7a1f7fc9bfc2d65796f401`;
`controls-observation.json` `ef28afae145c33670fc682df4c665b655aea22a55978682042dc5ba92c5c82ad`.
