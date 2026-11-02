# Declared source closure for the thirteen-variable restoration

This is a static planning snapshot, not a Lean build or a checked compiled
import closure. `prepare.py` parsed the current declared source imports for
`DiophantineConsistency.ModelThirteenRestoration` into the fresh directory
`/tmp/ipra-thirteen-restoration-source-survey-01`. Actual session 63515
exited 0 and printed:

```
FROZEN_NOT_COMPILED 1140 project modules 111 direct external modules fcc52c38ba2b7ccd54b8125a9ec600ecc63a9641851cd03744146c6de95e0ff4
```

The pinned [manifest](manifest.json) records source SHA-256 values, declared
edges, workspace paths, and the then-current Git HEAD
`dc906096f1ed93218d2653c894e706049366b722`. The first-party freezer's own
hash was `b238a5ddca6509913f88f05bd891f6219df400dbc211259a6e8623df178deacc`.
The separate `audit_snapshot.py` process, actual session 7258, exited 0 and
printed `PASS_SOURCE_SNAPSHOT_AUDIT 6cbe802a4330c64af00034c0883a7fe54ecf8b094577ab0c181e4c1c5409f5b6 tracked 1140 changed 0 untracked 0`.
Its [receipt](source-audit.json) and source pins reflect that moment; later
workspace changes are possible. Its script hash was
`9f1bd0cee7feb74f5fcdd96c2217b4684ddfcf33f0d37a244c66f9fe85e7b328`.

The read-only `python3 -I -S compare.py` actually exited 0. It checks both
manifest hashes and reports 64 common modules with equal source bytes, 1,076
modules only in this survey and six only in the previously audited 70-source
snapshot. This count neither authorizes reuse of compiled objects nor checks
transitive package imports or dynamically loaded inputs. A coherent rebuild
needs independently reviewed ancestry, provider, namespace and resource
guards; no such build of these 1,140 modules is claimed here.
