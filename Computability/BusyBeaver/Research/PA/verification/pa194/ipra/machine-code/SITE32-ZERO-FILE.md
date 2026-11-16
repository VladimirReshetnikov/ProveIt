# Site-32 zero rollback and file identity

`PA194Site32ZeroRollbackCell.rollback` proves the all-PRA-model physical zero-decision route from dense control 4 through control 11, including the nine-slot rollback, with an explicit clock and arbitrary initial left base, register values, spare and complete suffix. `PA194Site32ZeroFile.returnedIsSourceFile` separately proves that its returned file equals the original encoded source file when logical register 6 is zero. The connection to the site-32 physical entry and subsequent return to site 34 remain to be composed; no full source/physical step is claimed.

A fresh incremental replay passed with exit 0 and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-zero-file.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo \
  /dev/shm/pa194-site32-to1-repo /dev/shm/pa194-site32-second-root-repo \
  /dev/shm/pa194-site32-return-header-repo /dev/shm/pa194-site32-first-pass-repo \
  /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-zero-file-replay
```

Use a fresh output directory. The checker rebuilds the two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, and records source, direct object/companion and upstream receipt hashes. Prior machine and general foundation stages remain prebuilt, and this incremental replay does not independently authenticate their full transitive object closures. The fetch machine-object root is excluded from Lean's search path.
