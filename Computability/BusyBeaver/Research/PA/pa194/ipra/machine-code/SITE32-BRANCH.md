# Site-32 physical decision branches

`PA194Site32Branch.zeroTo5` proves the literal physical run reaches dense state 5 when logical register 6 is zero. `positiveTo6` proves it reaches dense state 6 when register 6 is a successor. Both quantify arbitrary other registers and the complete suffix, and give the exact decision-point tape shape with existential clock and left-tape value. The previously staged `PA194Site32To4.to4` retains its exact clock and carried word.

`PA194CarryEightAppendZero.eightThenZero` is the all-model nine-slot carry identity needed for the zero-branch rollback. Neither decision theorem has yet been followed back to its source-frame destination, and this increment does not prove the complete source/physical synchronization.

The following fresh incremental source replay passed with exit 0, the two branch axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site32-branch.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-branch-replay
```

Use a fresh output directory. The checker rebuilds the two sources, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both branch axiom audits, and records source, direct object/companion and upstream receipt hashes. The earlier physical and general foundation stages remain prebuilt; this incremental replay does not independently authenticate their full transitive object closures. The fetch machine-object root is excluded from Lean's search path.
