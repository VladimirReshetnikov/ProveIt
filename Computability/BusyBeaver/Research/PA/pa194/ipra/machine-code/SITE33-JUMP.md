# Site-33 source and physical jump

`PA194SourceSite33Controller.controllerStep` proves that the actual encoded source instruction at site 33 jumps to site 31 and preserves the complete register file and controller tail. `PA194Site33Jump.jumpWord` proves a 34-step literal physical run over an arbitrary tape suffix. `PA194Site33JumpPath.jumpPath` identifies its endpoint with the site-31 physical frame, and `PA194SourceSite33Physical.sourcePhysical` combines the source and physical transitions. The file and full suffix are arbitrary and preserved; the gap shifts from `(k+1)+1` to `((k+1)+1)+1`.

The finite row trace used to write `PA194Site33Jump.lean` was generated from an exploratory table listing. The trace itself is not trusted: each row is proved using the pinned table and the all-PRA-model transition lemmas, and the 34-step run is composed in Lean. This is one source instruction, not a complete simulation or a consistency implication.

A fresh staged source replay passed with exit 0, the 34-step and final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site33-jump.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site33-jump-replay
```

Use a fresh output directory. The checker rebuilds four source modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the two final axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier machine and foundation stages remain prebuilt; this replay does not independently authenticate their full transitive closures. The fetch machine-object root is excluded from Lean's search path.
