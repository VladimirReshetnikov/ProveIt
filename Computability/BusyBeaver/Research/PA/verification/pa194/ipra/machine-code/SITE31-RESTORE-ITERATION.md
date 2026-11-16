# PRA-model source and state iteration for the site-31 loop

`PA194ModelTransferState.iterPacked` proves by PRA open induction that a model-valued number `j` of updates increases both the physical gap and repeated-spare count by `j`, preserves the spare value, and iterates an arbitrary supplied PR controller-advance code `j` times. `PA194ActualRestoreSource.sourceIteration` specializes the controller advance to the actual triple of site-31, site-32 positive and site-33 source instructions. For `j ≤ register 6`, it yields register 0 + j, register 6 − j, and preserves all other source registers and the independent controller tail. Both the iteration count and input values range over arbitrary PRA models; no IΣ₁ hypothesis is used.

These two invariants are separate model-level results. They do not yet prove an iterated physical run, an iPRA sentence for that run, global simulation, or a consistency implication.

A fresh incremental source replay passed with exit 0, both final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site31-restore-iteration.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-transfer-loop-repo /dev/shm/pa194-site33-jump-repo /dev/shm/pa194-site32-both-physical-repo \
  /dev/shm/pa194-site32-positive-to12-repo /dev/shm/pa194-site32-positive-return-repo \
  /dev/shm/pa194-site32-zero-physical-repo /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-restore-iteration-replay
```

Use a fresh output directory. The checker rebuilds three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
