# Matched transfer-loop step with explicit coded-clock sum

`PA194SourceSite31CodedLoop.oneLoop` proves in every PRA model one matching actual source/controller and physical loop 31→32→33→31, with one exact physical run whose time is the sum of the site-31 PR clock, the site-32 positive-branch PR clock, and 34. The 13 input values `e` encode registers 0–8, the independent controller tail, a physical gap parameter, a model-valued repeated-spare count, and an independent spare value. For `e 10 = k+1` and `e 6 = m+1`, the physical frame output increments register 0, decrements register 6 to `m`, retains all other register values and the controller tail, adds one one-spare to the model-length suffix ending in blank tape, and increases the gap by one.

This theorem is one model-uniform loop step and exposes a sum of two PR codes, but does not yet package the whole sum as one PR code, prove model-length iteration, transfer that iteration to native iPRA, establish full simulation, or prove a consistency implication.

A fresh incremental source replay passed with exit 0, both axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-coded-loop.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-coded-clock-repo /dev/shm/pa194-site31-native-repo /dev/shm/pa194-site32-clock-code-repo /dev/shm/pa194-site32-positive-exact-repo \
  /dev/shm/pa194-site33-jump-repo /dev/shm/pa194-site32-both-physical-repo \
  /dev/shm/pa194-site32-positive-to12-repo /dev/shm/pa194-site32-positive-return-repo \
  /dev/shm/pa194-site32-zero-physical-repo /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-coded-loop-replay
```

Use a fresh output directory. The checker rebuilds two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
