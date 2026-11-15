# Matched transfer-loop step at a single PR clock

`PA194Site31TransferClockCode.clockCode : Code 14` computes the exact sum of the site-31 clock, the site-32 positive-branch clock at the updated file, and the 34-step site-33 jump. `modelClock` proves that interpretation in every PRA model. `PA194SourceSite31FullyCoded.oneLoop` uses it to prove the corresponding matched actual source/controller and physical loop 31→32→33→31, with a single physical stepper call at the code value.

The first 13 inputs encode source registers 0–8, the independent controller tail, a physical gap parameter, a model-valued repeated-spare count, and an independent spare value. The fourteenth input is the predecessor of the gap parameter. The theorem assumes that predecessor relation and that register 6 is `m+1`. Its output increments register 0, decrements register 6 to `m`, retains all other registers and the controller tail, adds one one-spare to the model-length suffix ending in blank tape, and increases the gap by one.

This is a single model-uniform loop step at a PR-coded clock. Model-length iteration, transfer of this coded statement to native iPRA, full physical simulation and the consistency equivalence remain to be proved.

A fresh staged source replay passed with exit 0, both final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site31-fully-coded.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-coded-loop-repo /dev/shm/pa194-site31-coded-clock-repo /dev/shm/pa194-site31-native-repo /dev/shm/pa194-site32-clock-code-repo /dev/shm/pa194-site32-positive-exact-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site31-fully-coded-replay
```

Use a fresh output directory. The checker rebuilds two modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires both axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
