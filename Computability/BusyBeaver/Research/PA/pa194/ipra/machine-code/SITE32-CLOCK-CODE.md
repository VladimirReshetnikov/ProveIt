# Primitive-recursive code for the site-32 positive clock

`PA194Site32PositiveClockCode.clockCode : Code 12` represents the exact clock already used by `PA194Site32PositivePathExact.positivePath`. The kernel-checked theorem `modelClock` proves in every PRA model that evaluating this code on `e : Fin 12 → M` gives `PA194Site32PositiveTo24Exact.clock (e 0) (fun i => e i.succ)`. `PA194Site32CodedPositive.positivePath` substitutes the code directly into the physical 32→33 theorem. Thus the first input is the gap parameter k; the other eleven are the entire logical register file including its suffix slot. The preceding positive physical branch requires `args 6 = m+1` and preserves the rest of that file and suffix.

This is a PR timing code and a model equation for one positive physical branch. It is not yet a coded clock for the full site-31–33 transfer loop, a model-length iteration theorem, a native iPRA loop sentence, a global simulation, or a consistency implication.

A fresh staged source replay passed with exit 0, the final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site32-clock-code.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-positive-exact-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-clock-code-complete-replay
```

Use a fresh output directory. The checker rebuilds five modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier machine and foundation stages remain prebuilt; this replay does not independently authenticate their full transitive closures. The fetch machine-object root is excluded from Lean's search path.
