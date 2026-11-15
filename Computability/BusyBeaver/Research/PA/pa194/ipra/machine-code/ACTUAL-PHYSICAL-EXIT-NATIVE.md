# Native iPRA: physical loop and site-31 zero exit

`PA194ActualPhysicalCodedExitSentence.nativeIPRA` is an explicit universally
closed equality in native `standardTheory`. Its 13 inputs are the nine source
register values `r0` through `r8`, an independent controller tail, a padding
parameter `k`, a count `n` of repeated one-valued trailing blocks, and the
spare-block value. It starts the literal PA194 encoded stepper at the coded
site-27 frame with gap `k+3`, executes `r0` iterations of the positive source
loop, then takes the zero branch to site 31. The displayed total time is the
sum of the PR-coded loop clock and the PR-coded zero-branch clock evaluated
at the intermediate frame. The output frame has site 31; register 0 is
`r0−r0`, registers 6 and 8 each increase by `r0`, gap increases by `r0`,
and the count of trailing one-valued blocks increases by `2*r0`. Other
registers, spare value, and the independent controller tail are preserved.
The suffix following those repeated blocks is blank.

`PA194Site27ZeroClockSentence.nativeIPRA` separately proves the exact
site-27-to-site-31 physical zero branch with the tested register syntactically
zero; the other entries and the full suffix are arbitrary. The clock is the
Code-12 value proved correct by `PA194Site27ZeroClockCodeSplit.modelClock`.
`PA194ModelLoopFrameAt` gives a physical frame code for any externally fixed
source site, and `PA194Site27ZeroCostInput` supplies its packed clock inputs.
`PA194Site27ZeroCodedStep` proves the coded zero branch conditional on clock
correctness, `PA194ActualPhysicalCodedExit` composes it with the physical
loop, and the final native sentence discharges the clock condition.

The comprehensive source replay `check-actual-physical-exit-native.sh` has
passed with exit 0 (`/tmp/pa194-actual-physical-exit-native-check.log`). It
rebuilds the full previously handed-off native physical loop, twelve existing
zero-branch source modules, and the nine new source modules listed below in
one temporary output. Every reported model, classical PRA, and native iPRA
theorem axiom audit is free of `sorryAx`. Its first 26 arguments are those in
`ACTUAL-PHYSICAL-ORBIT.md`; argument 27 is the zero-branch source directory
`/dev/shm/pa194-site27-zero`. The retained machine and foundation overlays are
prebuilt; direct hash, overlap and unchanged-input audits do not authenticate
their complete transitive source closure. This is one loop and its exit, not
a full source-machine simulation or either consistency implication.

The nine new sources are `PA194Site27ZeroExactClock.lean`,
`PA194Site27ZeroClockPhysical.lean`, `PA194Site27ZeroClockCodeSplit.lean`,
`PA194Site27ZeroClockSentence.lean`, `PA194ModelLoopFrameAt.lean`,
`PA194Site27ZeroCostInput.lean`, `PA194Site27ZeroCodedStep.lean`,
`PA194ActualPhysicalCodedExit.lean`, and
`PA194ActualPhysicalCodedExitSentence.lean`. The existing zero-branch source
files, the native loop sources, pinned direct machine objects and the audited
theorem names are listed in the checker.

From the repository root, the successful invocation was:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-actual-physical-exit-native.sh "$PWD" \
  /dev/shm/pa194-model-length /dev/shm/pa194-source-controller \
  /dev/shm/pa194-source-physical /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-site28-controller /dev/shm/pa194-site28-work/build-complete \
  /dev/shm/pa194-site28-work/build-finish-return \
  /dev/shm/pa194-site28-work/build-site29-selected-return \
  /dev/shm/pa194-site28-work/build-carry-seven \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-codes \
  /dev/shm/pa194-site28-work/build-site29-to-increment \
  /dev/shm/pa194-site28-work/build-site29-return-to-root \
  /dev/shm/pa194-site28-work/build-site29-path30-identities \
  /dev/shm/pa194-site28-work/build-site29-complete \
  /dev/shm/pa194-site28-work/build-site28-dynamic-complete \
  /dev/shm/pa194-site28-work/build-site29-dynamic-complete \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-site30-jump \
  /dev/shm/pa194-site28-dynamic-controller \
  /dev/shm/pa194-site29-dynamic-controller Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site27-zero
```
