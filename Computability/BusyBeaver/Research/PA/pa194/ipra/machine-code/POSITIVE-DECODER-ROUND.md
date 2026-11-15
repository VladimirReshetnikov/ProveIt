# Matched positive decoder round

`PA194SourcePositiveDecoderRound.positiveRound` matches the actual source-controller sequence 34→35→36→37→41→34 with its literal physical execution in every PRA model. It assumes registers 6 and 8 are positive, input gap `k+5`, and numeric suffix `repeatOutput(count, 0)` for an arbitrary model-valued count. The round decrements registers 6 and 8, increments register 7, appends one repeated-spare block, preserves the other registers and controller tail, and returns with gap `k+7`.

The physical run has three existential model-valued segment clocks; this is one round, not a primitive-recursive clock code, model-length loop, or native iPRA sentence. Build order: `PA194Site36PositiveClockExists.lean`, `PA194SourceSite36PositiveReturn.lean`, `PA194Site35ClockExists.lean`, `PA194SourcePositiveDecoderRound.lean`.

Fresh staged replay passed with exit 0 using my site-37 stage. The invocation below substitutes the repository-rebuilt stage; use a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-positive-decoder-round.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site37-physical-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
  /dev/shm/pa194-site34-branch-repo /dev/shm/pa194-site34-second-pass-repo /dev/shm/pa194-site34-to14-repo /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-positive-decoder-round-repo \
  /dev/shm/pa194-site41-physical-repo \
  /dev/shm/pa194-site36-positive-physical-repo \
  /dev/shm/pa194-site32-positive-exact-repo \
  /dev/shm/pa194-site36-zero-physical-repo \
  /dev/shm/pa194-site36-branch-repo \
  /dev/shm/pa194-site36-marked-entry-repo \
  /dev/shm/pa194-site36-second-pass-repo \
  /dev/shm/pa194-site36-second-to14-repo \
  /dev/shm/pa194-site36-first-pass-repo \
  /dev/shm/pa194-site36-gap-dispatch-repo \
  /dev/shm/pa194-site36-to42-repo \
  /dev/shm/pa194-site38-zero-physical-repo \
  /dev/shm/pa194-site38-zero-to16-repo \
  /dev/shm/pa194-site38-zero-to14-repo \
  /dev/shm/pa194-site38-zero-to12-repo \
  /dev/shm/pa194-site38-zero-rollback-repo \
  /dev/shm/pa194-site38-branch-repo \
  /dev/shm/pa194-site38-to4-repo \
  /dev/shm/pa194-site38-to1-repo \
  /dev/shm/pa194-site38-second-pass-repo \
  /dev/shm/pa194-site38-second-to14-repo \
  /dev/shm/pa194-site38-first-pass-repo \
  /dev/shm/pa194-site38-second-to71-new \
  /dev/shm/pa194-site38-second-to95-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their complete transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
