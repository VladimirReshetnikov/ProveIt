# Blank-seed first drain iteration

`PA194SeedToDrainReturn.blankToDrainReturn` composes the certified literal blank-start path to the first site-38 frame with the matching positive source-controller cycle 38→39→40→38. In every PRA model it reaches the actual physical site-38 frame at gap 43, with a corresponding three-step controller execution for an arbitrary controller tail. `PA194SeedSite38Guard` proves the initial logical register-7 value is 1 and the required repeated-spare suffix, so neither is assumed.

The intermediate physical clocks are existential. This is a finite initial execution and does not establish a primitive-recursive uniform clock, a model-length decoder iteration, a native iPRA sentence, or the consistency equivalence. Build order: `PA194SeedSite38Guard.lean`, `PA194SeedToDrainReturn.lean`.

Fresh staged replay passed with exit 0. Repeat with a fresh output directory:

```sh
python3 \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-seed-drain-return.py \
  "$PWD" \
  Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-controller \
  /dev/shm/pa194-one-spare-seed26-repo \
  /dev/shm/pa194-loop-to32-repo \
  /dev/shm/pa194-site31-restore-physical-exit-repo \
  /dev/shm/pa194-site35-restore-entry-repo \
  /dev/shm/pa194-fetch-coherent-full-v2 \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-seed-drain-return-repo \
  /dev/shm/pa194-seed-first-gap-repo \
  /dev/shm/pa194-site32-zero-clock-code-repo \
  /dev/shm/pa194-site32-zero-exact-repo \
  /dev/shm/pa194-site31-restore-physical-orbit-repo \
  /dev/shm/pa194-site31-fully-coded-repo \
  /dev/shm/pa194-site31-restore-iteration-repo \
  /dev/shm/pa194-site31-transfer-loop-repo \
  /dev/shm/pa194-site31-coded-loop-repo \
  /dev/shm/pa194-site31-coded-clock-repo \
  /dev/shm/pa194-site31-native-repo \
  /dev/shm/pa194-site32-clock-code-repo \
  /dev/shm/pa194-site32-positive-exact-repo \
  /dev/shm/pa194-site33-jump-repo \
  /dev/shm/pa194-site32-both-physical-repo \
  /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo \
  /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo \
  /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo \
  /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo \
  /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo \
  /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo \
  /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-site35-header-return-repo \
  /dev/shm/pa194-site35-increment-to7-repo \
  /dev/shm/pa194-site35-selected-repo \
  /dev/shm/pa194-site35-to2-repo \
  /dev/shm/pa194-site35-second-pass-repo \
  /dev/shm/pa194-site35-to14-repo \
  /dev/shm/pa194-site35-second-to95-repo \
  /dev/shm/pa194-site35-first-pass-general-repo \
  /dev/shm/pa194-site34-branch-repo \
  /dev/shm/pa194-site34-second-pass-repo \
  /dev/shm/pa194-site34-to14-repo \
  /dev/shm/pa194-site34-first-pass-general-repo \
  /dev/shm/pa194-site34-first-pass-repo \
  /dev/shm/pa194-site28-work/build-complete \
  /dev/shm/pa194-site28-work/build-finish-return \
  /dev/shm/pa194-site28-work/build-site29-selected-return \
  /dev/shm/pa194-site28-work/build-carry-seven \
  /dev/shm/pa194-site28-work/build-carry-codes \
  /dev/shm/pa194-site28-work/build-site29-to-increment \
  /dev/shm/pa194-site28-work/build-site29-return-to-root \
  /dev/shm/pa194-site28-work/build-site29-path30-identities \
  /dev/shm/pa194-site28-work/build-site29-complete \
  /dev/shm/pa194-site28-work/build-site30-jump \
  /dev/shm/pa194-termgraph \
  /dev/shm/pa194-site34-positive-physical-repo \
  /dev/shm/pa194-site35-source-physical-repo \
  /dev/shm/pa194-seed-first-site38-repo \
  /dev/shm/pa194-site38-drain-single-repo \
  /dev/shm/pa194-site38-drain-step-repo \
  /dev/shm/pa194-site40-physical-repo \
  /dev/shm/pa194-site39-physical-repo \
  /dev/shm/pa194-site38-positive-physical-repo \
  /dev/shm/pa194-site38-zero-physical-repo \
  /dev/shm/pa194-site38-positive-to16-repo \
  /dev/shm/pa194-site38-positive-return-repo \
  /dev/shm/pa194-site39-increment-to7-repo \
  /dev/shm/pa194-site39-second-pass-repo \
  /dev/shm/pa194-site39-first-pass-repo \
  /dev/shm/pa194-site38-to4-repo \
  /dev/shm/pa194-site38-to1-repo \
  /dev/shm/pa194-site38-second-pass-repo \
  /dev/shm/pa194-site38-second-to14-repo \
  /dev/shm/pa194-site38-second-to95-repo \
  /dev/shm/pa194-site38-second-to71-new \
  /dev/shm/pa194-site38-first-pass-repo \
  /dev/shm/pa194-site38-to30-repo \
  /dev/shm/pa194-site38-zero-to16-repo \
  /dev/shm/pa194-site38-zero-to14-repo \
  /dev/shm/pa194-site38-zero-to12-repo \
  /dev/shm/pa194-site38-zero-rollback-repo \
  /dev/shm/pa194-site38-branch-repo \
  /dev/shm/pa194-site36-zero-physical-repo \
  /dev/shm/pa194-site36-branch-repo \
  /dev/shm/pa194-site36-marked-entry-repo \
  /dev/shm/pa194-site36-second-pass-repo \
  /dev/shm/pa194-site36-second-to14-repo \
  /dev/shm/pa194-site36-first-pass-repo \
  /dev/shm/pa194-site36-gap-dispatch-repo \
  /dev/shm/pa194-site36-to42-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. The seed/controller, physical and foundation stages are prebuilt; their complete transitive closures are not independently authenticated by this incremental replay. In particular the seed-controller scratch overlay retains the caveat documented by `SEED-FIRST-GAP.md`.
