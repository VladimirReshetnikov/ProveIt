# First seed-derived site-36 gap

`PA194SeedFrameAlignment.seedFrame` identifies the previously checked blank-startup site-27 file with the model-loop frame and a `repeatOutput(27,0)` suffix. `PA194SeedToFirstRestore.blankToFirstRestore` composes that startup with the model-length site-27 exit, proving that the literal blank machine reaches the first site-31 restore frame and that the subsequent site-36 gap is at least 39. `PA194SeedValues.firstSite36Gap` proves the actual gap is exactly 42 and `firstSite34Guard` proves the positive site-34 register-8 guard is satisfied. All these are statements in every PRA model with clean axiom audits.

The exact gap calculation uses the existing restore and site-34/site-35 frame formulas. This increment does not yet compose a blank-to-site-36 physical run, prove a gap invariant for later decoder rounds, or establish the consistency equivalence.

Build order: `PA194SeedGapBound.lean`, `PA194SeedFrameAlignment.lean`, `PA194SeedToFirstRestore.lean`, `PA194SeedValues.lean`. The seed-controller stage `/dev/shm/pa194-site28-controller` is prebuilt and its direct imported objects are hashed; the earlier seed-controller replay is documented in `SEED-CONTROLLER-RETURN27.md`. The other listed physical and foundation roots are prebuilt. Direct-object pins and receipt hashes do not authenticate their full transitive closure.

Replay with a fresh output directory:

```sh
python3 \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-seed-first-gap.py \
  "$PWD" \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site28-controller \
  /dev/shm/pa194-one-spare-seed26-repo \
  /dev/shm/pa194-loop-to32-repo \
  /dev/shm/pa194-site31-restore-physical-exit-repo \
  /dev/shm/pa194-site35-restore-entry-repo \
  /dev/shm/pa194-fetch-coherent-full-v2 \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
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
  /dev/shm/pa194-site35-source-physical-repo
```

The checker rejects conflicting direct machine-object overlaps, changes to pinned inputs, missing axiom reports and `sorryAx`; the fetch machine-object root is excluded from Lean's search path.
