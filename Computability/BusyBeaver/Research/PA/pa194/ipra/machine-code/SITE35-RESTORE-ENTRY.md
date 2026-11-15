# Restore output feeds the site-35 positive entry

`PA194Site35RestoreEntry.restoreFeedsSite35` kernel-proves in every PRA model that if the site-34 register 8 in the existing restore output equals `m+1`, the actual restore physical run followed by the actual site-34 positive physical branch reaches site 35. The resulting physical gap is `((k'+1)+1)+1`, and its suffix is `repeatOutput(succ(n'),0)`, exactly meeting the gap and suffix premises of the matched site-35 increment theorem. All variables and the suffix count are model-valued; the register guard remains explicit. The theorem does not assert that a blank-tape run reaches the restore input or that the remaining decoder and global simulation are proved.

Source: `PA194Site35RestoreEntry.lean`. The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site35-restore-entry.py \
  "$PWD" \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site31-restore-physical-exit-repo \
  /dev/shm/pa194-site35-source-physical-repo \
  /dev/shm/pa194-site34-positive-physical-repo \
  /dev/shm/pa194-fetch-coherent-full-v2 \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  /dev/shm/pa194-site35-restore-entry-repo \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
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
  /dev/shm/pa194-site34-first-pass-repo
```

This incremental checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies the named axiom audit, and records source, direct object/companion and three upstream receipt hashes. It uses the listed prebuilt physical and foundation stages; it does not authenticate their complete transitive closures. The fetch machine-object root is excluded from Lean's search path.
