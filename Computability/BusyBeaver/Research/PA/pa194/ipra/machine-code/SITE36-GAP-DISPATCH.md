# Site-36 zero and positive gap dispatch

`PA194Site36GapDispatch.zeroGap` and `.positiveGap` prove in every PRA model that the literal site-36 frame reaches state 60 at gap zero and state 59 at gap `g+1`, respectively, after exactly 12 transitions. Both endpoints retain the exact full file/suffix word. The remaining gap is `g` in the positive case. The finite transitions are kernel checked. This distinguishes the gap cases and does not establish either source-level branch of site 36.

Source: `PA194Site36GapDispatch.lean`. The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site36-gap-dispatch.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site36-to42-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site36-gap-dispatch-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their entire transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
