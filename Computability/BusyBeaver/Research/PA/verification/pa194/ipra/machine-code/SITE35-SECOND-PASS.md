# Site-35 second root pass

`PA194Site35SecondPass.secondPass` proves in every PRA model that the literal site-35 frame with gap `k+2` completes the second physical root pass, returning to the actual site-35 path with the exact named right-tape output. All model-valued register entries and the entire numeric suffix are arbitrary. The clock is explicit and model-valued; the final 25-step return has each row checked by Lean. This is before the site-35 increment, and does not claim native iPRA, complete decoder, global simulation or consistency equivalence.

Build order: `PA194Site35MarkerReturnNext.lean`, `PA194Site35SixteenSixRuns.lean`, `PA194Site35SecondTo17.lean`, `PA194Site35SecondReturn.lean`, `PA194Site35SecondPass.lean`. The first two are minimal-import adaptations of existing checked return lemmas, avoiding reliance on unrelated prebuilt machine roots.

The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site35-second-pass.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site35-second-pass-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their entire transitive closures are not authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
