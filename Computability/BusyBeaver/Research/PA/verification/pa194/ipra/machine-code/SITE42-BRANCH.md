# Site-42 physical decision point

`PA194Site42Branch.at4` proves in every PRA model that the literal site-42 frame with gap `(k+1)+1` reaches the physical control-4 decision point for logical register 7. `zeroTo5` and `positiveTo6` check the immediate zero and successor transitions. The entire arbitrary remaining file and numeric suffix are retained, and the preceding physical clocks are explicit.

These are decision-point transitions, not complete source branches or native iPRA transfer. Build order: `PA194Site42ThirdPrefix.lean`, `PA194Site42To1.lean`, `PA194Site42MarkedFile.lean`, `PA194Site42CarryFrom1.lean`, `PA194Site42To4.lean`, `PA194Site42Branch.lean`.

Fresh staged replay passed with exit 0 using my second-pass stage. The following invocation substitutes the repository-rebuilt stage; use a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site42-branch.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-site42-second-pass-repo /dev/shm/pa194-site38-to30-repo /dev/shm/pa194-site35-source-physical-repo /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site42-branch-repo \
  /dev/shm/pa194-site38-to4-repo \
  /dev/shm/pa194-site42-first-pass-repo \
  /dev/shm/pa194-site38-second-to14-repo \
  /dev/shm/pa194-site34-zero-physical-repo \
  /dev/shm/pa194-site38-positive-to16-repo \
  /dev/shm/pa194-site38-positive-return-repo \
  /dev/shm/pa194-site38-zero-physical-repo \
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
