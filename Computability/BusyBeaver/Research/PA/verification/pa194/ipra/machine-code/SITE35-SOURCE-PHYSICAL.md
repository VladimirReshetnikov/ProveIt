# Matched site-35 increment to site 36

`PA194SourceSite35Physical.sourcePhysical` proves in every PRA model that the actual encoded controller and literal physical machine execute the site-35 increment to site 36. The input physical gap must be `((t+1)+1)+1`; the output gap is `t`. Logical register 7 is incremented, all other logical registers and the independent controller tail are unchanged, and the physical suffix changes from `repeatOutput(count,0)` to `repeatOutput(count+1,0)` for any model-valued count. The physical clock is an explicit nested sequence of model-valued times, with the exact output source-frame word identified.

The extra gap is met for the immediate continuation of the existing `PA194RestorePhysicalExit.completeExit` followed by the site-34 positive branch: restore exit has gap `((k'+1)+1)+1`, and that branch preserves it. This describes composition of checked statements; an explicit Lean theorem composing them is not included here. The source-35 result is not yet a single PR clock code or a native iPRA sentence; the complete decoder, global simulation and consistency equivalence remain separate.

Build order: `PA194Site35OutputFile.lean`, `PA194Site35Complete.lean`, `PA194SourceSite35Controller.lean`, `PA194SourceSite35Physical.lean`.

The fresh staged replay passed with exit 0. Replay with a fresh output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site35-source-physical.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code /dev/shm/pa194-site35-header-return-repo /dev/shm/pa194-site35-increment-to7-repo /dev/shm/pa194-site35-selected-repo /dev/shm/pa194-site35-to2-repo /dev/shm/pa194-site35-second-pass-repo /dev/shm/pa194-site35-to14-repo /dev/shm/pa194-site35-second-to95-repo /dev/shm/pa194-site35-first-pass-general-repo /dev/shm/pa194-site34-positive-physical-repo \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site35-source-physical-repo
```

The checker rejects conflicting direct machine-object overlaps and `sorryAx`, verifies named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages are prebuilt; their entire transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
