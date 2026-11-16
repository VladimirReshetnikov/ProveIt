# Generalized site-34 physical first root pass

`PA194Site34FirstPassGeneral.firstPass` proves in every PRA model the exact first physical header pass from a site-34 frame with model-valued gap `k+2` back to the site-34 root. The precise resulting unary-header/tape expression and PR arithmetic clock are in the theorem; the full register file and arbitrary suffix are retained. This strengthens the previously replayed `k+4` version and covers an input gap of three, which can arise at the restore exit. The 13 initial literal transitions are rechecked using only two known zero cells; the 23-step return comes from the previous checked stage.

This establishes the first pass only. The second pass and source-instruction branches, native iPRA transfer, full simulation and consistency equivalence remain separate.

A fresh staged source replay passed with exit 0, five axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site34-first-pass-general.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-first-pass-general-repo
```

Use a fresh output directory. The checker rebuilds five modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires each named axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
