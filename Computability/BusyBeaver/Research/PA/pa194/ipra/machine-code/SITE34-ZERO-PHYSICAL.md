# Matched site-34 zero branch to site 42

`PA194SourceSite34ZeroPhysical.zeroBranch` proves in every PRA model that when logical register 8 is zero, the actual encoded source controller takes its site-34→42 zero branch and the literal PA194 physical stepper reaches the actual site-42 source frame at the theorem's exact model-valued clock. Both source and physical frames retain the entire file and arbitrary suffix, the independent controller tail is preserved, and the gap is unchanged at `k+2`. The resolved site-34 instruction and the six-bit prefix used in the final physical return are kernel checked; the path-42 identifier is separately kernel checked. The intermediate return passes use the full residual file rather than a blank-tail assumption.

This establishes the complete zero source/physical branch. The positive 34→35 branch, a PR code for the whole zero clock, native iPRA transfer, the complete decoder, global simulation and the consistency equivalence remain separate.

A fresh staged source replay passed with exit 0, the named axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site34-zero-physical.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-zero-physical-repo
```

Use a fresh output directory. The checker rebuilds eleven modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the named axiom audits, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
