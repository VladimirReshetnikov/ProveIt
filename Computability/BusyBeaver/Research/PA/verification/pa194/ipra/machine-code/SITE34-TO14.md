# Site-34 second pass through state 14

`PA194Site34To14Exact.to14` proves in every PRA model that the literal PA194 machine advances from a site-34 frame with gap `k+2`, through its first root pass and into the second pass, reaching physical control state 14 at the theorem's exact PR arithmetic clock. The endpoint explicitly retains the remaining encoded file and arbitrary full suffix; its right tape is the unary block for the second physical register followed by the entire residual file. The model-valued state-93 and state-113 scans process the header and first physical register. An eight-row fixed prefix and three additional literal transitions are individually checked in Lean.

This is an intermediate physical configuration before the site-34 source-instruction branch decision. It does not establish that branch, the whole decoder, a native iPRA sentence, full simulation or a consistency implication.

A fresh staged source replay passed with exit 0, five axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site34-to14.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site34-first-pass-general-repo /dev/shm/pa194-site34-first-pass-repo /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-to14-repo
```

Use a fresh output directory. The checker rebuilds five modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires each named axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
