# Site-34 physical decoder first root pass

`PA194Site34FirstPass.firstPass` proves in every PRA model that the literal PA194 machine starts at the site-34 source frame with a model-valued gap `k+4`, executes an exact explicit clock, and returns to the site-34 root with the precise unary-header/tape expression stated in the theorem. The complete 11-slot register file and suffix are arbitrary; no blank-tail or zero-register premise is imposed. Intermediate theorems identify the state-15, state-16 and state-17 configurations and use a model-length zero/one scan. The first 13 literal transitions and final 23 root-return transitions are individually proved in Lean; exploratory Python merely suggested their finite row sequences and is not part of the trusted proof.

This is the first physical header pass of the site-34 decoder. It does not yet prove either branch of site 34, the whole decoder, its native iPRA transfer, full physical/source simulation, or a consistency implication.

A fresh staged source replay passed with exit 0, the six final axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site34-first-pass.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-both-physical-repo /dev/shm/pa194-site32-positive-to12-repo \
  /dev/shm/pa194-site32-positive-return-repo /dev/shm/pa194-site32-zero-physical-repo \
  /dev/shm/pa194-site32-zero-to14-repo /dev/shm/pa194-site32-zero-boundary-repo \
  /dev/shm/pa194-site32-zero-file-repo /dev/shm/pa194-site32-branch-repo \
  /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site34-first-pass-repo
```

Use a fresh output directory. The checker rebuilds six modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires each named axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; their full transitive closures are not independently authenticated by this incremental replay. The fetch machine-object root is excluded from Lean's search path.
