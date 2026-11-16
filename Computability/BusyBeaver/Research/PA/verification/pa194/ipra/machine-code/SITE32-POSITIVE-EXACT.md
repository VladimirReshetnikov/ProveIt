# Site-32 positive branch with an exact model clock

`PA194Site32PositivePathExact.positivePath` proves in every PRA model that the literal physical stepper runs from the site-32 frame with gap `(k+1)+1` to the site-33 frame with gap `((k+1)+1)+1`, using the named model-valued clock `PA194Site32PositiveTo24Exact.clock k args`. Under the sole branch premise `args 6 = m+1`, the complete file is updated at register 6 to `m`; all other registers and the full tape suffix are retained. The seven modules expose and compose exact return, scanning and header costs.

This is a single-branch all-model physical theorem. The clock has not yet been provided as a primitive-recursive `Code`, and this result alone does not establish a native iPRA sentence, iteration, global simulation or a consistency implication.

A fresh staged source replay passed with exit 0 and without `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-positive-exact.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
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
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-positive-exact-replay
```

Use a fresh output directory. The checker rebuilds the seven new source modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier machine and foundation stages remain prebuilt; this replay does not independently authenticate their full transitive closures. The fetch machine-object root is excluded from Lean's search path.
