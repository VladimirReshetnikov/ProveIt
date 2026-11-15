# Site-32 selected-register scan and header return

`PA194Site32TwoPassesTo71.twoPassesTo71` composes the existing first pass with a second marked path dispatch and model-length scans through the first two physical file slots. `PA194Site32To17.site32To17` extends this through an existing six-slot scan and rewind. The selected physical slot is slot 8, which the pinned register permutation identifies as logical register 6. Its full right suffix, all other register values, exact endpoint, and total model-valued clock remain explicit. `PA194Site32ReturnToHeader.returnToHeader` then returns the result to dense state 17 at the source-header side, preserving the encoded file, arbitrary suffix and explicit clock.

These are physical-run theorems in every PRA model. They do not yet prove either full site-32 source branch or a source/physical simulation. The earlier first-pass stage includes kernel-checked source-controller zero and positive branches.

The following fresh incremental replay passed with exit 0, no `sorryAx`, and explicit final axiom audits:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site32-return-header.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-return-header-replay
```

Choose a fresh output directory. The checker rebuilds five machine-specific source files, checks direct machine-object overlaps, records source and direct prebuilt object/companion hashes and upstream receipts before and after, and excludes the fetch machine-object root from Lean's search path. It consumes the first-pass, loop, matched, tail, carry, baseline and general foundation stages as prebuilt; those hash checks do not independently authenticate the full transitive closure of these stages.
