# Site-32 second root

`PA194Site32SecondReturn.to24` gives the literal physical return from the header-side control 17 to root control 24 for an arbitrary model-valued word, with its exact clock. `PA194Site32SecondRoot.secondRoot` composes that return with the previously staged two passes, six-slot selected-register scan and rewind, and header-side return. The resulting encoded tape word and clock are explicit, and all file arguments and the complete physical suffix remain arbitrary in every PRA model.

This is a physical prefix through the second root. It does not yet include the final register-6 decision, either source-frame branch endpoint, or a complete physical/source simulation.

A fresh incremental replay is run from the repository root with a new output directory:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-second-root.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-return-header-repo /dev/shm/pa194-site32-first-pass-repo \
  /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-second-root-replay
```

The checker rebuilds two source files, checks direct machine-object overlaps, records source hashes, available Lean object companions and upstream receipts before and after, and rejects `sorryAx`. It consumes the prior return-header, first-pass, loop, matched, tail, carry, physical baseline and foundation stages as prebuilt; those checks do not independently authenticate their full transitive closures. It excludes the fetch machine-object root from Lean's search path.
