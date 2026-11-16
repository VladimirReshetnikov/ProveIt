# Site-32 positive decision and eight-slot return

`PA194Site32PositiveEight.returnEight` generalizes the previously verified six-slot return to eight carried slots. `PA194Site32PositiveReturnCell.returnPositive` combines the dense state-4 positive decision with that return, giving an explicit subclock and retaining an arbitrary tail. `PA194Site32PositiveFile.returnedFile` separately identifies the returned file word with the complete source file after decrementing logical register 6.

These are all-PRA-model pieces of the site-32 positive path. Their connection to the full site-32 input, the site-33 header and the encoded source-controller step is not yet proved in this increment.

The following fresh incremental replay passed with exit 0, required axiom audits and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-site32-positive-return.py "$PWD" Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-branch-repo /dev/shm/pa194-site32-to4-repo /dev/shm/pa194-site32-to1-repo \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-positive-return-replay
```

Use a fresh output directory. The checker rebuilds three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, requires the final axiom audits, and records source, direct object/companion and upstream receipt hashes. The earlier machine and foundation stages remain prebuilt; their full transitive closures are not independently authenticated in this replay. The fetch machine-object root is excluded from Lean's search path.
