# Site-32 physical run to dense state 1

`PA194Site32RootWord.secondRootWord` identifies the exact second-root word with the actual site-32 path applied to twice the retained word. `PA194Site32RootTo1.rootTo1` uses this path together with the prior state-42 positive-run theorem to reach dense state 1. `PA194Site32To1.to1` composes this third dispatch with the previously checked two passes, selected-register scan, and exact second-root return. Its clock, full endpoint word, arbitrary physical file and suffix are explicit in every PRA model.

This is an all-model physical prefix, not yet the site-32 zero or positive source branch, a native iPRA sentence, or a complete simulation. In particular the carry to the selected register, the branch test, and the final source-frame return remain separate.

The following fresh incremental replay passed with exit 0 and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site32-to1.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-second-root-repo /dev/shm/pa194-site32-return-header-repo \
  /dev/shm/pa194-site32-first-pass-repo /dev/shm/pa194-loop-to32-coherent \
  /dev/shm/pa194-site31-matched-coherent /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-to1-replay
```

Use a fresh output directory. The checker rebuilds the three named modules, rejects mismatched direct machine-object overlaps and `sorryAx`, checks the final axiom audit, and records source, direct object/companion and upstream receipt hashes. Earlier physical and general foundation stages remain prebuilt; this incremental check does not independently authenticate their full transitive object closures. The fetch machine-object root is excluded from Lean's search path.
