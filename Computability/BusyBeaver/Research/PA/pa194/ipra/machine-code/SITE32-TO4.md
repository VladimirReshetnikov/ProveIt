# Site-32 carry to the selected register

`PA194Site32CarryTo4.carryTo4` proves an all-model eight-slot carry ending at dense state 4 with the selected unary word and arbitrary full suffix. `PA194Site32CarryFileIdentity.carryFile` identifies the exact state-1 output from the preceding physical run with the eight-slot file needed by that carry. `PA194Site32To4.to4` composes them with the previous site-32 physical prefix, giving an exact clock and endpoint. The selected physical slot is slot 8, which corresponds to logical register 6.

The final zero/positive physical branches, their returned source frames, and source/physical synchronization remain open. This is an all-PRA-model result, not yet a native iPRA sentence.

A fresh incremental replay passed with exit 0, all required axiom audits, and no `sorryAx`:

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site32-to4.py "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code \
  /dev/shm/pa194-site32-to1-repo /dev/shm/pa194-site32-second-root-repo \
  /dev/shm/pa194-site32-return-header-repo /dev/shm/pa194-site32-first-pass-repo \
  /dev/shm/pa194-loop-to32-coherent /dev/shm/pa194-site31-matched-coherent \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2 /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-site32-to4-replay
```

Use a fresh output directory. The checker rebuilds the three modules, rejects conflicting direct machine-object overlaps and `sorryAx`, and records source, direct object/companion and upstream receipt hashes. Earlier physical and foundation stages remain prebuilt; this replay does not independently authenticate their full transitive object closures. The fetch machine-object root is excluded from Lean's search path.
