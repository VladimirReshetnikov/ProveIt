# Bidirectional model-length scans

`PA194BidirectionalRunScan.fullScan` proves that a certified self-loop of
the literal dense PA194 table traverses a bit run whose length is an
arbitrary element of a PRA model. The packed tape halves may also be
arbitrary model elements. The scanned half loses the entire run and the
opposite half gains a run of the row's written bit. Both movement
directions and all read/write bit combinations use the same open
induction argument. `partialScan` gives the same exact accounting at any
intermediate clock at most the run length.

The compressed runtime can use this theorem for its affine run segments.
The proof still needs separate register-file contracts to cover a complete
source instruction.

Run from the repository root with a fresh output.

```sh
python3 Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-bidirectional-run-scan.py \
  "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-bidirectional-run-scan-repo \
  /dev/shm/pa194-bidirectional-generic-repo \
  /dev/shm/pa194-symbolic-zipper-repo \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-fetch-coherent-full-v2/foundation-view \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker records the selected direct imported objects and source hash
and checks their contents are unchanged after compilation. The older scan,
physical machine and Foundation objects remain staged. This replay does
not authenticate the full transitive dependency closure.
