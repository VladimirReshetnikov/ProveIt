# Marking and decrement for the compressed register oracle

`PA194CompressedBoxFiles` proves marking and both decrement outcomes at any
physical register position, over arbitrary model register values and packed
suffixes. `PA194CompressedBoxOracle.boxAgreement` combines them, with an
explicit increment contract and decrement branch condition.

```sh
base=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code
python3 "$base/check-compressed-box-oracle.py" "$PWD" "$base" \
  /dev/shm/pa194-compressed-box-oracle-repo "$base/compressed-box-oracle-stages.txt"
```

The replay hashes selected direct inputs and audits the two new sources.
Further dependencies remain staged.
