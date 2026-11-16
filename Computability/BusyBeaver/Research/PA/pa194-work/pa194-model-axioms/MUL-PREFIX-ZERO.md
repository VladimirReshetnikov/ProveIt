# Zero-input multiplication-prefix existence

`mulPrefixExists` says that some zero and graph satisfy the actual source `mulPrefix` relation. `zeroPrefixWitness` constructs such a prefix for any zero input and any base from equality, empty-set and adjunction proofs, using the existing point graph. It is a typed Foundation source derivation with explicit premises, not full multiplication totality: successor extension, ordinal induction, source-theory discharge and native iPRA transfer remain open.

Run from the repository root with a fresh output directory:

```bash
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-mul-prefix-zero.sh "$PWD" /dev/shm/pa194-mul-prefix-zero-repo
```

The single-source replay rejects `sorryAx` and checks two axiom reports. It retains previously built dependency objects, including `/dev/shm/pa194-forward-mul-zero-repo` and Foundation overlays; it does not rebuild their source closures.
