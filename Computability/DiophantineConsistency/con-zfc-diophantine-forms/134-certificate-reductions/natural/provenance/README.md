# Bounded natural-engine provenance

`../SOURCE_PINS.json` binds exactly the 97 files in `../ENGINE_MAP.json` to
ProveIt commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`. It records the
original repository path and Git blob, original SHA-256, intermediate input
SHA-256, final local SHA-256, and every intervening line edit. The source paths
were resolved using the pinned `PLACEMENT.md` ledger and the package 129 source
ledger, then authenticated against the pinned Git tree.

Of the 97 inputs, 95 are exact upstream bytes. Two are new mathematical edits:

- `build_modular_factorial.py` implements the descending factorial floor with
  `F=F0+2`, the shared top `F^2-1`, and its exact power.
- `build_derived_label_range.py` changes the reciprocal-index equation to
  `C+1=T+B*iq`, matching the descending moduli.

Three files have further export edits. Two only shorten directory references.
The factorial builder also relabels two descriptive metadata fields, so its
`ENGINE_MAP.path_relocated` flag must not be read as a path-only claim. Both
edit stages are completely recorded in `SOURCE_PINS.json`. Reversing them
recovers the intermediate input and the pinned original bytes.

The two retained parent summary files authenticate the comparison endpoints:
parent natural233 has 182 rows, 50,762 terms and height 88,674,690; parent
natural234 has 183 rows, 9,019 terms and height 87,741,134. These are parent
figures, not the new equation's metrics. `anchor129.md`, `consecutive129.md`,
and `cap129.md` retain the ordinary inherited interface arguments used by this
branch, with their exact source paths in the ledger. Their historical relative
links refer to the original packages and are not a claim that all those
packages are copied here.

The immediate Lean calibration sources are among the 97 engine files. Their
named interfaces are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. This inventory does not
rebuild their full import graph and is not a new formal ZFC derivation.

From the release root, verify the retained bytes and both edit stages with:

```sh
python3 -B natural/provenance/check_pins.py
```

With a ProveIt Git checkout containing the pinned commit, also authenticate
every repository-path/blob binding:

```sh
python3 -B natural/provenance/check_pins.py --repo /path/to/ProveIt
```

The historical ZIP identity quoted in the ledger is inherited from the pinned
parent ledger; that ZIP was not downloaded again in this audit. Every used
original file was independently matched to the pinned Git tree. New top-level
release programs and mathematical outputs are authored artifacts and are
outside this bounded inherited-source inventory.
