# Twelve-positive companion

Main equation: `p12_desaturated_product.json`, degree629, 114 live binary operations.
Three-equation system: degree622, 109 operations; shifted transport system: 108.
`P12_PROOF.md` and `section.tex` contain the mathematical argument.

Run from any working directory using the absolute path, or from this directory:

```sh
python3 build_p12.py
python3 check_p12.py
```

The builder and checker use only Python's standard library. All checker gates
raise explicit exceptions and remain active under `-O`/`-OO`. The checker uses
exact carry-free integer packing for modular polynomial multiplication; its
documented coefficient bound prevents carries between packed coefficients.
It also compares this implementation with a naive convolution on 24
deterministic fixtures. Normal and `-O` runs produce identical results, as
recorded in `CHECKER_PORTABILITY_RECEIPT.json`.
Both scripts resolve all paths relative to their own files.
Its proof boundary and inherited attribution are stated in `NOTICE.md`.
The authoritative coefficient binding is `../coefficients/COEFFICIENT_BINDING.json`.
The exact old proof and polynomial are included under `upstream/`, with
commit and content hashes in `SOURCE_PINS.json`.
