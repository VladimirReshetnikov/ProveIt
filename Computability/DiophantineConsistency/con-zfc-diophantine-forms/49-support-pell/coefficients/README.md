# Exact common package-31 coefficient tuple

This directory contains the complete fixed tuple `wang943-mixed-121x8801`
used by every new equation in this archive. The `MF_source` port is already
shifted by `beta`; never substitute the unshifted native mask.

- `COEFFICIENT_BINDING.json`: canonical dimensions, aliases, payload sizes and hashes.
- `payloads/`: all four actual unsigned little-endian integer payloads, gzip-compressed.
- `COEFFICIENT_PROOF.md`: inherited finite recipe and compiler-coefficient argument.
- `build_coefficients.py`: inherited coefficient generator.
- `upstream/`: literal 943-tile table, K215 transitions and source proof copies.
- `licenses/`: inherited third-party licenses and notices.

The current article appendix is `../sections/coefficients.tex`, included in
`../report.tex` and `../report.pdf`. The original package-31 README,
including its original repository-relative paths, is preserved as historical
provenance at `upstream/README_PACKAGE31.md`.

Run the independent reconstruction from the archive root:

```sh
python3 audits/verify_coefficients.py coefficients
```

It reconstructs all four exact integers from the recipe and tile table,
without importing the original builder, and checks both compressed and
raw payload hashes. This finite check does not replace the compiler proof.
