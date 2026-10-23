# Smaller Diophantine forms of ZFC consistency

Prepared 22 October 2026 for ProveIt. Comparison snapshot:
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`.

## New results

The recommended equation has **12 strictly positive unknowns, exact degree
1081, and 116 binary arithmetic operations**. Its absence of positive integer
solutions is provably equivalent in ZFC to Con(ZFC), by the new ordinary
mathematical proof composed with the identified inherited native compiler
and K215 calibration.

The new complete coefficient tuple has **B = 2^(5^9)**. Its four actual
integer payloads total **977,220 raw bytes**, versus 5,312,269 bytes in the
previous best materialized Wang943 tuple. All four coefficients are included.

| Form | Positive unknowns | Equations | Degree | Operations |
|---|---:|---:|---:|---:|
| Recommended hybrid product | 12 | 1 | 1081 | 116 |
| Recommended hybrid system | 12 | 3 | 1072 | 111 |
| Hybrid sum of squares | 12 | 1 | 2144 | 119 |
| Simpler outer-proof product | 12 | 1 | 1081 | 117 |
| Inherited P67, new coefficients | 15 | 1 | 155 | 67 |
| Inherited retained system, new coefficients | 16 | 7 | 24 | 59 |

The hybrid improves package 20's degree-1145, 123-operation product and package
21's degree-1353, 116-operation product. The 111-operation system count uses a
direct comparison of final norm terms. The same rewrite makes package 21's
published 112-operation system use 111 operations: this is a degree improvement
at a tied normalized cost, not an exclusive new system-operation record.

The nine-natural-variable Jones specialization remains better on variable
count. No global minimum, proof of consistency, or new Lean/Rocq endpoint
is claimed. Positive-domain formulas must not be read over unrestricted Z.

## Start here

- `report.pdf` and `report.tex`: the complete report and LaTeX source.
- `arithmetic/hybrid12_square_unweighted_product.json`: recommended equation.
- `arithmetic/hybrid12_square_unweighted_system.json`: recommended system.
- `coefficients/COEFFICIENT_BINDING.json`: the one complete fixed instance.
- `proofs/HYBRID12_PROOF.md`, `proofs/COEFFICIENT_PROOF.md`: expanded proofs.
- `proofs/INDEPENDENT_*_AUDIT.md`: separate mathematical reviews.
- `provenance/SOURCES.json`: pinned inherited files and hashes.

## Reproduce without the source repository

Python 3.10 or later and its standard library suffice:

```sh
python3 reproduce.py
```

This regenerates all nine circuit variants and all coefficient payloads,
runs the independent verifiers, and checks the actual fixed-instance
residues. It makes no network calls. Receipts are in `verification/`.

To compile the report, with a LaTeX installation containing the listed
standard packages:

```sh
make pdf
```

The archive includes the compiled PDF, so LaTeX is not required to read it.

## Exact coefficient contract

The canonical instance is `wang943-mixed125-external-padding-5pow9`.
Payloads in `coefficients/coefficients/*.bin.gz` decompress to minimal
unsigned little-endian integers. No header is present in those raw bytes.
Use `int.from_bytes(gzip.decompress(path.read_bytes()), 'little')` to load.

| Circuit port | Payload |
|---|---|
| beta or Bm1 | beta |
| K0 or Kconstant | K |
| MC | MC |
| MF | MF_source |

`MF_source = MF_native + B - 1`. Replace all four ports together.
Historical source files under `upstream/` keep their original instance
descriptions and serve as evidence; the delivered circuits select the new
tuple through their explicit binding metadata.

## Verification boundary

The mathematical proof handles unbounded witnesses. Finite programs check
algebra, exact support identities, materialized bytes, degree certificates,
and arithmetic accounting. They do not decide Con(ZFC), evaluate an actual
refutation witness, or replace the inherited semantic compiler proofs.

The new source can be placed in a new directory such as `24-hybrid12/` under
the existing collection. All runtime paths are relative to this package,
so placement does not require editing scripts or retrieving omitted files.
The `upstream/` evidence files may describe their historical layouts; none
is executed or imported by the reproduction driver.
