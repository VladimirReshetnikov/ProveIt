# Five exact arithmetic-circuit contractions

All five child circuits are **identical polynomials** to their complete frozen parents from ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`. The witness domains, all actual coefficients, exact degrees and full zero sets are unchanged. No new source-calibration claim or global optimum is asserted.

| Strictly positive variables | Parent operations | New operations | Exact degree |
|---:|---:|---:|---:|
| 10 | 99 | 98 | 368 |
| 10 | 105 | 103 | 340 |
| 11 | 111 | 107 | 211 |
| 12 | 96 | 95 | 70 |
| 13 | 88 | 87 | 51 |

The incoming Bootstrap package already contains a 110-operation evaluator
for the eleven-variable degree-211 polynomial. The new 107-operation circuit
saves three operations relative to that incoming point and four relative
to its exact pinned 111-operation parent.

`REPORT_SECTION.tex` provides a self-contained mathematical account ready to include in a larger LaTeX report. `circuits/` contains all new explicit polynomial circuits. Their only fixed leaves are the four fully supplied integers in `coefficients/payloads/`; use `int.from_bytes(gzip.decompress(bytes), "little")`. `coefficients/BINDING.json` fixes each payload and its bit length. `MF` is already shifted and must not be shifted again. The complete coefficient recipe and original transition data are also supplied.

`parents/` contains the complete unchanged parent circuits. `SOURCE_PINS.json` records exact repository paths, commit, and hashes. `inherited_proofs/` contains the ordinary mathematical dependencies used for interpretation; their historical relative links refer to the pinned repository. Native/compiler calibration and full internal-ZFC formalization are inherited matters, not proved anew by circuit checking.

## Verify without network access or third-party packages

```sh
python3 -B check.py
python3 -B -O check.py
```

The independent checker imports no generator. It compares every coefficient of small exact free-polynomial cuts, then certifies complete output equality by structural induction through each graph. It also checks topology, liveness, counts, source/payload hashes and corrupted-output rejection. Exact degree is transported from the parent through identity; raw syntax bounds are listed separately.

To regenerate the five child circuits from their frozen parent snapshots:

```sh
python3 -B fold_transport.py
python3 -B fold_additional.py
python3 -B check.py
```

These builders require only the Python standard library. Their modular controls supplement the exact independent proof; they are not used as proof of identity.
