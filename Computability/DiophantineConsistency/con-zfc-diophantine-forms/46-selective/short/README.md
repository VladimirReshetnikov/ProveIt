# A complete 74-operation local polynomial

`p74_norm_minima.json` is an ordinary integer-coefficient polynomial in fifteen strictly positive unknowns. It has 74 live binary operations and exact total degree 68. Its complete positive zero set is the same as the inherited P75 (and hence P67) baseline. The new argument is uniform for fixed integer ports with beta positive; it does not use the native compiler theorem to establish this local equivalence.

The fixed coefficients for this delivered instance are the **entire package-36 tuple**, pinned to ProveIt commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`, not the different package-31 tuple used by the main ten-/nine-variable equations. The native base is `2^1012115`. The ports have these bit lengths:

| Circuit port | Payload port | Bits |
|---|---|---:|
| beta | beta | 1,012,115 |
| K0 | K | 1,016,946 |
| MC | MC | 1,012,115 |
| MF | MF_source | 1,012,116 |

The copied binding is `coefficients/COEFFICIENT_BINDING.json`. Its own relative payload paths are preserved under `coefficients/coefficients/`; this nested directory is intentional. MF_source is already shifted by the native `B-1`. Do not mix coefficient components between tuples.

`RESULT.md` contains the proof. `UPSTREAM_SHORT_SYSTEM.md` contains the exact inherited factor definitions, and `upstream_p75.json` is the unedited source circuit. `SOURCES.json` pins all inherited local files to their original Git blob hashes and records SHA256, sizes, and coefficient payload hashes.

Run:

```
python3 verify_p74.py
python3 -O verify_p74.py
```

The verifier checks the coherent actual payloads, positive beta, shifted mask convention, all gates and inputs, and a nonzero degree-68 coefficient for the real supplied tuple. Its mathematical formula is `2^8*beta^40` on the all-variable diagonal. `p74_audit.json` records the result. These are finite exact checks plus the local proof; the compiler-to-ZFC semantics remain inherited ordinary mathematical results and are not newly kernel-certified here.
