# Two prime-separated equations in twelve integers

The two circuits in `equations/` are exact ordinary polynomials using
the fixed source-34 six-tuple in
`inherited/root_fusion/coefficients/BINDING.json`.

| Polynomial | Variables | Exact degree | Live operations |
| --- | ---: | ---: | ---: |
| prime_separated12_degree2400 | 12 integers | 2400 | 215 |
| prime_separated12_degree2912 | 12 integers | 2912 | 209 |

Read `proofs/PRIME_TWELVE.md` and the root article for the new proof.
The parent interpolation proof, independent audit, and full root-fusion
dependency tree are included. `baselines/` contains the pinned old
degree-4832/248-operation and degree-16000/223-operation circuits for
comparison only; their historical relative metadata is unchanged.

Every JSON node is one of:
- `["variable", name]`
- `["coefficient", port]`
- `["integer", literal]`
- `["add"|"sub"|"mul", earlier_index, earlier_index]`

The output index names the final polynomial; all nodes are live.
Register names provide explanatory abbreviations, not extra variables.
The coefficient files are gzip-compressed unsigned little-endian integer
payloads, with compressed/raw hashes and bit counts in the binding.
The actual coefficient constants are not counted as variable inputs.

Regenerate from this directory:

```sh
python3 build_prime12.py --variant rational --output equations/prime_separated12_degree2400.json
python3 build_prime12.py --variant integral --output equations/prime_separated12_degree2912.json
python3 check_prime12.py --source-root inherited/root_fusion --receipt /tmp/prime12-check.json
python3 check_norm_exact.py --receipt /tmp/norm-check.json
```

The optional carrier31 switch is retained as a comparison generator; only
the default classical carrier19 endpoints above are claimed and audited.
Operation counts include scalar multiplications and squarings; common
registers and fixed numeral leaves are free. Bit complexity and coefficient
description length are separate metrics.

The proof uses the ordinary calibrated native source. It does not prove
that the polynomial has no solution, nor provide a new complete
proof-assistant derivation inside the encoded ZFC syntax.

