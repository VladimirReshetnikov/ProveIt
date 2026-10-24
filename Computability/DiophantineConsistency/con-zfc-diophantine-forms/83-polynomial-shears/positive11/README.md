# Eleven positive unknowns, degree 211, 112 operations

This component gives an explicit ordinary integer polynomial with eleven
strictly positive unknowns. Its exact degree is 211 and its literal
division-free circuit uses 112 live binary arithmetic operations. The
incoming centered predecessor has degree 257 and 114 operations.

The new reduction translates the auxiliary coordinate by `F+alpha`.
An early Pell-growth estimate makes the auxiliary radical positive before
transport positivity is established. Two polynomial root centers and a degree-two gap majorant then replace
the predecessor's larger exceptional-sign weight.

Read `PROOF.md` for the complete construction, unbounded mathematical proof,
explicit completeness lift, and inherited semantic boundary. `section.tex`
is the article-ready version. The literal polynomial is
`p11_positive_degree211.json`; its intermediate registers are polynomial
abbreviations, not extra quantified variables. Its two-residual system has
109 operations.

Run from any working directory:

```sh
python3 path/to/positive11/verify.py
python3 -O path/to/positive11/verify.py
python3 path/to/positive11/rebuild_coefficients.py
```

Only Python's standard library is required. `build.py` regenerates the exact
JSON circuit. `audit.py` does not import the builder: it checks every named
polynomial contract, the conjugate norm and rational-extraction identities,
the exact double-center cancellation, the exact leading coefficient, liveness, and
all operation counts. Explicit checks remain active under `-O`.

All four coherent compact44 coefficients are included as compressed
little-endian integers, with the finite coefficient generator and literal
transition input. Their total raw payload is 295,388 bytes. The MF port is
already shifted. Do not substitute ports from another binding.

The conclusion is an ordinary zero-existence equivalence composed with the
inherited native/compiler and syntactic-ZFC calibration. No assumption or
proof of consistency, global minimum, new nine-variable bound, historical
priority, or new end-to-end proof-assistant certificate is claimed.

## Sources and provenance

`PROVENANCE.json` records the reviewed repository head and the exact incoming
centered predecessor. `SOURCE_PINS.json` retains the earlier inherited source
pins. `upstream/` contains the mathematical interfaces and their original
notices; the immutable coefficient recipe is under `native_recipe/`.

The current finite verification receipts are `ALGEBRA_AUDIT.json`,
`VERIFICATION.json`, `VERIFICATION_OPTIMIZED.json`, and
`COEFFICIENT_REBUILD.json`. These checks establish finite algebra and data;
they are not substitutes for the unbounded proof.

