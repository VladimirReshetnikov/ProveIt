# Inverse Lucas correction with a squared transport coordinate

Two complete polynomials in ten strictly positive integer variables, with
85 binary arithmetic operations and exact degree 232. The principal variant
uses L=(cT-R)^2 and lowers the carrier numerator degree from 57 to 21.
It combines the trace reduction in ProveIt package 163 with the inverse
correction in package 164 and resolves package 163's explicit b² transport
question. No global minimum or worldwide novelty is claimed.

**Late comparison:** a newly inspected incoming archive already contains
the identical bV polynomial at 85 operations and degree 232. That companion
is a reproduced baseline. The distinct contribution here is L=b², lowering
the carrier numerator degree from 57 to 21 without changing the total
degree or operation count. See `LATE_COMPARISON.json` for exact identities
and the bounded comparison scope at commit
`0d75e561a8cefc8c30fc4224605a8984c810ad1c`.

Read `PROOF.md` for the full formula, the new unbounded argument and the
precise inherited logical boundary. The ordinary proof establishes that
positive unsolvability is equivalent, in ZFC, to Con(ZFC), composed with
the named native/refutation calibration. No new transitive proof-assistant
closure is supplied.

The final graph files are in `equations/`. All paths inside their metadata
are relative to this component directory. The exact four fixed coefficients
are in `coefficients/`, stored as gzip-compressed little-endian integers.
Their complete finite recipe is in `inherited/coefficient_recipe.tex`.

To reproduce and check with Python 3 and the standard library:

```sh
python3 -B build.py --check
python3 -B verify.py
```

`build.py` without `--check` deterministically regenerates the equations and
coefficient payloads. Tests authenticate the finite artifacts and do not
replace the mathematical proofs. The largest fixed integer has 592884 bits.

`radix47/` additionally contains two separately calibrated specializations
using the whole complemented-label tuple. Their largest fixed port has
415,904 bits, with 207,214 raw bytes across all four constants. The complete
changed native carry/controller proof and its exact bridge are retained;
the arithmetic circuit remains 85 operations at degree 232. Read that
component's proof and run its separate builder/verifier. The coefficient
improvement is credited prior work, composed here with the new forms.

Compared with the trace parent: 85 rather than 87 operations at degree 232.
Compared with the inverse parent: degree 232 rather than 304 at 85 operations.
The squared weight does not lower the total degree below 232; it reduces a
specific carrier's degree and simplifies the signed soundness proof.

All new material follows the included ProveIt MIT No Attribution license.
See `NOTICE.md` for retained sources and the scope of AI-assisted checking.
