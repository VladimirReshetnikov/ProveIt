# Raw/default-affine613 integer quartic

This separate complete endpoint has **613 unrestricted integer variables,
375 quadratic residuals, degree4,9661 expanded monomials and coefficient
height2445790974704**. It saves352 monomials compared with the accepted
compact613/10013 point, at the same dimension, degree, row count and
height. It is unrelated to the bootstrap-guard exchange and keeps the
original78 guards unchanged.

The literal polynomial is `expanded_polynomial.json`; `equation.json`
gives the equivalent sum of squares of all375 explicit quadratic rows.
No external coefficient or unspecified parameter occurs in either file.
`elimination_certificate.json` restores all880 deleted coordinates as
integer polynomials. The exact1493 source, its78-guard certificate and its
901/904 bridge data are copied under `source/`; they match the frozen
parent byte for byte. All613 unknowns occur in the full polynomial.

| Quantity | Accepted compact cap32 | New raw/default-affine cap8 |
|---|---:|---:|
| Integer variables | 613 | 613 |
| Quadratic residuals | 375 | 375 |
| Exact degree | 4 | 4 |
| Expanded monomials | 10013 | 9661 |
| Maximum absolute quartic coefficient | 2445790974704 | 2445790974704 |
| Largest residual support | 89 | 86 |

The new producer uses the **exact unchanged** frozen
`candidates/retained-radius-comparison-base/guarded.json` with
`max_support=8`, `affine_support=None`, `quadratic_first=False`. No variable
metadata, labels or ordering is changed. This differs from the previous
raw low-height variants with affine caps1/2 and from optimizing after
contracting to901. The entire input SHA256 is
`c30bee5671a654988f4ffa1eb5e5b43469b000292f4e78a85f5c062c0239494e`.

The source proof is inherited in the correct order: restore every signed
coordinate and guard into the literal1493 parent; apply its exact901
integer bijection; only then apply the accepted nonpointwise comparison
lift into904 and its pointwise extension into967. The original q4 is not
assumed positive. See `PROOF.md` for the complete unbounded equivalence
and the limits of the result. This is an ordinary arithmetic endpoint,
not a new Lean/internal-ZFC theorem or a global minimality claim.

The archive and the sole imported optimizer member are authenticated in
`SOURCE_PINS.json`. The independent checker imports no optimizer, source
builder or emitter. It checks every monic inverse and complete substituted
row, expands every residual square, compares the entire9661-term
polynomial, and verifies the actual raw/domain/901/904 bridge identities
through pinned frozen identity functions. It rejects six semantic
corruptions. All generated files and dependencies are pinned; the final
manifest is closed.

Run from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_retained_radius_default_affine.py --check
python -B -O Computability/DiophantineConsistency/tools/build_retained_radius_default_affine.py --check
python -B Computability/DiophantineConsistency/candidates/retained-radius-default-affine/check.py
python -B -O Computability/DiophantineConsistency/candidates/retained-radius-default-affine/check.py
```

The generator without `--check` writes only this new sibling. Accepted
parents, canonical pages, common documents and Lean files are unchanged.
