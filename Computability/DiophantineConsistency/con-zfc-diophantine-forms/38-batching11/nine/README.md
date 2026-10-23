# Nine nonnegative or positive variables by quadratic batching

`generated/nine_natural.json` defines a polynomial in exactly nine
nonnegative integers, with exact degree 166,177,600 and 868 binary operations.
`generated/nine_positive.json` is its positive-coordinate translation,
with the same exact degree and 864 operations.

The complete new proof and all formulas are in the parent report's
Section 2, source `../sections/section_nine.tex`. Inherited source proofs
and the exact formal carry/ratio interfaces are retained in `inherited/`.
The independent local review is `INDEPENDENT_BOOTSTRAP_REVIEW.md`.

The parent has 22 quadratic residuals in 31 positive coordinates. The new
source shifts these to 31 natural coordinates, uses 528 distinct unordered
pair sums on 32 explicit positions, and tests 22 target coefficients at once.
This replaces quartic base-five packing. Its source constant is exactly
`kappa=2^1359525`, bound to the complete sibling compiler tuple.

Run with Python 3.10+ and no extra packages:

    python3 build_nine.py
    python3 bind_coefficients.py
    python3 verify_nine.py

All arithmetic operations are explicitly charged after powers are expanded.
The 917-operation `nine_degree_certificate.json` is an algebraically equal
circuit exposing the cancellations, not the production operation count.
Its exact degree/diagonal-leading certificate retains all 16 derived
fixed coefficients symbolically and yields `2^196*kappa^83088652`.

The literal `parent31.json` is byte-exact upstream source. Its historical
default-binding metadata is inactive. Current bindings are
`COEFFICIENT_BINDING.json` and `../compiler/COEFFICIENT_BINDING.json`, and
`source_data.json` contains every derived fixed-coefficient recipe.

The construction proves the equivalence to Con(ZFC) in ordinary mathematics
using the inherited native compiler/K215 calibration and parameterized
Jones ratio theorem. It is not a new end-to-end formal proof or a claim
about nine unrestricted integer variables.
