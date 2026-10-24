# Projected direct proof-certificate quartics, round 13

Final selected literal equations:

- `projected/`: 1,859 nonnegative variables, 1,581 quadratic residuals,
  12,275 monomials, coefficient height 63,924,066.
- `projected_integer/`: 3,179 unrestricted integer variables, 2,074 quadratic
  residuals, 23,157 monomials, coefficient height 63,923,766.
- `forward/`: sparse alternative with 2,560 nonnegative variables,
  2,217 residuals, 11,074 monomials, coefficient height 63,923,744.

All have exact degree four, and coefficient height below 2^26. Their no-zero
statements are equivalent in ordinary ZFC mathematics to Con(ZFC), using the
explicit pinned numerical C222-to-ZF and constructible-choice calibration.
This does not prove absence of zeros or provide a new end-to-end Lean
certificate. No global variable-count or simplicity record is asserted.

Each term `[coefficient,[indices]]` is a literal integer coefficient times
the indexed variables; repeated indices mean repeated factors and indices
start at zero. equation.json lists quadratic residuals. The single polynomial
is their sum of squares. expanded_polynomial.json gives its fully collected
ordinary polynomial. No variable exponent, unexpanded arithmetic macro,
coefficient port, or bounded search remains in these files.

## What is inherited and what is composed here

The incoming eight-column projection parameterizes each rule's labels and
pads a proof with truth steps so its horizon N bounds all four schema
parameters. The incoming sign-orbit method supplies U/Z sign normalization.
Both methods are explicitly credited and pinned, not claimed as new here.

This construction composes them with:

1. A sharp bounded-factor carrier M=(m+1)^N.
2. A polynomial label bound m=(N+4)^(2^22), computed with 22 squarings.
3. A shared CRT radius H=(4+N+x+y+M0)^(2^23), computed with 23 squarings.
4. Eight local columns bounded by (N,N,N,N,y-1,y-1,x,x). Canonical beta
   quotients are automatically at most x, so no private bound U remains.
5. Forty parametric positive-power graphs, eleven binomials, two factorials.
6. In the integer version, 161 unrestricted congruence quotients, 80 verified
   U/Z sign actions, and only 414 three-triangular-number sign certificates.

The selected 3,179-variable equation improves the late 3,671-variable
incoming alternative on variables, monomials and height. The incoming
3,776-variable equation still has fewer monomials and much smaller
coefficients; the new equation does not dominate every current variant.
The sparse natural companion likewise retains its genuine term-count
advantage. Full comparisons and the complete equivalence argument are in
section.tex; projected_section.tex separately records the final delta.
The eleven-column 2,170-natural/4,087-integer construction described in the
proof is a reconstructible intermediate, not the final selected result.

## Clean offline rebuild

Python 3.12+ and its standard library suffice. From this directory:

    python build_projected.py --output /tmp/round13-natural
    python build_projected.py --integer-template --output /tmp/round13-mixed
    python build_integer.py --source /tmp/round13-mixed --output /tmp/round13-guarded --free-quotients
    python build_sign_normalized.py --source /tmp/round13-mixed --prior-integer /tmp/round13-guarded --output /tmp/round13-integer
    python build_forward.py --output /tmp/round13-sparse

For byte-exact verification of every selected output in a fresh portable
copy, in both normal and optimized Python:

    python verify_rebuild.py --output /tmp/round13-replay.json

The mixed template is not a standalone natural-domain equation. Its 161
quotients are unrestricted integers. The completed unrestricted-integer
polynomial is the output after sign guarding and normalization. The guarded
intermediate is retained for the exact normalization/sign certificate.

No builder imports or executes anything from sources/, a remote URL, or
an upstream repository. All executable modules in the release are locally
authored implementations. The finite source dependencies in sources/ are
inert text, with source pins and inherited licenses.

## Exact evidence

The selected directories include raw quadratic circuits, all macro bindings,
full affine restoration maps, exact sparse coefficient files, projection and
radius certificates, and complete sign-normalization/closure certificates.
The enclosing release includes independent algebra and semantic audits.
CLEAN_REBUILD.json records exact reconstruction, not a consistency test.
SOURCE_PINS.json records source roles and hashes. RELEASE_WHITELIST.json
names the portable payload; RELEASE_SHA256.json binds its exact bytes.
