# Independent review of the three denominator variants

Reviewed separately from the denominator proposal and its producing script,
25 October 2026.

The mathematical denominator lemma is valid relative to the explicitly
retained parent Pell/native proof. The product-square extraction depends on
the denominator only through positivity of M=hDH. The transport argument
needs D>2. Clearing the integral carrier supplies D dividing hHe; since q^4
divides D and q is coprime to hH, q^4 divides e. The unchanged first Pell
congruence and 1<=n0<R<q^4 force 2n0=R+1. At that stage the full modulus
4XY^2 divides e, and D divides 4XY^2, so e/D is integral. This order avoids
any unjustified coprimality assumption about D and hH.

For positive completeness the parent supplies e as a positive multiple of
4XY^2, so e/D>=1. Its other positive-witness arguments, including g>kappa,
are unchanged. The proposed new padding coordinate is therefore a positive
integer. The first Pell norm is exactly unchanged when the two products
Y^2 followed by X times Y^2 are replaced by X times Y followed by that
product times Y.

The standalone `verify.py` was written without importing the producing
`build.py`. It authenticates all 38 original compact-parent files, checks
all allowed source changes, and checks 28, 28, and 29 exact polynomial cuts
covering every register in the three circuits. It independently propagates
the complete leading homogeneous form, with 1,950, 141, and 141 nonzero
terms respectively. The displayed nonzero coefficients are

```text
 16384 beta^378,      -1024 beta^284,      -1024 beta^284.
```

The authentic beta is positive, as verified by independently reconstructing
the complete tuple from the retained finite code and comparing exact bytes.
Therefore the degrees are exactly 626, 464, and 460. Every independent input,
fixed port, and intermediate register is live. The exact binary-operation
counts are 78, 79, and 80. The completed receipt is `VERIFICATION.json`.

This review verifies the new mathematical delta and finite objects. It does
not independently reprove every theorem in the retained native/refutation
calibration and does not claim global minimality or historical priority.
