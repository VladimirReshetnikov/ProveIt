# Shift the fixed affine index: 94 operations

The affine-radix system in `AFFINE_RADIX_95_PROOF.md` has a
94-operation certificate after an exact change of its fixed index.
The resulting count is 51 multiplications and 43 additions, with
the same 34 positive unknowns and 22 equality tests. Fixed numerals
and equality tests are free.

## 1. The new index and the actual radix

Use the complete physical-coordinate construction, target layout,
and constants of `AFFINE_RADIX_95_PROOF.md`. In that construction,
the sufficiently large fixed power of two is H0, and the old supplied
index component is H_old=H0+1. Replace that component by

    H=H0-3=H_old-4.

Keep V and Tindex=psi_4(L) unchanged. Since H0>1024, the new
component H is a positive integer. It depends only on the represented
system, just as the old component did. The three supplied index
components remain (V,H,Tindex); the queried input is still x.

In the new source equations, the actual mathematical radix is

    B_math=H+b+4=H0+b+1.

Replace every occurrence of H_old in the old source system by H+4.
In particular, its radix equation becomes

    theta+4=(H+4)+b,

or, equivalently,

    theta=H+b.                              (1)

The geometric equation remains

    q^2-1=lambda*(B_math-1),

and the second exponent equation uses B_math. The numerical value
of the actual radix has not changed. Thus the single forbidden bit
is still H0, since

    B_math-1-b=H+3=H0.

Neither H nor b is required to be a power of two. The conditions on
the new admissible index are exactly that H+3 is the sufficiently
large power of two specified in the old construction, with the same
associated V and Tindex.

## 2. Exact equivalence and positive witnesses

Fix a represented set and its old admissible index
(V,H_old,Tindex). Let H=H_old-4. For every positive input x and every
tuple z of the 34 positive unknowns, the new source residuals obey
the polynomial identities

    F_new(x,V,H,Tindex,z)
      =F_old(x,V,H+4,Tindex,z).

These identities hold for every equation, before imposing any of
the other equations. Consequently the new and old systems have
exactly the same positive witness tuples at the corresponding
indices. The witness map is the identity on all 34 unknowns and on
x. The inverse parameter map is H_old=H+4.

The proof in `AFFINE_RADIX_95_PROOF.md` therefore applies without
any strengthening of its inequalities or coding arguments. In
particular, B_math, theta, q, both integer codes, the forbidden-bit
mask, every reset and unit test, and all Pell coordinates have the
same values. Necessity uses the same arbitrarily large power-of-two
radix B_math and b=B_math-H0-1; sufficiency uses the same first-mask
and Pell deductions. Every supplied witness remains positive.

This is a bijection between admissible indexed systems. It does not
assert the equivalence theorem for arbitrary positive H unrelated
to the prescribed fixed index.

## 3. The saved operation and the complete checker

In the old 95-operation schedule, the registers named `B` and `L3`
were computed as

    B=H_old+b,
    L3=theta+4,

and the free equality test was `L3=B`. Neither register was an
operand of any other arithmetic instruction. After shifting the
fixed component, retain the one addition

    theta_sum=H+b

and test `theta=theta_sum` directly. Delete `L3=theta+4`.

The retained addition is renamed `theta_sum` to distinguish its
value from the mathematical radix B_math. The mathematical radix is
theta_sum+4, but the certificate never needs to construct it.
The checker verifies that `theta_sum` is used only in this equality
test and has no downstream arithmetic use. The geometry already
uses theta*lambda+3*lambda+1, and the second exponent calculation
already uses a-theta=(a+4)-B_math on equation (1).

Every other primitive instruction is retained. This removes exactly
one addition and no multiplication:

    95=51 multiplications+44 additions
      ->94=51 multiplications+43 additions.

The standalone checker
`../verification/round33_1980_shifted_affine_certificate.py` verifies
the full parameter substitution, the absence of downstream uses of
the deleted register, all 94 primitive instructions, and all 22
source residuals. Its three residual corrections are the same
acyclic ones as before: geometry and the second exponent depend on
the exact radix equation, and the signed norm depends on the exact
relaxed auxiliary norm. The adjacent JSON receipt lists the complete
primitive schedule, equality tests, domains, and residual identities.

This proves an upper bound of 94 for the stated straight-line
certificate measure; no minimality claim is made.
