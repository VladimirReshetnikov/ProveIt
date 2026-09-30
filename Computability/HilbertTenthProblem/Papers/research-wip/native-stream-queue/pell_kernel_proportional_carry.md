# Exact proportional-carry reduction and elementary decidable cases

Consider the same transported equation as in the
[nonzero-determinant theorem](pell_kernel_nonabsorbing_determinant.md),
but now assume alpha*delta-beta*gamma=0:

    (alpha W+beta)A+(gamma W+delta)B
        +epsilon WL+zeta W+eta(x)=0.                 (1)

The radix R>=2 is fixed, W and L are powers of R, and W satisfies its
effective input lower bound. The append domain is either
`1<=A,B<=L-1` or `A,B>=1, A+B<=L-1`. This note gives an exact reduction
for the general proportional case and complete decision procedures for
three elementary subcases. It does **not** decide the general remaining
exponential divisibility problem and makes no universality claim.

## 1. Integer factorization and the exact remaining guards

There are effectively computable integers u,v,a,b such that

    gcd(u,v)=1,
    alpha W+beta=uG(W), gamma W+delta=vG(W),
    G(W)=aW+b.                                      (2)

If (alpha,gamma) is nonzero, take a=gcd(alpha,gamma)>0 and
(u,v)=(alpha/a,gamma/a). Proportionality and Bezout's identity imply
(beta,delta)=b(u,v) for an integer b. If the first vector is zero but
(beta,delta) is nonzero, take a=0,b=gcd(beta,delta)>0 and its primitive
vector. If both vectors vanish, use a=b=0,u=1,v=0.

Let Image(L,Z) be the fixed ordinary Presburger formula

    exists A,B: the chosen append domain and Z=uA+vB. (3)

Its coefficients are fixed integers, so ordinary integer-linear quantifier
elimination is effective. The image may have holes or one-sided bounds;
it must not be replaced by a bare divisibility assertion.

For a!=0 define the signed integer H=aZ+epsilon L+zeta. Then(1) is
equivalent to

    G(W)H=b*epsilon*L+b*zeta-a*eta(x),
    H-epsilon*L-zeta is divisible by a,
    Image(L,(H-epsilon*L-zeta)/a).                    (4)

Indeed, substitute the definition of H: the difference between the two
sides of the first equation is exactly a times the left side of(1).
As a is nonzero, this implication is reversible. The divisibility guard
recovers the integer Z, and Image supplies exactly the original positive
append values. H is a derived signed quantity in this reduction, not an
additional positive certificate coordinate.

At the possible width with G(W)=0, decide the original fixed-width
formula directly; there is at most one such positive width. Away from
that width, (4) necessarily includes

    aW+b divides b*epsilon*L+b*zeta-a*eta(x),          (5)

with W,L both radix powers. The congruence and image guards in(4) still
remain. For example, with G=W+1,u=v=1,epsilon=zeta=0,eta=-3,
W=L=2, divisibility in(5) holds and forces H=1. But the positive append
image has Z=A+B>=2, so there is no original witness.

## 2. Absorbing global coefficient: epsilon=0

In this case(1) is independent of L. Given positive A,B satisfying it,
choose any sufficiently large power L so that the separate or joint
append bound holds. Conversely every original witness gives such A,B.
Thus the projection is exactly

    exists a permitted power W and positive A,B:
      (alpha W+beta)A+(gamma W+delta)B+zeta W+eta(x)=0.

This is the one-parameter Presburger situation decided effectively in
[the earlier effectivity audit](input_bridge_presburger_effectivity.md).
It includes all coefficient degeneracies and either append domain. No
padding claim is made for a nonabsorbing endpoint: here the q coefficient
vanishes by hypothesis.

## 3. Constant common factor: a=0

The append coefficients c0=beta,c1=delta are constants. If epsilon=0
Section2 applies. Otherwise let

    C=|c0|+|c1|,
    L0=2(|zeta|+1), W0=2(C+|eta(x)|+1).             (6)

Every witness has W<W0 or L<L0. To see this, use A,B<L in(1):

    W(|epsilon|L-|zeta|)<=CL+|eta(x)|.

For L>=L0 the factor in parentheses is at least L/2, so
W<=2C+2|eta(x)|/L<W0. This proof also covers c0=c1=0.

Enumerate the finitely many powers W<W0. For each, the remaining
sentence in A,B,L is ordinary Presburger arithmetic; eliminate A,B and
test the resulting one-variable formula on powers L by the finite
preperiod/period procedure. For the complementary branch enumerate
powers L<L0 and the finite append domain. The equation is then linear
in W; test its unique candidate power, reject an inconsistent constant
equation, or accept when it is identically zero and a permitted power
width exists. This is a complete effective decision procedure.

## 4. Zero constant term of the common factor: b=0

If a=0, Section3 already applies. Otherwise (1) factors as

    W[a(uA+vB)+epsilon L+zeta]+eta(x)=0.             (7)

When eta(x)!=0, W divides that fixed nonzero integer. There are only
finitely many positive power widths to inspect. Each fixed-width case
is decided by the same ordinary Presburger elimination and one-power
algorithm as above.

When eta(x)=0, divide by positive W. The remaining equation and either
append domain are ordinary Presburger conditions in A,B,L independent
of W. Eliminate A,B, test powers L, and choose an arbitrarily large
power W satisfying its input lower bound. Thus the zero-intercept case
is decidable even when the endpoint coefficient epsilon is nonzero.

## 5. Scope of the unresolved case

After these procedures, the general proportional case has a,b,epsilon
all nonzero, together with the exact congruence and image guards(4).
No bound on its variable modulus, no general decision algorithm, and
no universal realization is proved here. Additional special cases can
be simpler; this note does not call every instance of(5) unresolved.

For context, an accepted nonabsorbing carry cannot simply be padded by
zero labels while retaining its endpoint. In radix R, the zero-label
recurrence is `R*k_next=k+h`. After ell>0 zero labels, equality of the
initial and final endpoint cf would imply

    (R^ell-1)*((R-1)cf-h)=0.

Hence such padding is possible only at the absorbing endpoint
`(R-1)cf=h`. This is a direct recurrence identity, not a restriction on
other possible nonzero padding words.

The [checker](pell_kernel_proportional_carry.py) audits integer
factorization, equivalence(4) with every image guard retained, the
constant-factor bound, zero-intercept divisibility, and the exact
zero-padding identity. It does not implement general Presburger
elimination or solve the remaining two-power divisibility relation.
Default execution checks the [receipt](pell_kernel_proportional_carry.json).
Independent full proof/source/default review passed, including all
degenerate factors, the exact image and congruence guards, and each
elementary decision procedure. The complete universal bound remains76.
