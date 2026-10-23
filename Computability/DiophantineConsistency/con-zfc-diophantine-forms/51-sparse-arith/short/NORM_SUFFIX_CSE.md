# Three exact arithmetic savings in the reduced-weight finalizer

These changes leave the polynomial identical at every assignment; they do
not require squarehood, positivity, or any compiler theorem.

## 1. Reuse the common square scale

The reduced radical weights are 1,b,bK.  The squared radicands are

    a0 = Sigma^2 r0,
    a1 = Sigma^2 b^2 r1,
    a2 = Sigma^2 (bK)^2 r2.

Both b^2 and K^2 are already evaluated in the source.  Put

    M = Sigma^2 b^2;
    a1 = M r1;
    a2 = (M K^2) r2.

The identity `Sigma^2 (bK)^2 = (Sigma^2 b^2)K^2` permits deletion of the
otherwise private product bK and its square.  This saves two multiplications.
The conceptual weight bK need not be materialized as a circuit node.

## 2. Factor the common four in the norm suffix

For arbitrary x,a0,a1,a2, put

    x2=x*x,
    v=x2+a2-a0-a1,
    v2=v*v,
    xa=x2*a2,
    ab=a0*a1,
    w=v2+4*(xa-ab),
    F=w*w-16*v2*xa.

This is identically the previous three-radical norm expression

    w_old=v2+4*x2*a2-4*a0*a1,
    F_old=w_old*w_old-4*v2*(4*x2*a2).

Both equal the product of the eight signed linear radical factors.
The new suffix uses fourteen binary operations:

1. x2=x*x
2. v0=x2+a2
3. v1=v0-a0
4. v=v1-a1
5. v2=v*v
6. xa=x2*a2
7. ab=a0*a1
8. difference=xa-ab
9. four_difference=4*difference
10. w=v2+four_difference
11. w2=w*w
12. product=v2*xa
13. scaled_product=16*product
14. F=w2-scaled_product

The previous suffix used fifteen operations.  Multiplication by a fixed
small numeral is charged in both counts.  The saved operation comes from
the two occurrences of the coefficient four in w, not from treating a
fixed coefficient multiplication as free.

Together these exact refactorings reduce the current reduced-weight
ten-integer circuit by three operations, with no degree change.  They make
no global optimality assertion.

## 3. The nine-positive-variable two-radical suffix

The nine-variable construction has the two-radical norm

    inner = Theta^2 - Omega^2*(a0+V0^2*a1),
    output = inner^2 - 4*Omega^4*V0^2*a0*a1.

Set

    b0=Omega^2*a0;
    b1=Omega^2*(V0^2*a1);
    inner=Theta^2-b0-b1;
    output=inner^2-4*b0*b1.

Distributivity and `b0*b1=Omega^4*V0^2*a0*a1` prove the all-value identity.
The inner expression costs one additional subtraction/multiplication gate
overall, but the last term costs three fewer gates by reusing the scaled
radicands.  The net saving is two binary operations.

The same construction uses Omega=u*m and

    Theta=u*(n+Mdiv)+v-2*Omega*Mdiv-Omega*V0*V1.

Factoring u gives the identical expression

    Theta=u*(n+Mdiv-m*(2*Mdiv+V0*V1))+v.

The old Theta cone uses nine binary operations and the factored cone eight,
after u,m,n,Mdiv,v,V0,V1 are available.  The intermediate E0 is no longer
needed by the ordinary evaluator and is pruned.  Omega itself is retained
because the final norm still uses it.  This adds one further operation
saving without changing the polynomial or its degree.
