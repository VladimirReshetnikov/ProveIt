# The retained Pell kernel for a fixed radix Boolean mask

This bounded audit changes no published certificate. The reference kernel
has 43 operations: 25 multiplications and 18 additions/subtractions. It is
not a universal system on its own. The surrounding finite-history
construction still has to supply its stated bounds, parity, input, and
halting conditions. All fixed integer numerals are free.

## 1. Exact interface and a confirmed outer saving

The kernel is instructions 34 through 77 of the round37 schedule, with
instruction 51 (the second-Pell positive gap) removed. Its input `n2` is
already computed by the outer schedule. It does not read `n` anywhere.
The retained quantities are

    U=w*n2, Y=s*n2, E=U*Y, a=E+Y,
    A=a+2, D=A^2-1=a^2+(4a+3), M=4a+3,
    Pfirst=2UY^2+1, J=2r+1.

The first norm and interval use

    tau(tau+1)=(E^2+U)(Yk)^2,
    c=Yk+eta, k=eta+zeta, k=r+1+hE.

The remaining equations are the main norm and exponent congruence,
the relaxed auxiliary norm, and the half-parameter index block:

    d^2=Dc^2+1, d=U+ac+gamma*M,
    R=ic^2, K=R^2=D(f^2-1),
    u=J+jc=c+of, K(u^2-y^2)=1-y^2.

In `EXPLORATION_PERIODIC_DIGIT_MASK.md`, put Q=q^2, Lbig=Q^8 and
n2=Q^12. The following five multiplications suffice:

    Q=q*q, Q2=Q*Q, Q4=Q2*Q2,
    Lbig=Q4*Q4, n2=Lbig*Q4.

There is no need to construct N0=Q^6 and then square it. N0 remains
mathematical proof notation, not a free power operation or supplied
integer. Relative to that explicit six-product chain, this saves one
multiplication. It confirms the 11-operation outer schedule in the
periodic-mask note, so those two conditional components cost 54
operations together. This excludes every other history operation and
does not establish a universal bound of 54.

The preliminary bound 0<=Pcode<Q^6, together with

    3lambda+1=Lbig,
    r=(Lbig-Pcode)(Lbig-1)+2lambda,

gives N0^2<r<Q^16<N0^3 and N0>=64 before any digit or power-of-two
decoding. Thus the published first-Pell hypotheses hold with this
mathematically defined N0. Since U=wQ^12, the recovered U=2^(2r+1)
forces q to be a power of two, just as an explicitly materialized N0
would. Canonical positive necessity additionally requires Pcode even,
which the proposed row-edge condition must supply.

## 2. The positive main-root shift costs one more operation

Consider replacing the supplied d by

    z=d-ac.

This is a valid positive change of variables: the old main norm has
D>a^2, hence d>ac. Conversely d=z+ac is positive whenever the new
variables are positive. The two affected equations become exactly

    z=U+gamma*M,
    z(z+2ac)=M*c^2+1.                           (1)

The discriminant D is still needed in the relaxed auxiliary equation;
its two instructions a^2 and a^2+M cannot be removed.

Excluding the shared construction of M,D and c^2, the old exponent
equation uses four operations: ac, U+ac, gamma*M, and their final sum.
The old main norm uses three: D*c^2, addition of one, and d^2.
The combined cost is seven operations.

The new exponent equation uses two: gamma*M and addition of U.
The new main norm uses six: ac, 2ac, z+2ac, its product with z,
M*c^2, and addition of one. The combined cost is eight. Equivalently,
including c^2, the comparison is eight versus nine. The complete
retained kernel therefore grows from 43 to 44 operations.

This is an exact positive-witness equivalence and an unsuccessful cost
optimization, not a rejection on mathematical grounds. The accompanying
script checks both polynomial identities and the full transformed
register count. Removing the second exponent block does not alter this
obstacle: D remains live through the first auxiliary norm.

## 3. Two other local changes have no saving

The half-parameter norm already takes five operations once K and u are
available: u^2, y^2, their difference, multiplication by K, and 1-y^2.
Replacing y by u+z, with z>0, gives

    (K-1)z(2u+z)=u^2-1.

This takes seven operations: K-1, 2u, its sum with z, two products,
u^2, and subtraction of one. The four congruence operations for u are
unchanged. Its complete kernel count is 45.

The congruence operations also merely move when one uses

    of=J+j_new*c, u=c+of

instead of u=J+j*c=c+of. On canonical solutions j_new=j-1 is positive
because u is much larger than c+J; this restricted replacement is not
needed for the count observation. Either displayed construction uses
the same two multiplications and two additions. It does not remove an
operation merely by moving the supplied quotient's offset.

These explicit counts do not establish local or global optimality. No
reduction of the retained 43-operation kernel was proved in this bounded
audit. The confirmed change is the single multiplication removed from
the surrounding power chain.

## 4. Exact verification and scope

`../verification/explore_fixed_radix_pell_kernel.py` imports the actual
published register list, checks the 43-operation slice and its D-only
outer interface, verifies the outer monomial powers, and checks the
main-root transformation by exact symbolic expansion. It constructs
the full 44-operation shifted register list and checks the affected
equality residuals, including the positive-root substitution. The
unchanged predicates retain their published source proofs.

This is an interface and arithmetic audit. It does not supply missing
history boundaries, positive encodings of zero planes, or a complete
universal finite-history predicate.
