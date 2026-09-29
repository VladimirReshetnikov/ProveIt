# Full false-input witnesses for the direct interleaving shortcut

The natural positive separated-field interleaving proposal has a complete
**74=41M+33A** schedule, 33 positive coordinates and 21 equations. It is
**unsound**: for every admissible fixed compiler, it accepts every positive
ordinary input. Its collapsed **75=42M+33A** variant is unsound as well,
with 31 positive coordinates and 19 equations.

This is a full positive-witness construction for these newly specified
sources, including the unchanged 43-operation Pell kernel and the ordinary
input bridge. It is not merely a carry example. Neither source is one of
the previously open 75-operation candidates, and neither refutes those
candidates or the established complete76 theorem.

## 1. The tempting complete sources

Take any fixed positive compiler constants from the established76 native
layout. Write B=2^d for its cell base, b for its odd inner bit width,
and MC,MF for its even masks. They satisfy

    d>=3, 0<MC,MF<B-1,
    popcount(MC)+popcount(MF)=d, b odd.

Enlarge each proposed computation cell to Q=B^2 and put

    m=MC+B*MF, K0=DC+Q*DR.

Thus m is even, lies strictly between zero and Q-1, and occupies exactly
half of each 2d-bit cell. All these are fixed program numerals, independent
of the varying ordinary input x.

Attach the eight outer instructions of the
[one-field module](one_field_half_mask.md), using its fixed base Q and
its field V:

    q=n^2, D0=n^3,
    (Q-1)J=q-1,
    r=(q-V)(q-1)+m*J.                                    (1)

Attach the unchanged ten equations of the 43-operation base-two kernel at
scale D0. In particular the recovered/canonical main quantities are

    X=2^(2r+1), a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3.

The proposed outer compiler then supplies positive P,v,C,Z,F,W,z,alpha
and imposes

    P*v=q,
    C=Z+W,
    V=Z+B*F,
    (K0+P)*C=F+z*(q-1),
    C+alpha+4d*x=q.                                     (2)

Finally retain the four original input bridge equations with the fixed
scaling numeral changed to 4d. Writing u=4d*x+b, they are

    kappa=u+delta*Delta,
    c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H.                                 (3)

The intended endpoint is W=2^u=2^b*Q^(2x). This preserves ordinary x;
there is no input-dependent compiler numeral.

The intended reading of V is that Z occupies the lower B-sized halves of
Q-cells and F occupies the upper halves after multiplication by B. But
`V=Z+B*F` does not impose that separation on its positive summands. The
single mask on V cannot simply replace their two separate typing masks.

The exact ledger is:

| Part | M | A | Total |
|---|---:|---:|---:|
| One-field outer source and unchanged kernel |30|21|51|
| Independent stride product, C+alpha, marker, combined field, transport |4|5|9|
| Ordinary-input bridge, including strengthened raw bound |7|7|14|
| **False complete source** |**41**|**33**|**74**|

The middle block is nine literal instructions:

    C+alpha; P*v; Z+W; B*F; Z+B*F;
    K0+P; (K0+P)*C; z*(q-1); F+z*(q-1).

The existing registers q-1, D0, Delta and H are reused. No comparison is
charged and no variable multiplication by a numeral is omitted.

Eliminating positive Z and F gives the weaker collapsed transport

    L*C=V+W+B*z*(q-1), L=1+B*(K0+P).                    (4)

Its direct schedule costs eight instructions for (4), one for C+alpha,
one for P*v, and the same 51+14 module/bridge operations: total75.
The factor B multiplying the wrap quotient is retained. The witnesses
below even restore positive Z and F, so their failure is not explained
by a missing positivity condition in this elimination.

## 2. A Boolean residue lemma

Let L>1 be odd, and choose any L-1 distinct nonnegative bit positions
j_1,...,j_(L-1). Their Boolean subset sums cover every residue modulo L:

    {sum epsilon_i*2^(j_i) modulo L : epsilon_i in {0,1}}
       = Z/LZ.                                         (5)

Indeed every weight is a unit modulo L. If S is a proper nonempty subset
of Z/LZ and w is a unit, then S+w cannot equal S: invariance under w would
make S invariant under the whole cyclic group. Thus `S union (S+w)` has
at least one more member than S. Start from S={0} and apply this argument
L-1 times. It is a finite constructive argument; a predecessor table also
recovers a selected Boolean subset.

Unlike a false assumption about sums of arbitrary digit words, (5) uses
distinct bit positions exactly once. Consequently every selected sum has
no carries and remains within the specified bit mask.

## 3. Construct all positive outer coordinates at an arbitrary raw input

Fix any positive x and keep all compiler numerals fixed. Fix h=1 and set

    P=Q, K=K0+P, L=1+B*K,
    u=4d*x+b, W=2^u.

Here L is a fixed odd integer greater than B+1, and K>Q. Choose N large
enough that all the following requirements hold, and put

    n=B^N, q=Q^N, J=(q-1)/(Q-1), M=m*J.

The requirements are N>1, dN>=L+1, u<q, and the two explicit inequalities

    B*(q-1)>L*W,
    (L-B-1)*q+B+1-W > L*(4d*x).                         (6)

They hold for every sufficiently large N, since all constants on their
right are fixed after choosing x, and L-B-1>0. One may even restrict N to
arbitrarily large powers of five; the argument does not need that restriction.

The mask M has dN allowed bit positions. Since m is even, the units bit
in every Q-cell is allowed. Reserve the two distinct allowed positions
zero and 2d(N-1), and write

    Vfixed=1+Q^(N-1)=1+q/Q.

There remain at least L-1 allowed positions. By (5), select a Boolean
subset of them, with sum T, such that

    T = -W-B*(q-1)-Vfixed modulo L.

Set

    V=Vfixed+T,
    C=(V+W+B*(q-1))/L,
    z=1, v=q/P, alpha=q-C-4d*x.                          (7)

The two reserved bits are disjoint from the subset, so

    0<V<q, V AND M=0, V odd, V>=q/Q.                     (8)

The selected congruence makes C an integer. The first inequality in (6)
gives C>W. Since V<=q-1, the second gives C<q-4d*x and therefore alpha>0.
Also v>0, P*v=q, z>0, and (4) holds exactly.

Restore the separated coordinates by

    Z=C-W,
    F=(V+W-C)/B.                                        (9)

The first is positive. For the second, (4) and L=1 modulo B give
`C=V+W modulo B`, so F is an integer. Further,

    L*(V+W-C)=B*[K*(V+W)-(q-1)]>0,

because K>Q and V>=q/Q. Thus F>0. Since C>W and V<q, also F<q/B.
Equations (7)--(9) now imply every equation in (2), including

    K*C=F+(q-1), C=Z+W, V=Z+B*F.

So all separately supplied outer coordinates are positive, even with
F<q/B, Z<C<q and the strengthened raw-input bound. No negative formal
field or zero quotient is being used.

## 4. Fresh complete kernel and ordinary-input witnesses

Define the actual packed index r from (1). The inverse-packing identity
applied to (8) gives

    q<=r<q^2, popcount(r)=3dN.

Moreover q is even, M is even and V is odd, so r is odd. In terms of the
old kernel scale parameter n, these are exactly

    n^2<=r<n^4, r odd,
    n^3 divides binom(2r,r).

Thus the established complete76 positive kernel converse applies directly
with its old scale parameter replaced by n. It supplies all seventeen
kernel coordinates freshly at this actual packed r and at D0=n^3. In
particular X=2^(2r+1), c=psi_A(2r+1), and a>q^3. This appeal needs only
the established positive kernel converse; it does not assume that any
new one-field computation compiler is sound.

The even-mask variation of the one-field module is therefore harmless
here: its necessary parity is explicitly met by V odd. We are using a
mask-valid point with the correct central-binomial valuation, not a
weakened Pell kernel or a wrong-index example.

The index u is odd, at least three, and satisfies u<q<2r+1. Set

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta,
    phi=c-kappa,
    rho=(mu-a*kappa-W)/H.

The odd-index discriminant congruence makes delta integral, and the
standard base-two congruence makes rho integral. Strict growth gives
phi>0 and delta>0. Also

    mu-a*kappa=2*kappa-psi_A(u-1)>kappa>=2A>W,

so rho>0. These coordinates satisfy all four equations (3), with the
original ordinary raw input x and the fixed scaling numeral 4d. Every
one of the 33 supplied coordinates of the74 source is now positive;
removing Z,F leaves every coordinate of the75 collapse positive as well.

## 5. Scope of the refutation and executable evidence

The construction works for **every** fixed choice of the admitted compiler
constants and **every** positive x. In particular, choose the fixed native
compiler for the empty recursively enumerable set. The proposed source
then has positive witnesses at x=1 although that machine rejects every
input. This is a full false-input theorem for the new74 source and its
75 collapse. It does not promote a toy mask to a universal compiler:
the argument applies to the actual compiler numerals without enumerating
their enormous bit positions.

The failure is the claimed arithmetic separation of the two tracks.
Explicit positivity, a whole-cell temporal divisor, the correct endpoint
power, a correct main Pell index, and the original input gap all survive.
Any repair must add a proved separation or typing property, or change the
encoding beyond these equations. This is not a lower bound for every
one-field compiler, and the retained main power could participate in a
different source which this construction does not cover.

The [checker](interleaved_compiler_collapse_refutation.py) independently
expands all21 residuals of the74 schedule and all19 of the75 schedule,
including the auxiliary-norm corrections. It verifies3,069 residue targets
and materializes nine complete outer tuples with positive Z and F, across
three illustrative half-mask layouts and raw inputs1,2,3. Each tuple has
the exact required packed population and all hypotheses for the complete
positive Pell extension; their untyped C is also checked directly.

The [receipt](interleaved_compiler_collapse_refutation.json) is compared by
default. The finite layouts are examples of the algebraic construction,
not actual huge universal compiler layouts. The proof supplies actual
compiler witnesses parametrically, along with the enormous final Pell
coordinates; those full integers are not materialized. Author and independent complete proof/source reviews pass; fresh default
receipt replay matches. The established complete
universal bound remains76.
