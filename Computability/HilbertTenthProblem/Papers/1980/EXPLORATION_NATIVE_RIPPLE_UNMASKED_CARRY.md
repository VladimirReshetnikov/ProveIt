# A refuted 62-operation ripple with an unmasked termination signal

This note records an exact arithmetic saving that is mathematically
unsound. It concerns the variant masking the four fields FC,FA,FB,FD.
The omitted field is FE, the carry-termination signal. The distinct
valid 62-operation construction in `EXPLORATION_UNIT_TWO_TERNARY_RIPPLE.md`
retains FE instead of FD and is not refuted here.

## 1. The complete candidate

For positive parameters q,FA,FB and positive auxiliaries H,FD,FC,alpha,
retain the 17 positive Pell witnesses of the base-three kernel. Replace
the finite outer equations by

    q=2H+1,
    FC+q=3FD+2,
    FA+FC+H=FB+2FD,
    FA+FC+alpha=q+H.                                  (1)

Construct

    P0=FC+qFA+q^2FB+q^3FD,
    D0=q^4, r=P0.                                     (2)

Use the same ten base-three Pell equations, with U=wD0,Y=sD0.
The equation r=P0 is a free comparison. Computing D0 requires just
q2=q*q and D0=q2*q2; no multiplication by three or offset is retained.

The intended decoded relations, after subtracting H from the fields,
would be C=3D+1 and A+C=B+2D, equivalently B=A+D+1. They fail to
make D the initial run of carry bits. A later isolated D bit can
create a spontaneous increment after the original carry has stopped.
The original Boolean test on E=2D+1 was essential for excluding this.

## 2. Exact count, including the bound

Compute q=H+H+1 in two additions. For the local equation compute

    twice_D=FD+FD, local_base=FA+FC,
    local_lhs=local_base+H, local_rhs=FB+twice_D.

These are four additions. The seed uses

    seed_lhs=FC+q, three_D=twice_D+FD, seed_rhs=three_D+2,

three more additions, reusing twice_D. The bound computes
bound=local_base+alpha and bound_rhs=q+H, two additions. The
four-field Horner packing costs three multiplications and three
additions. The two powers cost two multiplications. The unchanged
43-operation kernel costs 25 multiplications and 18 additions.

Thus the full candidate has

    2+4+3+2+6+2+43=62 operations,
    30 multiplications+32 additions/subtractions,
    15 equality tests,
    3 positive parameters and21 positive unknowns.

The bound is exactly the last equation of (1), imposed on the computed
two-field local_base. Bounding the full three-term local left side by
q+H would reject every intended native transition with C>=1: that
side is 3H+A+C>=3H+1=q+H, leaving no positive slack. Neither bound
is silently imported from the old system.

## 3. A fully typed false transition

Take q=81,H=40 and

    FA=40, FB=53, FD=52, FC=77, alpha=4.

All four fields are native words below q. Their decoded Boolean words are

    A=0, B=13=(111)_3, D=12=(110)_3, C=37=(1101)_3.

Both seed sides equal158, both local sides equal157, and
FA+FC+alpha=121=q+H. The candidate therefore accepts the endpoint
from binary counter zero to binary counter seven, not zero to one.

The complete packed value and scale are

    P0=r=27985982,
    D0=43046721=3^16.

The packed word has sixteen native ternary digits and its lowest digit
is two. Hence every position carries when P0 is doubled, and
v_3(binom(2r,r))=16. Also r is even, r<D0, D0<r^2 and r>=83.
Thus the counterexample survives the entire binomial and exponent
component, as justified next; it is not merely a local equation failure.

## 4. Positive Pell extension at a general scale

The enlarged kernel proof can be stated independently of a formula
D0=3q^4. Suppose instead that an integer scale D0 and index r satisfy

    D0>=243, r>=83, r<2D0, D0<r^2.                     (3)

With U=wD0,Y=sD0, all bounds in the proof use only these inequalities:
E=UY>=D0^2>r+1, a=Y(U+1)>=D0(D0+1)>2r+1, and
6r/a<12/(D0+1)<1/2. The first index is at least r+1, the main index
at least r+2>=85, and therefore c>A^6>AD^2 and c>2r+1. The generic
relaxed-rank and half-parameter results recover the main index 2r+1;
E>r and the same positive difference
(2P_pell-1)-4A=4Y(U(Y-1)-1)-11 recover the first index r+1.

The ratio argument then gives Y>=U^r, a>U^(r+1), and error below
24r/(U+1). The direct recurrence congruence gives U=3^(2r+1):
both that power and U lie in (0,6a+8). Exact rounding gives
D0|binom(2r,r). No scale being square, nor a factor three outside q^4,
is used in these steps.

For the positive converse, assume additionally that D0 is a power of
three, r is even, and D0 divides the central binomial coefficient.
Set Jmain=2r+1 and choose

    U=3^Jmain, w=U/D0,
    Y=floor((U+1)^(2r)/U^r), s=Y/D0,
    a=Y(U+1), A=a+3, E=UY, P_pell=2UY^2+1,
    c=psi_A(Jmain), d=chi_A(Jmain), k=psi_P_pell(r+1).

Since D0<r^2<U and both scales are powers of three, w is integral
and positive. The binomial expansion gives positive integral s. The
same ratio and tail estimates give positive eta=c-Yk,zeta=k-eta.
The usual formulas for tau,h,gamma are positive integral, including
gamma=(d-U-ac)/(6a+8)>0 because d-ac>2c>U.

Finally choose m=2cJmain, f=chi_A(m), i=(A^2-1)psi_A(m)/c^2,
R=ic^2, y_aux=psi_R(Jmain), u=chi_R(Jmain)/R,
o=(u-c)/f, j=(u-Jmain)/c. Divisibility c^2|psi_A(m) and the two
odd-index polynomial congruences give integrality. Even r supplies
Jmain=1 modulo4, so both signs are positive. Pell growth gives u>c>Jmain,
and all auxiliaries are positive. This is the full positive extension
argument at the general scale (3), not an invocation of the old
D0=3q^4 interface with different inputs.

The concrete scale3^16 and r above satisfy every hypothesis. The
counterexample therefore has all21 positive supplied unknowns.

In fact there is an infinite family: choose q=3^m with m>=4,
H=(q-1)/2, and the same decoded A=0,B=13,D=12,C=37. Set each
native field to H plus its decoded value and alpha=H-36>0.
All equations hold. The packed word has unit two and4m native digits,
and is even because the field sum is4H+62. The general scale conditions
hold for D0=q^4,r=P0, so every family member has a positive Pell
extension and the same false binary endpoint.

## 5. Exact evidence and scope

`../verification/explore_native_ripple_unmasked_carry.py` verifies the
complete62 primitive schedule and all15 fresh source residuals, including
the retained acyclic auxiliary correction. It evaluates the complete
finite outer tuple, the direct digit test, independent factorial
valuation, parity and every prerequisite of the general positive
extension for seven family members.

It does not materialize enormous Pell witnesses. Their existence is
proved above. The arithmetic count is real, but the candidate's
representation claim is refuted. This is neither a new bounded ripple
theorem nor a new universal bound.
