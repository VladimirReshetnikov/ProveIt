# An integral quotient core shares the two signed relator actions

The two signed actions of one relator can be appended at the existing
two-form cut with10M+10A, replacing12M+12A. The saving is2M+2A per
relator. It uses the inverse relation and an integral quotient of the
fixed representation, rather than rank alone. All divisions occur only
in preparing fixed integer numerals; every runtime product and final
accumulator update is charged.

Root requested a bounded continuation of the common-left/right-invariant
idea while composing the guarded two-form source. This is a separate
local theorem. It changes no formed input, positive guard, selector,
native lane, witness or ordinary-input proof, and it does not assign the
new saving to any already frozen complete source.

## 1. Fixed representation and the exact four-input cut

For P=[p,q;s,t] in SL2(Z), let

    A=S(P)=[p^2,-2pq,q^2;
            -ps,pt+qs,-qt;
            s^2,-2st,t^2].                               (1)

The inherited representation gives S(P^-1)=A^-1. Retain the exact right
basis from the three-form and guarded two-form notes. In their notation,
write V=[u;v], a2-by-3 integer row matrix, and let E_+,E_- be the fixed
3-by-2 integer matrices satisfying

    A-I3=E_+ V, A^-1-I3=E_- V.                           (2)

Multiplication on the right by the fixed four-coordinate decoder C gives
the original relator increment identities. The already computed signed
input pairs at the current cut are arbitrary integers

    t_+=(t_+,1,t_+,2)^T, t_-=(t_-,1,t_-,2)^T.

The old append adds E_+ t_+ +E_- t_- to the existing original(d,e,f)
accumulators. In the guarded interface each t_sigma,j is exactly the
selected centered word minus the shared selected-center offset. Their
producers and all lane proofs are outside this cut and remain unchanged.
The replacement below is an identity for all integer t_+,t_- and all
integer accumulator values, without one-hot or positivity assumptions.

## 2. The frozen right basis gives an integral quotient section

For noncentral P the right invariant w0=(2q,p-t,-2s)^T is nonzero.
Divide by its positive coordinate gcd to obtain a primitive vector w.
Both A and A^-1 fix w. The inherited construction first permutes its
coordinates so w1!=0, puts g=gcd(w1,w2)>0 and chooses integers a,b with
a*w1+b*w2=g. In those permuted coordinates it uses

    u=(w2/g,-w1/g,0), v=(-w3*a,-w3*b,g).                  (3)

A direct cross product gives

    u cross v=(-w1,-w2,-w3)=-w.                          (4)

Undoing the fixed coordinate permutation changes the sign, at most, so
the actual original-order rows of V satisfy u cross v=+/-w. This fact
is stronger than their independence over Q: their two-by-two minors
have gcd1, because w is primitive.

Choose a fixed integer row c with c*w=1. Such c exists by the ordinary
Bezout identity for the three primitive coordinates. The3-by-3 matrix

    U=[u;v;c]                                             (5)

has determinant+/-1 by(4), hence an integer inverse. Let J0 be the first
two columns of U^-1. Then

    V J0=I2.                                              (6)

This is a fixed integral right inverse, not a supplied coordinate or a
runtime division. Every column of I3-J0 V is killed by V and therefore
is a rational multiple of w. In fact it is an integer multiple because
w is primitive, but the rational statement already suffices below.

For P=I2 or -I2, retain the earlier central convention V=[e1;e2],
E_+=E_-=0. Set w=e3 and c=e3^T; then U=I3 and J0 is its first two
columns. A=I3 fixes w, and(5)--(6) hold without dividing by the zero
original invariant. This covers every fixed P in SL2(Z).

## 3. An exact integer two-by-two inverse core

Prepare the fixed integer matrix

    T=V A^-1 J0.                                         (7)

Since A^-1 fixes w, it preserves ker V. Hence V A^-1(I3-J0 V)=0, which
proves the exact quotient identity

    V A^-1=T V.                                          (8)

It follows that T does not depend on which integral right inverse J0
was chosen: the difference of two sections has image in ker V.
Moreover T lies in SL2(Z). Indeed U A^-1 U^-1 has last column(0,0,1)^T,
because U w=e3 and A^-1 w=w. Its upper-left block is T, so det T=
det A^-1=1. Equivalently det S(P)=(pt-qs)^3=1 directly from(1).
The trace, if useful for fixed preparation, is(p+t)^2-2. Neither this
trace nor the determinant is a runtime witness or extra comparison.

Use A^-1-I3=-(A-I3)A^-1 and equations(2),(8) to obtain

    E_- V=-E_+ V A^-1=-E_+ T V.

Right multiplication by J0 and(6) now gives the crucial matrix equality

    E_-=-E_+ T.                                          (9)

Consequently, on the original integer input cut,

    E_+ t_+ +E_- t_-=E_+(t_+-T t_-).                     (10)

This is a fixed-coefficient identity, not an assertion that arbitrary
independent assignments to the old E_+,E_- ports satisfy(9). The recipe
(1)--(7) ties every coefficient to the same fixed relator. No division
by a variable, image-lattice index, discriminant or matrix entry appears
in(10). In the central case T=I2 and E_+=0, so the same formula is valid.

## 4. Fully appended paid schedule

Write T=[t11,t12;t21,t22]. First compute

    a1=t11*t_-,1; a2=t12*t_-,2; b1=a1+a2;
    a3=t21*t_-,1; a4=t22*t_-,2; b2=a3+a4;
    z1=t_+,1-b1; z2=t_+,2-b2.                            (11)

The four coefficient products, two sums and two differences cost4M+4A.
The notation t11,... denotes fixed integers; t_-,j denotes the existing
signed variable input, so no coefficient product is silently precomputed.

For each of the three existing output accumulators o_i in the original
(d,e,f) order, use

    p_i=E_+[i,1]*z1;
    q_i=E_+[i,2]*z2;
    a_i=o_i+p_i;
    o_i'=a_i+q_i.                                        (12)

This is6M+6A. It includes both additions per row and all three appends;
it does not stop at three separately computed outputs. Together,

    4M+4A +6M+6A =10M+10A.                               (13)

The former separate signed3-by-2 appends cost12M+12A. Therefore(13)
saves exactly2M+2A per relator at this cut. All zero, unit and negative
coefficient products may be retained in the uniform schedule, including
central relators. Structural register use is not a claim that every
coefficient or polynomial contribution is nonzero.

The new fixed action interface consists of the six entries of E_+ and
four entries of T, replacing the twelve entries of E_+,E_-. The eight
signed form coefficients do not change. Thus the guarded two-form
recipe has6+18r fixed roles after this replacement, rather than6+20r;
the common lambda,Cg and four inherited global roles remain the same.
Preparing U,J0,T is a terminating computation on the fixed relator
matrix. It does not materialize the inherited universal relator list
or turn its uninstantiated size into a numerical universal bound.

## 5. Relation to output-plane factorization and the existing ledger

**Remark 1 (a valid two-sided factorization need not save gates).** A
literal use of both primitive planes gives E_sigma=Bout C_sigma, with
integer2-by-2 cores C_sigma and the earlier sparse integer3-by-2 output
basis Bout. The two core-vector products cost8M+4A; adding their two
outputs costs2A. The generic Bout reconstruction then costs5M+2A and
the three accumulator appends cost3A. This is13M+11A=24, a valid tie
against12M+12A=24. It is not a counterexample to(13), and not a lower
bound for other factorizations. The genuine saving in(13) comes from
the inverse relation(9), which makes one quotient action the identity.

For the frozen guarded two-form interface, the unchanged per-relator
centered-form producers cost8M+8A and selected-center recovery costs
2M+4A. Replacing only its append by(13) gives

    8M+8A +2M+4A +10M+10A =20M+22A                       (14)

per relator. Its shared4M+2A center/guard work,52+4r selected fields,
62+6r native lanes,96+6r positive witnesses and fixed power cost all
remain unchanged. The source domains and positive history projection
do not need a new argument for this local replacement: (10) preserves
the three accumulated polynomials identically on the existing cut.

For r=0 there is no replacement. No old source is silently reassigned
the lower total, and no particular implementation's degree or complete
operation count is inferred from(14). Earlier valid relator-plane,
three-form and guarded schedules remain valid and frozen.

**Open question 1 (separate complete composition, credited to root).**
Emit and independently authenticate the new local rows, their exact
fixed-role recipe and consumer splice in the complete guarded source.
Only after that source/count/positive-domain audit may its complete
ledger incorporate the4r-operation reduction. Further simplifications
of the generic quotient core, or special relator matrices, are separate
questions; rank and determinant alone do not make their products free.

## 6. Proof provenance and execution boundary

Root posed the common-invariant reconstruction problem. The author
derived the integral quotient section, inverse-core identity and paid
schedule above. Aristotle independently challenged the cross-product,
unimodular section, quotient intertwining, central convention and full
append ledger by hand. He subsequently read the full draft, checked the
section-independence, determinant/trace, all-integer cut and retained tie,
and requested no correction. Root also read the complete draft and
independently handchecked the same proof and ledger, with no correction.
These proof challenges do not certify an emitted complete source.

All new reasoning and schedules are handwritten; dependencies are read
inertly. No supplied, archived, committed, predecessor or frozen helper
is run or imported. No saved scientific source or coefficient array is
evaluated or degree-propagated, and no scientific sampling, emitter or
build is used. New files remain in/tmp. Repository files, Git and all
earlier frozen artifacts are unchanged. The companion metadata binds
the exact dependency bytes and read spans.
