# The fixed-minus Pell kernel necessarily has an odd packed index

Every positive solution of the retained fixed-minus Pell kernel, under
the preliminary bounds of the
[78-operation certificate](FIXED_RAW_UNIVERSAL_78_PROOF.md), has **r odd**.
This is a necessary condition on all positive solutions, not only a
property of the canonical witnesses constructed for completeness.

The result strengthens the
[same-cost odd-index converse](EXPLORATION_ODD_INDEX_PELL_SIGNS.md).
It changes no source equation or arithmetic instruction, and by itself
does not establish a smaller complete certificate. The
[checker](../verification/explore_fixed_minus_index_parity.py) and
[receipt](../verification/explore_fixed_minus_index_parity.json) verify
the exact congruence argument, including noncanonical auxiliary indices
and both signs of the index reduction.

## 1. Facts already obtained independently of parity

Write A=a+2, Delta=A^2-1, and p=J0=2r+1. The retained main-index proof
first establishes, without assuming any parity of r,

    c=psi_A(p), dmain=chi_A(p),
    f=chi_A(m), c divides m, m>=2p,
    R=i*c^2=Delta*psi_A(m)>1.                              (1)

These are the independent main/auxiliary conclusions of the
[half-parameter proof](HALF_PARAMETER_PELL_92_PROOF.md), its
[relaxed auxiliary argument](PELL_RELAXED_AUXILIARY_PROOF.md), and the
fixed-minus modification. In the complete78 system, q>=16 and r>=q^2,
so p>=513. Standard Pell growth therefore gives the strict bounds

    c>2p,              f>2c.                              (2)

For the second, use m>=2p and
chi_A(2p)=1+2Delta*c^2>2c. These bounds do not use r odd, a canonical
choice of m, or the proposed conclusion.

The three relevant source equations are

    U=j*c-p=o*f-c,
    R^2=Delta*(f^2-1),
    R^2*(U^2-y^2)=1-y^2,                                 (3)

where j,o,y and i are supplied positive integers. Although U is an
arithmetic intermediate, it is now strictly positive:

    U=j*c-p>=c-p>0.

This excludes a negative choice of the normalized auxiliary Pell root.

## 2. The stronger plus-sign step-down, including its range

For completeness, the exact version needed here is:

> Let A>=2, m>=1, 0<k<=m and n>=0. If
> chi_A(n)=chi_A(k) modulo chi_A(m), then
> n=+k or -k modulo 4m.

This is the ordinary plus-sign step-down already used in
[the signed-congruence proof](PELL_SIGNED_PROOF.md). The weaker signed
version modulo2m would discard information needed below.

A direct argument also proves the stated version. Put f=chi_A(m).
The addition and doubling identities give

    chi_A(2m)=-1 modulo f, psi_A(2m)=0 modulo f,
    chi_A(n+2m)=-chi_A(n) modulo f.

Together with chi_A(-n)=chi_A(n), these reduce every residue to
either +chi_A(l) or -chi_A(l), with 0<=l<=m. If 0<k<m,
the comparison chi_A(k) lies strictly between0 and f. Also

    chi_A(l)+chi_A(k)<=2chi_A(m-1)<chi_A(m)=f

whenever l<m. The strict inequality follows from the recurrence and
A>=2. Thus the negative representative cannot equal chi_A(k) modulo f,
and the positive representative must have l=k by strict monotonicity.
It corresponds precisely to n=+/-k modulo4m. If k=m, the target
residue is zero and only l=m can give it; again n=+/-m modulo4m.
This also covers m=1, where only the boundary case k=m occurs.

## 3. Retain both congruence signs

From (3),

    (R*U)^2-(R^2-1)y^2=1.

Positivity and the ordinary Pell classification give

    R*U=chi_R(s), y=psi_R(s), s>0.

The index s is odd: for even s, the chi recurrence gives
chi_R(s)=+/-1 modulo R, contradicting R dividing chi_R(s), since R>1.
Write s=2h+1. The integer polynomial Q_h defined by

    chi_X(2h+1)=X*Q_h(X^2)

has recurrence

    Q_0(T)=1, Q_1(T)=4T-3,
    Q_(h+2)(T)=(4T-2)Q_(h+1)(T)-Q_h(T).

The same recurrence proves the two integer identities

    Q_h(0)=(-1)^h*(2h+1),
    Q_h(1-A^2)=(-1)^h*psi_A(2h+1).                       (4)

Therefore U=Q_h(R^2). Since c divides R and
R^2=1-A^2 modulo f, the two fixed-minus source congruences yield

    (-1)^h*s = -p modulo c,
    (-1)^h*psi_A(s) = -c modulo f.                        (5)

Squaring only the second congruence and using
chi_A(2t)=1+2Delta*psi_A(t)^2 gives

    chi_A(2s)=chi_A(2p) modulo f.

The step-down lemma applies with comparison index k=2p and m>=2p.
It gives

    2s=+/-2p modulo4m,
    s=epsilon*p+2m*t, epsilon in {1,-1}, t an integer.     (6)

The division by two here is ordinary integer division of an equality,
not division by a nonunit in a residue ring.

The addition identities also give

    psi_A(2m+z)=-psi_A(z) modulo f.

Using psi_A(-p)=-psi_A(p), equation (6) therefore implies

    psi_A(s)=epsilon*(-1)^t*c modulo f.                   (7)

Because c divides m, it also gives s=epsilon*p modulo c.
Keep the parity of h instead of discarding these signs. Since p=2r+1,

    (-1)^h*epsilon = (-1)^(r+m*t).                       (8)

For epsilon=1, h=r+mt. For epsilon=-1, h=-r-1+mt, and the extra
minus sign gives exactly the same formula (8).

Substituting (7)--(8) into the original two congruences (5), respectively,
produces

    (-1)^(r+m*t)*p = -p modulo c,
    (-1)^(r+(m+1)*t)*c = -c modulo f.                    (9)

The bounds c>2p and f>2c exclude identifying the positive and negative
representatives in either modulus. Hence

    r+m*t is odd,
    r+(m+1)*t is odd.

Subtracting shows that t is even. The first condition then proves

    r is odd, equivalently p=3 modulo4.                  (10)

No canonical choice of the auxiliary index m or the normalized-root
index s was used. In particular s need not equal p.

## 4. Generic signed form and applicability

The same argument has a useful symmetric statement. Assume A>=2,
p>=3 odd, c=psi_A(p)>2p, f=chi_A(m)>2c, c divides m, and m>=2p.
Let R>1 be an integer with c dividing R and
R^2=(A^2-1)(f^2-1). Suppose U,y are positive integers satisfying

    R^2*(U^2-y^2)=1-y^2,
    U=sigma*p modulo c, U=sigma*c modulo f,
    sigma in {1,-1}.

Then the above derivation gives

    (-1)^((p-1)/2)=sigma.                                (11)

Thus the plus branch forces p=1 modulo4, while the minus branch forces
p=3 modulo4. For the retained fixed-minus source, positivity of U is
derived from j>0 and c>p; it is not an extra supplied inequality.

The conclusion applies to every positive full-kernel solution once its
already proved main-index and relaxed-auxiliary facts have been obtained.
It may therefore be used in later soundness arguments before decoding
the represented computation. It does not require the encoded word to
have been proved genuine, and it does not assume that its packed index
had the canonical parity.

Conversely the existing positive odd-index construction supplies the
minus branch when r is odd and the remaining kernel hypotheses hold.
Together, the results explain the exact role of the sign choice. They
do not alone remove an arithmetic operation or change a universal bound.

## 5. Exact checks and evidence boundary

The checker verifies the two polynomial congruences and the strong
plus-sign step-down across bounded exact Pell sequences, including
k=m and both parities of m. It then constructs actual auxiliary norm
parameters with

    m=multiplier*c*p, multiplier=1,2,3,
    s=epsilon*p+2m*t,

using both epsilon signs and both parities of t. It checks c^2 dividing
R, the exact auxiliary norm, and evaluates Q_h(R^2) independently modulo
c and f by its matrix recurrence. Both sign formulas in (9) are checked.
Examples with p=1 modulo4 admit only the plus congruence pair; examples
with p=3 modulo4 admit only the minus pair. Noncanonical m and s are
explicitly included rather than inferred from canonical converse tests.

Several full auxiliary tuples are also materialized, including s=4m-p
and s=4m+p at a noncanonical m. Their norm and positive integral j,o,y
are checked directly. These are auxiliary examples, not materialized
astronomical full packed-kernel tuples. The universal necessity theorem
is the argument in Sections 1--4. The current78 source is unchanged.
