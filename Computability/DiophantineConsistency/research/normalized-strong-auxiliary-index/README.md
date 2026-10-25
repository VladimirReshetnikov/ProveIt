# Recover a Pell ordinate and its index without a supplied main ordinate

This code-free ordinary lemma validates the proposed normalized-strong argument,
including signed auxiliary V. It recovers the Pell index before using a supplied
main norm. It does not remove that norm's separate trace-calibration role, and
no current gate or variable saving is established. No application, compiler,
Lean or TeX/PDF tool was run, and no accepted or held code was changed.

## Exact statement

Let A,c,i,f be integers with A>=3, c>=2 and i,f>0. Let T,R,y be arbitrary
integers, and set

    Delta=A^2-1, b=i*c^2, S=Delta*b,
    V=f^2*(c*T-R)-c.

Assume exactly

    f^2-Delta*b^2=1,
    S^2*(V^2-y^2)+y^2=1.                         (1)

For the Pell sequences chi_A,psi_A with initial pairs (1,0),(A,1), there
are a unique positive index m and a unique index r such that

    f=chi_A(m), b=psi_A(m),
    3<=r<m, r odd, c=psi_A(r), r*c divides m,
    R=+r or -r modulo c.                          (2)

In particular c is odd and 0<r<c/2. If additionally 0<R<c/2, then

    r=R and c=psi_A(R).                           (3)

No positivity assumption on V, y or T is needed; V and y are automatically
nonzero. The displayed V formula is used only for its congruences modulo f
and c. This is a necessary-condition lemma, not an unrestricted converse.

## Odd-index polynomial and the two Pell classifications

For every integer parameter t and j>=0, define integer polynomials

    Q_0(X)=1, Q_1(X)=4X-3,
    Q_(j+1)(X)=(4X-2)*Q_j(X)-Q_(j-1)(X).

The Pell recurrences give, with n=2j+1,

    chi_t(n)=t*Q_j(t^2),
    Q_j(0)=(-1)^j*n,
    Q_j(1-A^2)=(-1)^j*psi_A(n).                  (4)

The first identity follows from the odd-subsequence recurrence with
coefficient 4t^2-2 and initial values t,4t^3-3t. At X=0 the recurrence
has coefficient -2, giving the second identity. For the third, the sequence
(-1)^j*psi_A(2j+1) starts with 1,1-4A^2 and has recurrence coefficient
2-4A^2, exactly Q evaluated at 1-A^2. These are integer polynomial identities,
so their reductions modulo f are valid.

Since b>0, the first norm in (1) gives the unique m>=1 with
f=chi_A(m), b=psi_A(m). This is the ordinary integer-coordinate Pell
classification for discriminant A^2-1, whose least positive solution is (A,1).

Here S>=32. The second norm is

    (S*V)^2-(S^2-1)*y^2=1.

If V=0 its left side is nonpositive; if y=0 it would give S^2*V^2=1.
Both are impossible. Classifying (S*abs(V),abs(y)) therefore gives n>=1
with chi_S(n)=S*abs(V) and psi_S(n)=abs(y). Modulo S, chi_S(2k)=(-1)^k,
whereas chi_S(2k+1)=0. Thus n is odd. For some epsilon in {1,-1},

    V=epsilon*Q_j(S^2), n=2j+1.

The strong norm gives S^2=Delta*(f^2-1)=1-A^2 modulo f, and the V formula
gives V=-c modulo f. Equation (4) consequently implies

    psi_A(n)=+c or -c modulo f.                  (5)

The sign epsilon is retained throughout; no sign of V was assumed.

## Fold the entire auxiliary index, with the correct signs

Use formal quadratic multiplication with u=A+sqrt(Delta). The doubling
identities give

    chi_A(2m)=2f^2-1=-1 modulo f,
    psi_A(2m)=2fb=0 modulo f.

Thus u^(2m)=-1 modulo f: 2m is an anti-period, and 4m a period. Write
n=2qm+s with 0<=s<2m, and put r=s if s<=m, otherwise r=2m-s. For s>m,
u^s=u^(2m)*u^(-r) shows psi_A(s)=psi_A(r) modulo f; the block quotient
contributes the possible sign (-1)^q. Hence

    0<=r<=m, n=2km+r or 2km-r for an integer k,
    psi_A(n)=+psi_A(r) or -psi_A(r) modulo f.

In combination with (5), psi_A(r)=+c or -c modulo f. But

    0<=psi_A(r)<=b, b=i*c^2>=c^2>c,
    f^2=1+Delta*b^2>4b^2, so f>2b and f-b>c.

The interval [0,b] contains exactly one integer congruent to either +c
or -c modulo f: the integer c. Therefore psi_A(r)=c. Since psi_A(0)=0,
psi_A(1)=1 and b>c, we have 2<=r<m. The exact index fold preserves parity,
so n odd implies r odd, hence r>=3. The recurrence modulo 2 gives
psi_A(r)=r modulo 2, so c is odd. Uniqueness follows from strict growth.

## The full r*c divisibility, without a sign or rank assumption

Put C=chi_A(r), so C^2-Delta*c^2=1 and C is a unit modulo c. Write
m=q*r+s with 0<=s<r. Since u^r=C+c*sqrt(Delta), reduction modulo c gives

    psi_A(m)=C^q*psi_A(s) modulo c.

Now c divides psi_A(m)=i*c^2. As C is a unit and 0<=psi_A(s)<c, this
forces s=0. Thus m=r*t for a positive integer t. This is also the usual
strong-divisibility implication psi_A(r)|psi_A(m) => r|m.

Composition gives psi_A(r*t)=c*psi_C(t). Its quotient sequence satisfies

    psi_C(t)=t*C^(t-1) modulo c,                 (6)

because C^2-1=Delta*c^2 is zero modulo c. Explicitly the binomial formula
is the sum of binom(t,2k+1)*C^(t-2k-1)*(C^2-1)^k for
0<=k<=floor((t-1)/2); only k=0 survives.
Since c^2 divides psi_A(m), c divides psi_C(t), and (6) with C a unit
gives c|t. Therefore r*c|m. This argument needs no supplied main abscissa
and no large-c ordinary-strong rank theorem.

## Recover R in its stated window

The exact fold n=2km+/-r and c|m give n=+r or -r modulo c. Also c|S,
so (4) gives V=epsilon*(-1)^j*n modulo c. On the other hand the strong
norm gives f^2=1 modulo c, and hence V=-R modulo c. Thus R=+r or -r
modulo c, as asserted.

For A>=3 the recurrence gives psi_A(k+1)>=(2A-1)*psi_A(k) for k>=1;
with psi_A(2)=2A>=6 this implies psi_A(r)>2r for r>=2. Thus 0<r<c/2.
If also 0<R<c/2, the +r congruence forces R=r, while R+r is strictly
between 0 and c and cannot be divisible by c. This proves (3).

The window cannot simply be omitted: replacing T by T+k and R by R+k*c
leaves V and both norms unchanged. The unconditional conclusion is the
signed congruence, not equality with an arbitrary integer R.

## Current arithmetic boundary and provenance

This lemma applies to the normalized strong equation in the accepted P66
setting. It is not obtained by canceling Delta from the different ordinary
equation (i*c^2)^2=Delta*(f^2-1). The direct squared-modulus Q identities
and normalized source setting are pinned with the local H10/Pell materials.

The useful result is earlier index recovery, including removal of a sign
premise for V. It does not recover the supplied main trace D. In the current
P66 circuit A=a+2, H=4a+3 and D=X+a*c+gamma*H; its norm links that
specific D to chi_A(R). The standard trace congruence is

    chi_A(R)-(A-2)*psi_A(R)=2^R modulo (4A-5)=H.

Thus the supplied main norm gives X=2^R modulo H, the separate residue used
in the power-of-two/native calibration. Merely proving c=psi_A(R) does not
impose that trace residue. N1 and gamma therefore remain in the current
equation. No changed circuit, gate count, variable count or degree is claimed.

SOURCE_PINS records the exact mathematical files and the complete sealed
current P66 parent. This is an ordinary proof note, not a new Lean theorem
or native/compiler replay. Only this note and its inert pins/manifest are new.
