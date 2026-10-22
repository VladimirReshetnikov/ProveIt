# The two Pell interfaces used by the fixed-input equations

All references below are pinned to ProveIt commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.
For an integer A>=2 define Delta=A^2-1 and

    chi_A(0)=1, chi_A(1)=A,
    psi_A(0)=0, psi_A(1)=1,
    z(n+2)=2A*z(n+1)-z(n).

Equivalently, chi_A(n)+psi_A(n)*sqrt(Delta)
is the n-th power of A+sqrt(Delta).

## Lemma1: the ordinary strong square restores Pell integrality and rank

**Premises.** A,p,c,i,f are positive integers, A>=2,

    c=psi_A(p), c>A*Delta^2,
    (i*c^2)^2=Delta*(f^2-1).

**Conclusion.** There is a positive integer m such that

    p divides m, c divides m,
    f=chi_A(m), i*c^2=Delta*psi_A(m).

In particular m>=c, and c^2 divides f^2-1, since

    f^2-1=Delta*psi_A(m)^2=i*c^2*psi_A(m).

No auxiliary norm, target index, ratio condition, exponent conclusion,
or computation encoding is a premise of this lemma. The inequality
c>A*Delta^2 must be established before the lemma is applied.

**Source and proof mechanism.** The full elementary proof is in

    Computability/HilbertTenthProblem/Papers/1980/PELL_RELAXED_AUXILIARY_PROOF.md

under the headings "The relaxed norm forces an integral Pell solution
at A" and "Recovering the required divisibility of the auxiliary index".
Its proof factors Delta into squarefree part times a square, compares
the fundamental unit of that quadratic ring with A+sqrt(Delta), and
uses strong divisibility of psi. The bound c>A*Delta^2 excludes the
proper-divisor rank alternative. The final binomial expansion modulo c
proves c|m. The source's temporary notation A=a+4 is irrelevant to this
abstract lemma; the argument uses only A>=2 and its stated premises.

## Lemma2: the two minus congruences identify the target index

**Premises.** All A,p,m,c,f,I,V,y,o,j,r are positive integers,
A>=2, I>1, Delta=A^2-1, and

    c=psi_A(p), f=chi_A(m), c divides m, c divides I,
    0<2p<m, 0<2p<c, 0<2r<c,
    I^2=Delta*(f^2-1),
    I^2*(V^2-y^2)+y^2=1,
    V=of-c=jc-r.

**Conclusion.** p=r.

**Proof.** The auxiliary norm is
(IV)^2-(I^2-1)y^2=1. Positive Pell classification gives
IV=chi_I(ell), y=psi_I(ell) for ell>0. Since I divides chi_I(ell)
and I>1, ell is odd: chi_I(2v)=(-1)^v modulo I. Write ell=2v+1.
The integer polynomials Q_v defined by

    chi_X(2v+1)=X Q_v(X^2)

satisfy

    Q_v(1-A^2)=(-1)^v psi_A(2v+1),
    Q_v(0)=(-1)^v(2v+1).

Thus V=Q_v(I^2). Reducing modulo f and using V=-c modulo f gives
(-1)^v psi_A(ell)=-psi_A(p) modulo f. Squaring and using
chi_A(2z)=1+2Delta*psi_A(z)^2 yields

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The signed chi step-down fact below, with comparison index2p<m,
gives ell=+p or-p modulo m, hence modulo c. Independently, c|I
and V=-r modulo c give (-1)^v ell=-r modulo c. Therefore
r=+p or-p modulo c. The strict bounds0<r,p<c/2 leave only r=p.

The odd-index polynomial identities are proved by their elementary
recurrence in sections3-4 of

    Computability/HilbertTenthProblem/Papers/1980/HALF_PARAMETER_PELL_92_PROOF.md.

Their application with both minus signs and a general target is in
section4, "Recovering the displaced main index", of

    Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.md.

### Signed chi step-down, with a direct elementary proof

For A>=2, m>=1, n>=0 and0<k<=m,

    chi_A(n)=+/-chi_A(k) modulo chi_A(m)
        implies n=+/-k modulo2m.

The addition identities give chi_A(n+2m)=-chi_A(n) modulo chi_A(m),
and chi_A(2m-r)=-chi_A(r) modulo chi_A(m). Reduce n modulo2m and
reflect the remainder to0<=r<=m. Then chi_A(r)=+/-chi_A(k) modulo
chi_A(m). If k=m, only r=m is possible, because all earlier positive
chi values lie strictly below chi_A(m). If k<m, then m>=2. For r<m,

    chi_A(r)+chi_A(k)<=2chi_A(m-1)<chi_A(m),

where the final inequality follows from the Pell recurrence and
strict growth. The negative congruence is therefore impossible, and
the positive congruence forces chi_A(r)=chi_A(k), hence r=k.
The case r=m cannot occur when k<m. This proves the statement.

The repository also records this observation in

    Computability/HilbertTenthProblem/Papers/1980/PELL_SIGNED_PROOF.md,

under "The signed chi step-down observation". The direct argument
above avoids importing the stronger modulo4m version quoted there.

## How the current equation meets the interfaces

The first/main norms and index unit establish n>=24,p>n and
c=psi_A(p)>A*Delta^2 before any auxiliary classification. Lemma1
then supplies m, f and I, with m>=c>2p. Positive reconstruction gives
o,j,V and r=R; the earlier size bounds give c>2R. Lemma2 proves p=R.

Only afterwards eliminate the first-index wrap. Write
2n=R+epsilon+vE with v>=0. The asymmetric source gives E>R+2.
If v>=1 then2n>=R-1+E>2R+1>2p, contradicting n<p=R.
Thus2n=R+epsilon. **No estimate E>2(R+2) is used or claimed.**
