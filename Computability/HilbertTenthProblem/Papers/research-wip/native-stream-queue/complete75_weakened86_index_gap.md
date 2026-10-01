# Restrictions on the remaining negative-index86 branch

The [weakened86 candidate](complete75_weakened_bound86_candidate.md)
remains unresolved. This note strengthens the necessary conditions on
its remaining branch **R<0**, when the computed input root **mu>0**:

    p is odd, n<p<=2n-3,
    Y<=(2(q^2-1)-1)*psi_2(p)+3p-1.

Here n and p are the first and main Pell indices. In particular this
branch cannot have the intended index relation p=2n-1. A new congruence
also restricts every allowed wrap, and zero wrap requires p>E/3.
These are necessary conditions, not a proof that the remaining branch
is empty and not a counterexample to full soundness.

The [checker](complete75_weakened86_index_gap.py) and
[receipt](complete75_weakened86_index_gap.json) retain the exact candidate
source hash. Its **86=48M+38A**,19 positive supplied coordinates and exact
degree203 are unchanged. No comparison, predicate or arithmetic gate is
added to that source. The established75/87 bounds remain unchanged.

The [gap-three successor](complete75_weakened86_gap_three.md) further
excludes p=2n-3 by an exact finite certificate, strengthening this branch
to n<p<=2n-5. Larger odd gaps and mu<0 remain unresolved; this note's
proof and source are unchanged.

## 1. The inherited positive-domain facts

Assume a positive zero under the fixed compiler contract of the
[positive-index analysis](complete75_weakened86_positive_index.md).
Retain its definitions

    q=(B-1)J+1>=16, X=wq^3, Y=sq^3, E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1,
    P=2XY^2+1, k=2*psi_P(n), c=psi_A(p),
    kY<c<k(Y+1), p>=12, n<p<2n.

The literal register named A still holds Delta; A here denotes the
mathematical Pell parameter. The same full strong equation and both
ratio slacks are retained throughout. Let epsilon and lambda be the
index and linear unit signs. Then

    2n=R+epsilon modulo E.                           (1)

For mu>0 the previous theorem supplies v<p and

    R+epsilon-lambda=omega*p-jwrap*c,
    omega in{1,-1}, 0<=jwrap<=2M-1, M=q^2-1.          (2)

The temporary integer jwrap is not the candidate's supplied auxiliary
coordinate j. The sign omega is also distinct from the positive scale
coordinate s in Y=sq^3. Only Sections3--5 assume R<0 and mu>0.

## 2. The main Pell index is odd globally

The complete strong equation is essential here. The
[full strong-rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md),
equations(9)--(10), gives an auxiliary index m with **p divides m**,
in addition to c divides m. The latter divisibility alone would not
justify the following parity argument.

For this candidate, p|m can also be seen directly from the actual
normalized strong factor. At a positive zero it gives

    f^2-Delta*(i*c^2)^2=1,
    f=chi_A(m), psi_A(m)=i*c^2.

The first equality is the literal factor inspected by the checker.
Strong divisibility of the Pell sequence gives

    gcd(psi_A(m),psi_A(p))=psi_A(gcd(m,p))=c.

Strict increase therefore gives p|m. Writing m=p*b, the binomial
expansion modulo c gives

    psi_A(pb)/c=b*chi_A(p)^(b-1) modulo c.

Since c divides the left side and gcd(chi_A(p),c)=1, c divides b.
Thus this normalized factor even gives pc|m. In particular m>2p,
and f>chi_A(2p)>2c, so the auxiliary root V=of-c is positive.
This retains, rather than weakens, the full strong-rank contract.

The auxiliary Pell classification and the
[signed step-down argument](complete75_reversed_auxiliary89.md),
Section4, give a positive **odd** auxiliary index ell with

    ell=+p or-p modulo m.                            (3)

Here oddness follows because T divides chi_T(ell), whereas
chi_T(2r)=(-1)^r modulo T, with T=Delta*i*c^2>1.
As p|m, equation(3) implies p|ell. Therefore p is odd. This reasoning
does not assume either R>0 or mu>0. Together with p>=12 it gives p>=13.

## 3. A small-parameter Pell congruence for every wrap

Because P=1 modulo E, the first Pell sequence gives k=2n modulo E.
Because A=2 modulo Y, the main sequence gives

    c=psi_2(p) modulo Y.

Reducing(1),(2) modulo Y and eliminating R yields

    jwrap*psi_2(p)+2n-omega*p-lambda=0 modulo Y.       (4)

Set d_omega=2n-omega*p-lambda. The strict ratio sandwich gives

    0<=d_omega<3p.

For omega=1 this follows from 1<=2n-p<=p-2; for omega=-1 it
follows from p+1<=2n<=2p-2. The only zero case is
omega=lambda=1 and p=2n-1.

Now assume R<0 and mu>0. The nonnegative integer on the left of(4)
cannot be zero. If it were, jwrap=0 and d_omega=0, so(2) would give
R=p-epsilon+1>0. Therefore it is a positive multiple of Y. Using
the finite wrap bound in(2), we obtain

    Y<=jwrap*psi_2(p)+d_omega
      <=(2M-1)*psi_2(p)+3p-1=:U.                    (5)

This is an upper bound on the actual scale Y, not an assertion that
the original packed fields have already been typed as Boolean words.

There is a stronger modulus in the zero-wrap subcase. If jwrap=0,
omega=1 would make R=p-epsilon+lambda>=p-2>0, so omega=-1.
Equation(1) then implies

    E divides 2n+p-lambda, 0<2n+p-lambda<3p.

Consequently **E<3p**, and p>E/3>=q^6/3. This leaves an unbounded
large-index subcase; it is not its elimination.

## 4. Growth excludes the gap p=2n-1

Write dgap=2n-p>0. The elementary bounds

    psi_A(p)>=(2A-1)^(p-1),
    psi_P(n)<=(2P)^(n-1),
    2A-1>2Y(X+1), 2P<4Y^2(X+1)

give the strict ratio estimate

    c/k>2^(-dgap)*Y^(1-dgap)*(X+1)^(p-n).

The retained upper ratio c/k<Y+1 therefore implies

    2^dgap*Y^(dgap-1)*(Y+1)>(X+1)^(p-n).            (6)

Combining with(5) also gives the fully explicit necessary inequality

    2^dgap*U^(dgap-1)*(U+1)>(X+1)^(p-n).            (7)

Suppose p=2n-1. Then p>=13 gives n>=7, and(6) gives

    Y+1>(X+1)^(n-1)/2>2q^(n+1),                    (8)

where the second inequality uses X>=q^3 and
q^(2n-4)>4. On the other hand,

    psi_2(2n-1)<=4^(2n-2)=16^(n-1)<=q^(n-1),
    6n-3<=q^(n-1).

The last inequality holds for q>=16,n>=7, for example by induction
from n=7. Equation(5) now gives

    Y+1<=(2q^2-3)*psi_2(2n-1)+6n-3
         <=(2q^2-2)*q^(n-1)<2q^(n+1),              (9)

contradicting(8). Thus p cannot equal 2n-1 in the negative-R,
positive-mu branch. Since p is odd globally and p<2n, the remaining
possibility is **n<p<=2n-3**. The other allowed gaps have not been
excluded by this argument.

## 5. Scope and exact checks

The candidate circuit and fixed compiler inputs are unchanged. No
restoration of a complete positive candidate zero is claimed in the
negative-index region. The result is a conjunction of necessary
conditions: odd p, the stricter gap, the wrap congruence(4), the scale
bound(5), the growth inequality(7), and E<3p for zero wrap. The branch
mu<0 remains open as well.

The checker records512 exact modular identities from separate first,
main and parameter2 Pell evaluations. Its formal wrapped targets include
435 negative targets and57 zero-wrap negative targets. It does not
assert that the first-index residual or the full candidate vanishes.
Another1,950 exact ratio-growth cases and90 uniform incompatible-interval
checks audit(6) and the gap-one contradiction. These are partial checks,
not a numerical construction of native Pell zeros.

The parity checks exercise the consequences of p|m and(3), with1,024
odd-index cases and1,504 even-main-index exclusions. Twenty-four index
lattices satisfy the zero-wrap congruence and sandwich at large indices;
their full Pell values are not materialized. The rank theorem itself is
proved or cited in Section2, rather than inferred from these samples.

```sh
python3 complete75_weakened86_index_gap.py
```

Author receipt generation and a fresh default replay both pass. All six
local links resolve. The root reviewer independently read the full proof
and source and ran a fresh default replay; all passed without findings.
That review checked the actual normalized norm's pc|m consequence, odd
auxiliary-index parity, both signs in(4), the strict growth estimates,
the gap-one contradiction and the zero-wrap condition E<3p. It retains
the partial-fixture limits and does not promote the86 candidate to a
universal bound.
