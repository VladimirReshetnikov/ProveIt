# Finite residue classification of the negative input-root86 subsystem

The [weakened86 candidate](complete75_weakened_bound86_candidate.md)
remains unresolved. This note treats its remaining **mu<0** branch
without fixing the odd gap `2n-p`. For every fixed main and first Pell
solution, an exact finite congruence test classifies the conjunction of:

* the negative input Pell norm and its retained discriminant equation;
* the retained first-index equation, including its positive slack;
* the auxiliary target congruence modulo the actual main coordinate `c`.

A passing class admits arbitrarily large input indices and positive
extensions of these equations with **R<0**. This is an equivalence for
the stated subsystem, **not** for the full candidate. In particular the
remaining auxiliary norm, auxiliary linear equation, transport equation
and product signs have not been reconstructed.

The test also excludes the negative-input branch at the known ratio
tuple `q=16, p=21, n=15, X=2^21, Y=8192`, uniformly over every admissible
mask pair, input offset and positive outer slack. This is one conditional
exclusion, not a global bound on the main data.

The [checker](complete75_weakened86_negative_input_residues.py) and
[receipt](complete75_weakened86_negative_input_residues.json) retain the
unchanged **86=48M+38A**, 19 positive supplied coordinates and exact
degree203 source. The established75/87 bounds are unchanged. The
[fixed-gap theorem](complete75_weakened86_gap_eleven.md) still leaves
positive-mu gaps at least13 open; the present result does not resolve
the full negative-mu branch.

## 1. Actual candidate data and the exact subsystem

Use the notation and full strong-rank hypotheses from the
[index-gap analysis](complete75_weakened86_index_gap.md). At any actual
positive candidate zero,

    q=(B-1)J+1>=16, X=wq^3, Y=sq^3, E=XY,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    c=psi_A(p), k=2*psi_(2XY^2+1)(n),
    p odd, p>=13, n<p<2n, kY<c<k(Y+1),
    chi_A(p)-a*c=X+gamma*H, gamma=rho+sigma>=2.

The mathematical Pell parameter `A` is distinct from the literal
candidate register named `A`, which holds `Delta`. Write

    C=q-F-alpha-2d*x>=0, u=2d*x+b,
    M=q^2-1,
    K=q(q-F)M+(MC+q(MF+B-1))J,
    R=K-MZ.                                                   (1)

In particular `u,K,M,E,k` are positive and `C` can be zero. The input
coordinate `delta` below is a supplied positive slack, whereas `Delta`
is the Pell discriminant. The exact equations considered here are

    kappa=u+delta*Delta,
    mu=C-Z+a*kappa+rho*H<0,
    mu^2-Delta*kappa^2=1,
    rho+sigma=gamma,
    k-R-hE=epsilon,
    R+epsilon-lambda=omega*p modulo c,                         (2)

with positive `delta,Z,rho,sigma,h` and signs
`epsilon,lambda,omega` in `{1,-1}`. The last congruence is a necessary
consequence of the complete strong auxiliary equations. It is weaker
than those equations. Our finite test does not replace that distinction
by an unproved converse.

The classification theorem is slightly more general: fix any integers
`A>=3`, odd `p>=3`, `E>=2`, `M,K,k,u>=1`, `C>=0`, `gamma>=2` and the
three signs; set `a=A-2`, `H=4a+3`, `c=psi_A(p)`. The actual data above
are a special case. All positive solutions of(2) with R<0 are described
by the finite test below, and each passing class has infinitely many
such solutions. The checker uses small algebraic hosts for this general
statement; it does not call them complete compiler solutions.

## 2. The unbounded input index has finite residue data

The input Pell classification gives a positive integer `v` with

    kappa=psi_A(v), mu=-chi_A(v),
    Z=C+rho*H+F_v, F_v=chi_A(v)+a*psi_A(v).                    (3)

Modulo `Delta`, the binomial expansion gives

    psi_A(v)=v             if v is odd,
    psi_A(v)=A*v           if v is even.                       (4)

Since `A^2=1 modulo Delta`, the discriminant equation in(2) is therefore
equivalent to `v=u modulo Delta` for odd v and `v=A*u modulo Delta` for
even v. Its positive-slack requirement will hold once v is sufficiently
large.

Let `c_-=psi_A(p-1)`. The addition identities give

    chi_A(2p)=1+2Delta*c^2,
    psi_A(2p)=2chi_A(p)*c.

Thus the Pell pair modulo c has period2p, without any claim that this is
the least period. The least nonnegative residues `f_r=F_r modulo c`,
for `0<=r<2p`, have the useful explicit form

    f_r=chi_A(r)+a*psi_A(r)              for 0<=r<p,
    f_p=c-c_-,
    f_r=chi_A(2p-r)-a*psi_A(2p-r)       for p<r<2p.            (5)

Every value is strictly positive and at most `c-c_-<c`. To check the
first interval, `F_r` increases and
`F_(p-1)=c-2c_-`. On the final interval,
`chi_A(s)-a*psi_A(s)=2psi_A(s)-psi_A(s-1)` increases and is less than c
for `1<=s<p`. At r=p, use `chi_A(p)=A*c-c_-`. Finally, negating the
Pell index modulo2p proves the last residue formula.

For the first-index equation we also need the Pell pair modulo E. Its
one-step transformation is

    (x,y) -> (Ax+Delta*y, x+Ay) modulo E.

The determinant is1, so this is a permutation. The orbit of `(1,0)` is
therefore periodic from its start, with a return period `T<=E^2`.
Any positive return period suffices. Let

    f^E_t=(chi_A(t)+a*psi_A(t)) modulo E, 0<=t<T.              (6)

The mathematical procedure is finite but need not be efficient: neither
E nor the number of main Pell solutions is bounded here. The checker's
period finder has an explicit size limit, and its actual large compiler
tuple is rejected before any search for a period modulo E.

## 3. The finite CRT test and its exact converse

Enumerate `0<=r<2p` and `0<=t<T`. First intersect the three index classes

    v=r modulo2p,
    v=t moduloT,
    v=u moduloDelta       if r is odd,
    v=A*u moduloDelta     if r is even.                       (7)

Their generalized CRT intersection is empty or a single class
`v=v0 modulo L`, where `L=lcm(2p,T,Delta)`. Equivalently, each pair of
residues must agree modulo the gcd of its two moduli. In particular, the
first and third classes require

    gcd(2p,Delta) divides r-u       if r is odd,
    gcd(2p,Delta) divides r-A*u     if r is even.              (8)

For a nonempty index class, the two retained target equations in(2)
become

    MH*rho = K-M(C+f_r)+epsilon-lambda-omega*p modulo c,
    MH*rho = K-M(C+f^E_t)+epsilon-k           modulo E.        (9)

For any linear congruence `a0*rho=b0 modulo m0`, set
`g0=gcd(a0,m0)`. It has no solution unless `g0|b0`; otherwise divide by
g0 and invert `a0/g0` modulo `m0/g0`. Apply this separately to both
congruences(9), then intersect their solution classes by generalized
CRT. If the intersection is `rho=rho0 modulo N`, choose its least
positive representative `rho_min`, using N when rho0=0. The exact
positive-domain test is simply

    rho_min<gamma.                                            (10)

All permitted rho are the finite progression
`rho_min+jN<gamma`. There is no need to iterate up to gamma.

Necessity follows directly by reducing any solution of(2). Conversely,
take a passing pair of index classes and any permitted rho. Set
`sigma=gamma-rho>0` and choose `v=v0+Lz` with z sufficiently large.
Define kappa,mu,Z by(3), then put

    delta=(psi_A(v)-u)/Delta,
    R=K-MZ,
    h=(k-R-epsilon)/E.                                       (11)

The index CRT makes delta an integer. The two rho congruences make h
an integer and give the target congruence modulo c. As z increases,
`psi_A(v)` and `F_v` tend to infinity. Consequently delta and Z are
positive, R<0, and h>0 for all sufficiently large z. The input norm is
identically1 and mu is strictly negative. This proves the stated iff
and the infinite extension property for the subsystem.

This theorem pays the actual first-index equation as well as the input
equations. It does not pay the remaining strong auxiliary equations.
In particular, the congruence modulo c alone does not produce positive
values of the candidate's supplied auxiliary fields. There is no claim
that any passing class is a full positive86 zero.

## 4. An actual all-mask exclusion at the ratio survivor

The [gap-nine proof](complete75_weakened86_gap_nine.md) had one ratio
survivor in its finite necessary positive-mu domain:

    q=B=16, d=4, J=1, X=2^21, Y=8192, n=15, p=21.             (12)

These values satisfy both strict ratios and the actual main equation
with positive integral
`gamma=(chi_A(p)-a*c-X)/H`. Here c has701 bits, gamma has666 bits,
`gcd(MH,c)=15`, and `gcd(2p,Delta)=21`.

We now exclude mu<0 at(12) by a superset of the test in Section3: impose
the input-index condition(8), the target congruence modulo c, and
`1<=rho<gamma`, but omit the first-index equation, the transport equation
and all restrictions between the three signs. This avoids needing the
large modular period for E.

Positive F and alpha and `C=16-F-alpha-8x>=0` force x=1. Every remaining
positive pair satisfies `F+alpha<=8`, giving28 pairs. The compiler mask
contract gives exactly

    (MC,MF)=(6,12), (10,12), (14,4).

All15 offsets `1<=b<16` and all8 sign triples are retained. For each
combination, condition(8) permits exactly two classes modulo42. The
resulting20,160 necessary cases all fail:

* 19,320 have an insoluble rho congruence modulo c;
* the other840 have least positive rho at least gamma.

The receipt records all840 exact interval comparisons as integers. No
floating approximation, first-index search or assumed native typing is
used. Thus **no full positive86 zero with mu<0 has the data(12)**, for
any fixed compiler coefficients satisfying the stated contract. In
combination with the earlier positive-mu wrap exclusion, this tuple
cannot support an R<0 zero of either input-root sign. Other main data
are not eliminated by this calculation.

## 5. Source scope and replay

The candidate source hash, all86 operations, full strong rows, both
ratios and retained input rows are checked through the frozen inherited
source contract. No gate, comparison or coordinate is changed.

The arithmetic audit includes1,440 modular Pell/discriminant checks with
indices as large as10^24,190 modular state periods and1,156 CRT
intersections checked against direct finite enumeration. On64 small
algebraic hosts it independently scans all5,784 indices in the common
period and every permitted rho, comparing with the compressed CRT
description. Thirty-two hosts have subsystem solutions, and72 exact
positive reconstructions check the input norm, discriminant equation,
positive rho/sigma, negative R, positive first-index slack and target
congruence. These hosts do not assert the compiler mask/ratio contract
or any complete positive polynomial zero.

```sh
python3 complete75_weakened86_negative_input_residues.py
```

Author receipt generation and a fresh default replay pass. All six
local links resolve. Root independently read the proof and source and
ran a fresh default replay, with no findings. His separate oracle
reconstructed all20,160 mask cases and840 interval comparisons without
the author's residue or CRT helpers. On24 additional hosts with
`A` in `{7,8,11}`, `p` in `{7,9}` and `E` in `{6,8,9,11}`, it checked
12,504 complete-period index visits and matched all29 passing pairs.
Native's independent full
proof/source/fresh-default review also passes. His separate sequential
Pell and finite-state oracle checked48 new complete-period hosts,
including nonminimal supplied periods,9,268 index visits,30 permitted
index/rho pairs and24 positive subsystem reconstructions. He also
independently regenerated all20,160 actual-mask cases, matching the
19,320 gcd rejections and all840 exact interval certificates.

The full86 candidate remains unresolved; this packet provides an exact
finite subsystem classification and one conditional all-mask exclusion,
not a universal86 bound.
