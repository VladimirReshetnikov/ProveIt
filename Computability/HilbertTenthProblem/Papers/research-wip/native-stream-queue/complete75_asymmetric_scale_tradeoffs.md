# Asymmetric scales lower the complete87/88 degrees to169/125

> The [linear-input/gap and grouping extension](complete75_asymmetric_linear_gap_tradeoffs.md)
> gives the combined exact frontier87/169,88/125,89/113,90/109,91/104,
> 92/92,93/72,94/62,95/60,96/50,97/48,98/44, with19 witnesses.
> The87/169 and88/125 endpoints and their proofs below remain unchanged.

Change only `X=w*q^3` to **`X=w*q`**, keeping `Y=s*q^3`, in the
[normalized87](complete75_normalized_strong87.md) and
[coupled88](complete75_coupled_index_linear88.md) sources. The resulting
universal polynomials have the following exact ledgers:

| Strong treatment | Polynomial operations | M | A | Exact degree | Certificate operations | Equations | Positive witnesses |
|---|---:|---:|---:|---:|---:|---:|---:|
| Normalized |87|48|39|**169**|86|1|19|
| Ordinary |88|47|41|**125**|87|1|19|

The ordinary positive input and every fixed compiler numeral are unchanged.
Each new source is in bijection with its own parent's **full positive
integer zero set**, by changing just the supplied coordinate w. The
operation count is unchanged; the separate complete comparison bound75
is unchanged. The historical87/203 and88/151 files remain frozen.

The new first-index argument needs `E>R+q^3`, rather than `E>2R`.
The lower Pell ratio then supplies the growth needed for exponent
recovery before any upper-error estimate. Once X is a power of two,
the retained factor q in X restores divisibility by the parent's q^3.
These are the same proof-order ideas used in the
[fixed-affine exponent52 component](pell_fixed_affine_exponent52.md),
applied here to the unchanged complete compiler and its packed index.
No ratio, strong norm, mask, input equation or positive coordinate is
discarded.

## 1. Literal source and coordinate identities

Keep the complete fixed compiler hypotheses of the selected parent,
including `B=2^d`, `d>=4`, its actual masks

    0<MC,MF<B−1, MC=2 mod4, MF=4 mod8,
    popcount(MC)+popcount(MF)=d,

and the full layout, ordinary-input and synchronization contract.
The nineteen positive coordinates retain the names

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma.

The source names for J,g,y are Jrep,tau_gap,y_aux. Definitions are
identical to each parent except for X:

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A²−1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    C=q−F−Z−alpha−2dx, W=C−Z,
    kappa=2dx+b+delta*Delta, mu=W+a*kappa+rho*H,
    G=q²−Z−qF,
    R=G(q²−1)+(MC+q(MF+B−1))J,
    V=of−c, Kindex=k−hE.

Every norm, index, transport and linear factor remains the selected
parent's literal expression. In particular the two potentially signed
linear units are

    Nk=Kindex−R, L=V−jc+Kindex,

and the transport unit is

    Nt=(DC+B*DR+X)C+(q−F)−zplus(q−1).

The [checker](complete75_asymmetric_scale_tradeoffs.py) accepts only the
entire selected canonical parent polynomial. It changes exactly

    wn2=w*n2  ->  wn2=w*q,

where `n2=q³` remains live in `sn2=s*n2`. No gate is inserted or erased,
and no metadata interface or residual is inherited from a different
source. The [receipt](complete75_asymmetric_scale_tradeoffs.json) contains
both complete output DAGs and their exact counts.

For any rational assignment with q nonzero, putting

    w_old=w_new/q²                                    (1)

and keeping all other coordinates fixed makes **every computed register**
of the old and new source equal. This includes all eight factors and
the final product-minus-one polynomial. Conversely,

    w_new=q²*w_old                                    (2)

has the same complete identity. These are off-zero rational identities;
(1) is not an integer substitution on arbitrary supplied tuples.
The main proof below establishes its positive integrality precisely
where it is needed.

## 2. Bootstrap bounds and auxiliary rank

First consider a positive zero of the new ordinary88 source. Its norm
sign arguments are unchanged and do not use the old scale lower bound:
Delta is0 or3 modulo4, the ordinary auxiliary coefficient is0 or1
modulo4, and the first norm reconstructs a positive root of

    tau²−V0(V0+1)k²=1, V0=XY²>1.

The negative-norm equation for V0(V0+1) has the same elementary strict
descent as in coupled88 §2. Thus the five norm factors are+1, and

    Nk=epsilon, L=lambda, Nt=nu,
    epsilon,lambda,nu in{−1,1}, epsilon*lambda*nu=1.   (3)

For a zero of the new normalized87 source, its unconditional strong
sign gives `f²−Delta*(ic²)²=1`. The positive proof-only substitution
`i_ordinary=Delta*i_normalized` gives exactly a zero of the new
ordinary88 source, with the same X,Y and all first/main data.
This is the local algebra of normalized87 §2, valid before any compiler
or scale theorem; it does not assume the conclusion being proved here.
We may therefore perform the following common index analysis in the
ordinary source. At the end, (1) will be applied directly to the original
normalized tuple, without changing any of its auxiliary coordinates.

Weak transport still forces C>=0. Indeed, if C<=−1 then its first
term is at most `−(DC+B*DR+X)<−1`, while its remaining term is
`1−F−(zplus−1)(q−1)<=0`. The positive slack gives F+Z<q. Exactly
the parent's elementary packing estimates consequently give

    (2q−1)(q²−1)<R<q⁴−q³,
    q>=B>=16, X>=q, Y>=q³,
    E>=q⁴>R+q³, a>R+2.                              (4)

In particular `0<R+epsilon<E`. Put P=2XY²+1. Then

    P−A=XY(2Y−1)−Y−1>0.

The positive first norm gives a unique n>=1 with
`k=2*psi_P(n)` and positive root `tau=chi_P(n)`. Because P=1 modulo E,

    2n=R+epsilon+vE, v>=0,
    n>=(R−1)/2.                                     (5)

The nonnegativity of v follows from `0<R+epsilon<E` and 2n>0;
we have not set v to zero. The positive main norm gives
`c=psi_A(p), D=chi_A(p)`. Since P>A and c>k, p>n. In particular
p is much larger than6, so elementary Pell growth yields

    c>A*Delta², c>2p.

Also `k=R+epsilon+hE` and Y>=q³ imply

    c>kY>2(R+2).                                    (6)

These are exactly the hypotheses of the retained generic strong-rank
lemma used in coupled88 §3. It restores

    f=chi_A(m), c divides m, m>=c>2p,
    ic²=Delta*psi_A(m)

in the ordinary strong source. Thus f>2c and V=of−c>0. The normalized
source alternatively gives the stronger direct divisibility pc|m by
the argument of exponent52 §2, but that strengthening is not needed.

Set `Jtarget=R+epsilon−lambda`. From(4),(6),

    0<Jtarget<c/2, 0<p<c/2,
    V=jc−Jtarget=of−c.

The unchanged odd-quotient and signed step-down proof in coupled88 §3
therefore gives

    p=Jtarget=R+epsilon−lambda.                       (7)

This application uses only the displayed bounds and the full strong
and auxiliary equations. It uses neither an exponent conclusion nor
any decoded field mask.

## 3. No first-index wrap, then lower-ratio power recovery

If v>=1 in(5), then(4) gives

    2n>=R−1+E>2R+q³−1>2(R+2)>=2p.

This contradicts n<p. Hence

    2n=R+epsilon, p=2n−lambda.                       (8)

This is where the new proof replaces the parent's stronger E>2R bound.
In fact E need only exceed R+5 at this step; the paid new scale gives
a margin greater than q³.

If lambda=−1, then p=2n+1. For Q2=chi_A(2), one has Q2>P and
A>Y+1. The Pell duplication identity and parameter monotonicity give

    psi_A(2n)=2A*psi_Q2(n)>=2A*psi_P(n)=A*k,

so c=psi_A(2n+1)>A*k>k(Y+1), contradicting the supplied positive
ratio slacks. Therefore lambda=1. Write

    p=2r+1, r=n−1, r>=1, k=2*psi_P(r+1).

The lower Pell ratio estimate used in half-binomial42 §5 is

    c/(k/2)>=xi*(1+3/(2a))^(2r)
                    *(1+1/(2XY²))^(−r)>xi,
    xi=(X+1)^(2r)/X^r.                              (9)

The weak inequality follows directly from
`psi_A(2r+1)>=(2A−1)^(2r)` and
`psi_P(r+1)<=(2P)^r`. Its strict comparison needs only `6XY²>a`,
which follows here from X>=16,Y>=4096. In particular (9) does not use `4r/a<1/2`, an upper
ratio error estimate, or X>=q³. The retained upper ratio c/k<Y+1
now gives

    Y>xi/2−1>X^r/2−1>X^r/3,
    a=Y(X+1)>X^(r+1)/3.                             (10)

For X>=16,r>=1,

    2^p=2*4^r<X^(r+1)/3<a, X<a.                    (11)

For completeness, the projection congruence can be recovered directly
without a stronger exponent criterion. The sequence
`z_j=chi_A(j)−a*psi_A(j)` starts at1,2 and satisfies the Pell recurrence.
Modulo the odd integer H=4a+3, `4A−1=4 mod H`; induction therefore
gives z_j=2^j modulo H. The retained main-root definition says
z_p=X+(rho+sigma)H. Thus `X=2^p mod H`. Both positive representatives
are below a by(11), so

    X=2^p.                                           (12)

No upper binomial approximation or population test has yet been used.

## 4. Restore the parent's full positive zero set

Since X=wq and q>0, (12) implies `q=2^t`, with integer t>=4.
From(4),(7), p>3q>3t. Consequently q³ divides X and

    w_old=X/q³=w_new/q²

is a strictly positive integer. Every other retained coordinate is
unchanged and positive. Identity(1) now gives a genuine positive
integer zero of the **selected original87 or88 source**, including
its complete polynomial, compiler masks, input bridge and domains.
Its established soundness theorem applies. In particular any remaining
negative index/transport sign is excluded by the original paid
population argument; we have not silently assumed that sign here.

Conversely every positive parent zero maps by(2) to a positive integer
new zero, preserving every computed register. This direction requires
no fresh auxiliary Pell family and no special canonical-subfamily
restriction. The maps(1),(2) are inverse on the full positive zero sets.
Thus each construction preserves even the other eighteen supplied
witnesses, not merely the accepted ordinary-input projection. The
normalized and ordinary constructions are each compared with their
own frozen parent; no bijection between those two strong treatments
is asserted.

The retained Y=sq³ is essential to this result. It continues to pay
the population threshold used to decode the compiler masks. This note
does not delete that multiplier or assert that the standalone free-Y
exponent component can replace that mask threshold.

## 5. Exact arithmetic degrees

Let Q0=(B−1)J, k0=eta+zeta, gamma0=rho+sigma and
`Ctop=Q0−F−Z−alpha−2dx`. The leading forms shared by both sources are

| Factor | Degree | Highest homogeneous form |
|---|---:|---|
| N0 |12| `w*s²*k0*Q0^7*(2g−k0)` |
| N1 |18| `8*gamma0*k0*w²*s³*Q0^11` |
| N2 |32| `−4*delta²*w^5*s^5*Q0^20` |
| Nk |7| `−h*w*s*Q0^4` |
| Nt |3| `w*Q0*Ctop` |
| L |7| `−h*w*s*Q0^4` |

The ordinary auxiliary and strong factors have degrees24 and22,
with highest forms `f²*k0²*w²*s^4*Q0^14` and
`i²*k0^4*s^4*Q0^12`. The normalized factors have degrees56 and34,
with highest forms `i²*k0^6*w^4*s^10*Q0^34` and
`−i²*k0^4*w²*s^6*Q0^20`. These follow from the actual norm
cancellations, not the uncorrected syntactic maximum at subtraction
gates. For example the main and input norm identity is

    (ac+L0)²−(a²+H)c²=2acL0+L0²−Hc².

In the product's inherited factor order the exact degrees are

    normalized:12,18,32,56,7,3,34,7,
    ordinary:  12,18,32,24,7,3,22,7.

Their sums are169 and125. The complete leading forms are respectively

    32Q0^101 h² gamma0 delta² i^4 k0^12
        *w^17 s^28 Ctop(2g−k0),
    −32Q0^73 h² gamma0 delta² i² f² k0^8
        *w^13 s^20 Ctop(2g−k0).

Both are nonzero for every fixed admissible B. Thus the degrees are
exact, not merely propagated upper bounds. The one changed instruction
is still a multiplication, and all gates remain ancestors of the final
output. The historical multiplication/addition totals are preserved.

## 6. Verification and limits

Default execution reconstructs the deterministic receipt:

    /tmp/diophantine-research-venv/bin/python complete75_asymmetric_scale_tradeoffs.py

The audit checks both complete canonical callers, the single changed
row, every dependency and output ancestor, and rejection of truncated,
extended, altered-Y and wrong-parent callers. It compares every
computed register and final polynomial in both coordinate directions
on768 assignments, half signed:1,536 complete identities, including768
signed identities. Rational inverse fixtures are explicitly counted
and are not passed off as positive integer zero maps.

Six weighted univariate source expansions check every factor degree
and both complete leading coefficients. Separate finite audits cover
the new pretyping margins, every tested sign/wrap combination, the
lower-ratio no-wrap inequality and restored scale exponent. The
projection recurrence is checked on1,024 Pell pairs. Five small
half-binomial first/main blocks check strict ratio slacks and root/index
identities; these are separate component fixtures, not complete
compiler zeros or materialized astronomical auxiliary witnesses.
The positive-domain bijection is proved in Sections2–4, rather than
inferred from those finite tests.

Root full proof/source review and fresh replay passed. A separate full
proof/source/dependency review and fresh replay also passed with no
findings. Its independent executor checked640 whole-register maps in
both directions(320 signed),320 eight-factor outputs and288 nonintegral
off-zero inverse fixtures. Six additional exact leading-form expansions,
180 actual lower-ratio Pell contexts,2800 wrap boundary cases,1280
modular projection pairs and157 divisibility bounds pass. All five local
links and whitespace pass. These source/component fixtures do not
materialize a full compiler Pell zero.

Author receipt generation and a separate fresh default replay passed.
All five local links resolve. The saved finite bound audit comprises360
pretyping cases,3,600 signed-index/wrap cases,320 lower-ratio no-wrap
bounds and125 restored-divisibility bounds.
