# Smaller carrier denominators for compact consistency equations

## 1. Statement, attribution, and domain

The three literal circuits `equation77.json`, `equation78.json`, and
`equation79.json` define ordinary polynomials with fixed integer coefficients
in ten independent strictly positive integer variables. The ordinary theorem
proved here, together with the retained native/refutation calibration, is

    ZFC proves: [there is no positive zero of P] iff Con(ZFC).

Their operation/degree pairs are respectively **77/626**, **78/464**, and
**79/460**. An operation means a live binary addition, subtraction, or
multiplication, including a square and a fixed scalar product. This is a
measured representation cost, not a proof of globally minimal complexity.

The immediate predecessors are the 78/630 and 79/468 equations in
`parent/`. The new argument weakens their carrier denominator from `Y^2`
to either `XY` or `q^4`. A divisor of size `q^4` already identifies the first
Pell index. The identified index then supplies the full divisibility needed
by the carrier. The `XY` choice also shares a multiplication between both
Pell bases.

Product-square extraction, Pell doubling, all-index folding, sign transport,
the native mask, the quotient substitution `Y=q^3*s`, and staged recovery
of a denominator after its index are inherited and explicitly attributed.
This packet claims the smaller denominator lemma, its proved application,
and the checked literal circuits. It retains K215/native ancestry. It does
not claim a newly formalized end-to-end Lean/Rocq theorem, a proof of ZFC's
consistency, or historical priority over all literature.

## 2. Complete polynomial definitions

The only unknowns are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

The four integers `beta,K0,MC,MF` are the complete, fixed directly indexed
BFS943 coefficient tuple of the predecessor. Their literal unsigned
little-endian bytes are in `coefficients/`; `rebuild_coefficients.py`
constructs all four from the supplied 436-character finite code. Their raw
hashes and bit lengths occur in every equation file. In particular they are
not further quantified parameters. The inherited port inequalities are

    beta>=31 odd, K0>0, 0<MC<beta<MF<2beta.

Every symbol below is a polynomial abbreviation:

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, Y=q^3*s,
    k=eta+zeta, c=k*Y+eta, A=Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, V0=X*Y^2,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fstar=1+4*a*F0, Q=Delta*(Fstar-1),
    b=c*(T+alpha)-R, V=Fstar*b-c,
    Kpos=X*(3*c-2*X)+2.

Choose one of the following three pairs:

| Equation | D | L |
| --- | --- | --- |
| 77/626 | XY | V^2 |
| 78/464 | XY | bV |
| 79/460 | q^4 | bV |

For that pair define

    M=h*D*H,
    Z=h*D*[H*(n-L*B)+Kpos]-H*[D*B+h*e],
    RG=M^2*G,
    P=Q*(Z^2-RG*V^2)+(RG-Z^2).

The requested single equation is `P=0`. No division, square-root function,
variable exponent, or auxiliary condition occurs in it. The actual circuits
evaluate `A-1` and use `Delta=(A-1)*((A-1)+2)` and `H=4*(A-1)-1`.

## 3. A general admissible-denominator lemma

The proof works for any specified integer polynomial `D=D(q,X,Y)` that,
on all the positive inputs under consideration, satisfies

    D>2, q^4|D, and D|4XY^2.                 (D)

Requiring `D` to depend only on the outer variables makes the completeness
construction independent of the final padding coordinate `n`. Both actual
choices satisfy (D). For `D=XY`, `XY=q^4*w*s` and `4XY^2/D=4Y`.
For `D=q^4`, `4XY^2/D=4*w*q^3*s^2`. Both quotients are positive integers.

For proof notation only put

    delta=Q-1, Dy=Q*V^2-1, z=Z/M,
    kappa=Kpos/H, rho=e/D, t=B/h, W=1+hL.

The following rational identities hold without any divisibility premise:

    P=delta*Z^2-M^2*G*Dy,
    z=n+kappa-W*t-rho.                       (1)

We prove that a positive zero of the modified polynomial recovers the same
outer native witnesses as the parent, and that a refutation gives fresh
positive witnesses for every modified polynomial.

## 4. Root extraction and the early sign argument

All quantities outside `D,M,Z,RG,P` have exactly their predecessor values.
Positive inputs give `q>=32`, `X>=q`, `Y>=q^3`, `k>=2`, `c>=3`, `A>4`,
`U>=c^2`, `E>1`, `Fstar>c+1`, `Q>1`, and `M>0`. For every integer `b`,
`V=Fstar*b-c` is nonzero, so `Dy>0`.

The exact identities

    Fstar=(1+2a)^2,
    Q=4*Delta^2*U^2*G

show that `G` is coprime to both `Q-1` and `QV^2-1`. If `P=0`, then
`delta*z^2=G*Dy`. At each prime dividing `G`, the other two factors are
units, so the prime valuation of `G` is even. Hence `G=g^2`, with `g>0`
integral. Because `F0=1 mod E`, the positive coprime factors split:

    E=tau^2, F0=f0^2, g=tau*f0.

The positive rational `y=|z|/g` satisfies

    QV^2-(Q-1)y^2=1.                         (2)

The adjacent-Pell descent proved in `parent/PROOF.md`, section 2, forces
`y` to be an integer. Thus `z=epsilon*g*y` is integral, with
`epsilon in {-1,1}`. Defining `f=1+2a` and `I=2U*g` gives

    f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2|I,
    V=f^2*[c*(T+alpha)-R]-c.                 (3)

The retained universal folding theorem now gives `c=psi_A(p)` for an odd
positive index `p`. The first norm gives

    k=2*psi_(2XY^2+1)(n0), n0>=1.

Its first index is impossible because it would give `k=2` and
`c=2Y+1` strictly between the first two positive main ordinates. Therefore

    k>=8XY^2+4, c>kY>=k>8XY^2>=8q^7.         (4)

The same source estimates give `Kpos>0`, `b>c`, `V>0`, and

    b-e=c*(T+alpha)-k+1>0, so rho<b/D.        (5)

Their proofs depend on the unchanged bases and masks, not on the choice of
`D`. The predecessor transport estimates give `g*y<L/2` for both choices
of `L`. For `L=V^2` this follows from `g<a`, `V>3g`, and `y<3V/2`.
For `L=bV`, the fifth-index estimate gives `b>4g`, again combined with
`y<3V/2`. The complete proofs and their hypotheses are retained in
`parent/PROOF.md`, section 3, and `proof_sources/product_square.md`.

If the actual integer `B<=-1`, then `Wt<=-L-1/h`. Equations (1) and (5)
would imply

    n=epsilon*g*y-kappa+Wt+rho < L/2-L+b/D < 0.

The last inequality uses only `D>2` and `V>b>1`. This contradicts positive
`n`. Consequently `B>=0`, whence `C>0`. The unchanged mask bounds give

    3q<R<q^4-2.

The unchanged normalized rank and auxiliary-index theorems apply to (3)
and (4): `c^2|I`, `c>2R`, `c>2p`, `V=-c mod f`, and `V=-R mod c`.
They identify the main index as `p=R`. In particular `R` is positive and
odd. Up to this point no integrality of `rho` was assumed.

## 5. The smaller denominator is enough

Since `z` is integral, clearing `hH` from (1) gives

    D | hH e.

By (D), `q^4|D`. Moreover `h=q-1` and
`H=4Y(X+1)-1=-1 mod q`. Thus `gcd(q^4,hH)=1`, and

    q^4 | e.                                (6)

Set `P0=2XY^2+1`. The base-one Pell recurrence gives

    psi_P0(n0)=n0 mod(P0-1),
    k=2n0 mod 4XY^2.                         (7)

The modulus in (7) is divisible by `q^4`. Combining (6) and (7) gives

    q^4 | (2n0-R-1).                         (8)

Also `P0>A`, since `P0-A=Y*(2XY-X-1)>0`. If `n0>=R`, monotonicity
in the base and index would imply `k/2>=psi_A(R)=c`, contrary to `c>k`.
Therefore `1<=n0<R`, and

    |2n0-R-1|<R<q^4.

The divisible integer in (8) must be zero. Hence `n0=(R+1)/2`. Returning
to the **full** congruence (7), we obtain `4XY^2|e`. Condition (D) now
implies `D|e`, so `rho=e/D` is integral.

This is the new general lemma. Soundness cancels only the coprime factor
`hH` modulo the known divisor `q^4`; it does not assert that the whole
denominator `D` is coprime to either `h` or `H`.

## 6. Projection and native source recovery

Write `R=2r+1`; the same mask bounds give `r>=48`. The retained zero-offset
ratio lemma at scale one uses exactly the unchanged pair of bases
`A=Y(X+1)+1` and `P0=2XY^2+1`. It gives

    Y>X^r/3, hence X^(r+1)<3Y(X+1)<H.

Because `rho` is integral, (1) gives `H|h*Kpos`. The identity

    Kpos=H*X*c-2*Kquad,
    Kquad=X*[X+2(A-2)c]-1

and odd `H` allow cancellation of two. The inherited universal projection
then gives

    H | h*(X-2^R)*(2^R*X+1).

The retained whole-product estimate bounds its absolute value strictly
below `X^(r+1)<H`, so `X=2^R`. No cancellation of an arbitrary factor
modulo a composite integer occurs. The same projection establishes that
`kappa` is integral. Equation (1) now implies `h|WB`; since `W=1 mod h`,
one gets `h|B` and integral `t=B/h>=0`.

Literal `q^3|Y`, the fixed-minus auxiliary parity theorem, and the unchanged
ratio/half-binomial rounding recover the fresh source at base `Y(X+1)+2`.
The indexed native calibration of the whole fixed coefficient tuple then
yields a finite syntactic ZFC refutation. These inherited steps, including
the distinction between the current base and the fresh source base, are
given in `parent/PROOF.md`, section 5, and the named proof sources.

## 7. Fresh positive witnesses from a refutation

A refutation supplies the inherited canonical outer data, with `X=2^R`,
`R=3 mod 4`, `r=(R-1)/2>=48`, `q^3|Y`, and integral `t=B/h>=0`.
Keep those data, set the positive coordinate `s=Y/q^3`, and form

    c=psi_A(R), k=2psi_P0(r+1), tau=chi_P0(r+1),
    eta=c-kY, zeta=k-eta.

The retained uniform ratio and half-binomial arguments give `0<eta<k`,
so both new coordinates are positive. Congruence (7) gives positive `e`
divisible by `4XY^2`. By (D), `rho=e/D` is a positive integer. Projection
gives a positive integral `kappa`.

The predecessor's finite-period construction supplies a seed Pell pair
`(f0,I0)` with `c^2*tau|I0`. Take `i=I0/(c^2*tau)>0`. The doubled
pair is exactly (3), and the auxiliary reconstruction supplies
`T'=T+alpha>alpha` and positive `V,y` satisfying (2). Thus `T>0`.

Finally choose

    n=g*y+(1+hL)*t+rho-kappa.

All its terms are integers. The retained estimate
`f0>(A-1)I0>Xc>kappa` gives `g>kappa`, while `y>=1`, `t>=0`, and
`rho>=1`. Consequently `n>0`. The carrier is exactly `z=g*y`, so `P=0`.
Since `D` depends only on the already chosen outer variables, this final
choice introduces no circularity. All ten quantified inputs are positive.

## 8. Exact arithmetic costs and degrees

For `D=XY`, use the three gates

    D=X*Y; Aminus1=D+Y; V0=D*Y.

They replace the four parent gates `X+1`, `Y*(X+1)`, `Y^2`, and
`X*Y^2`. This saves one multiplication. For `D=q^4`, retain the same
shared product under the name `XY` and add `D=q2*q2`, where `q2=q*q`
is already live. This costs one more multiplication than the `XY` carrier.

| Equation | Multiplications | Additions | Subtractions | Total | Degree |
| --- | ---: | ---: | ---: | ---: | ---: |
| D=XY, L=V^2 | 45 | 18 | 14 | 77 | 626 |
| D=XY, L=bV | 46 | 18 | 14 | 78 | 464 |
| D=q^4, L=bV | 47 | 18 | 14 | 79 | 460 |

The unchanged register degrees are

    q:1, X:2, Y:4, c:5, A:6, Delta:12, E:22, U:11,
    a:56, Fstar:112, Q:124, G:78, b:6, V:118, B:2.

For the first equation, `deg D=6`, `deg M=13`, `deg Z=251`; the term
`QZ^2` alone supplies degree 626. For the second, `deg M=13` and
`deg Z=139`; `-QM^2GV^2` alone supplies degree 464. For the third,
`deg D=4`, `deg M=11`, `deg Z=137`; the same unique top summand has
degree 460. These are global degree proofs, not degrees inferred from
numeric sampling.

With `q0=beta*J`, `k0=eta+zeta`, and `t0=T+alpha`, the entire leading
homogeneous forms are respectively

    2^14*q0^378*w^48*s^110*i^20*k0^64*t0^4*(q0-F-alpha)^2,
    -2^10*q0^284*w^36*s^82*i^14*k0^46*t0^2,
    -2^10*q0^284*w^34*s^80*i^14*k0^46*t0^2.

They are nonzero for the actual positive fixed `beta`. The checker expands
and compares every coefficient in these leading forms, along with exact
free-polynomial cut identities covering every gate of the full circuits.

## 9. Verification and proof boundary

The frozen immediate parent, every retained proof dependency, its notices,
and the unchanged fixed-numeral recipe have explicit hashes. The new
builder imports no parent program; it rewrites four explicitly matched
parent rows. The checker imports no builder and checks every register
against independently stated polynomial definitions. It is adapted from
the frozen predecessor checker, which remains included and credited.

The exact algebra checks, reconstruction of the four actual coefficients,
leading-form checks, modular transcription controls, and rejected mutations
authenticate the finite artifacts. They do not prove an unbounded theorem
by sampling. The equivalence with finite refutation is the ordinary
argument above composed with the explicit inherited arithmetic and native
calibration. Negating the two existential directions yields the theorem in
section 1 and is formalizable in ZFC.
