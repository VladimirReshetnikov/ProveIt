# Independent review of the 2048-scale polynomial majorant

## Decision and scope

The proposed 2048-scale adapter is sound with the corrected padding

    Bgap = 2*P*(P+R)+1.

It preserves the full existential interface of the inherited nine-coordinate ratio construction. Its exact total degree is `820*t+12*W+208`, with diagonal leading coefficient `3*2^1494`, under the retained source degree and leading-form facts. The source has `t>2`.

The earlier padding `P*(P+R)+1` also gives a valid semantic adapter, but its two highest-degree finalizer terms cancel. It must not be assigned the degree or coefficient stated above. The factor 2 in the corrected padding resolves this cancellation by an exact homogeneous-form calculation.

The new polynomial uses only the already present witnesses, integer literals, addition, subtraction, and multiplication. The rational expressions and square roots below are explanatory proof devices, not circuit operations. The review does not convert the inherited ordinary mathematical compiler proof into a new Lean formalization; that boundary is recorded in `FOUNDATION_AUDIT.md`.

## 1. Definitions and source domain

Retain the inherited ratio registers

    U=N^2*w, Y=N^2*s, M=R*Y,
    P=2*M^2*U, K=R+1+h*(P-1), A=M*(U+1),
    C=2*R+1+b*w+phi, J=4*A-5,
    D=(A^2-1)*C^2+1, E=i*J*D*C^2,
    F=(A^2-1)*E^2+1, G=A+F*(C*D+1-A),
    H=2*R+1+j*C, I=(G^2-1)*H^2+1,
    a0=(P^2-1)*K^2+1, a1=D*F*I.

The domain is `R,N>=8`, `b,w,s,h,i,j>=1`, and `phi>=0`. These imply `U,Y>=64`, `M>=512`, and `A>=33280`. In particular all inequalities below requiring only `A>=3` apply uniformly before assuming any source or Pell equation.

Define the following polynomial registers:

    e=i*J*C,
    L=C*D+1-A,
    Nstar=2*G+L,
    N1=2*e^2*D*(D-1)*L+3*C,
    N2=2*e^2*(D-1)*L,
    N3=2*e^2*(L-C),
    N4=2*e^2*C,
    correction=256*i*(e^2+2)+2048,
    T=e*((1024*D^2-512*D-128)*Nstar
          -64*N1-40*N2-28*N3-21*N4)+correction,
    Bstar=P*(P+R),
    Bgap=2*Bstar+1,
    V=T*H+Bgap,
    lambda=2048,
    b1=lambda^2*a1.

The names `N1,...,N4` in this review are local majorant registers and must not be confused with the older source-bound registers using similar names.

## 2. Proof of the uniform radical majorant

The exact relations `E=C*D*e` and `D-1=(A^2-1)*C^2` give

    F=(D-1)*D^2*e^2+1.

Put `X=e^2*D^3*(D-1)`. Then

    D*F=X+D,
    G=(X/D)*L+C*D+1.

All quantities in these rational proof expressions are positive. Indeed `D>=A^2>=9`, and `L=C*D+1-A>0` for `A>=3,C>=1`.

### A finite approximation identity

Set

    tn=1024*D^6-512*D^5-128*D^4-64*D^3-40*D^2-28*D-21,
    dn=33792*D^5+10560*D^4+4928*D^3+2464*D^2+1176*D+441.

Direct polynomial multiplication gives

    tn^2-1024^2*D^11*(D-1)=dn.

For `D>=1`, `tn>0`: the sum 512+128+64+40+28+21 is 793, below 1024, and each negative lower power is at most the corresponding multiple of `D^6`. The right side `dn` is positive. Consequently, for `D>1`,

    tn/D^4 > 1024*D^2*sqrt(1-1/D).

This finite exact identity is the entire approximation argument. No infinite-series convergence claim is needed.

### Exact quotient remainders

The four polynomial registers satisfy

    Nstar=D*N1+r1,       r1=3-A,
    Nstar=D^2*N2+r2,     r2=3*C*D+3-A,
    Nstar=D^3*N3+r3,     r3=2*e^2*(A-1)*D^2+r2,
    Nstar=D^4*N4+r4,     r4=2*e^2*(1-A-C)*D^3
                              +2*e^2*(A-1)*D^2+r2.

In particular `r2,r3>0`. The polynomial part of `T` equals

    e*(tn/D^4)*Nstar
      +e*(64*r1/D+40*r2/D^2+28*r3/D^3+21*r4/D^4).

To bound its possible negative remainder, use

    e*A/D < (9/2)*i,
    e*C/D < (3/2)*i,
    e*(A+C-1)/D < 6*i.

For the first inequality, `e*A/D < 4*i*A^2/((A^2-1)*C) <= (9/2)*i` for `A>=3,C>=1`. For the second, `e*C/D < 4*i*A/(A^2-1) <= (3/2)*i`. The strict inequalities come from `4A-5<4A` and the positive added constant in `D`.

Dropping only positive terms bounds the negative part of the remainder by

    64*e*A/D + 42*e^3*(A+C-1)/D + 21*e*A/D^4
      < 252*i*e^2 + (765/2)*i.

The last term is a harmless overestimate; retaining it makes the quoted bound directly compatible with the construction note. The correction `256*i*(e^2+2)+2048` exceeds this bound plus 2048, since their difference is `4*i*e^2+(259/2)*i>0`.

### Concavity bound

For positive `X,D`, squaring positive sides proves the strict inequality

    sqrt(X+D)<sqrt(X)+D/(2*sqrt(X)).

Multiply by `lambda*G` and use `G=(X/D)*L+C*D+1`. The result is exactly

    lambda*sqrt(D*F)*G
      <1024*e*D^2*sqrt(1-1/D)*Nstar+lambda*v0,
    v0=(C*D+1)/(2*e*D*sqrt(1-1/D)).

Here `v0<1` uniformly. To see this, `e>=7C`, `D>=9`, and `sqrt(D*(D-1))>D-1`; hence

    v0 < (C*D+1)/(e*(D-1))
       <=(D+1)/(7*(D-1))<1.

Combining the finite approximation identity, the exact quotient remainders, and the correction bound gives the strict global inequality

    T > lambda*sqrt(D*F)*G > 0.

There is no asymptotic restriction on the witnesses. In particular `i`, `j`, and all the source witnesses may be arbitrarily large.

Since `I<=G^2*H^2` when `H>=1`, this proves

    V-sqrt(b1)>Bgap=2*Bstar+1>Bstar.

## 3. The independent lower separation bound

The upper gap alone would not exclude zero signed sums. The inherited source gives the necessary independent lower separation as follows.

The exact identity `A^2-2P=M^2*(U-1)^2>0`, together with `C>1`, gives `D>A^2>2P`. Also `E>D`, so

    F>(2P-1)*(2P)^2>2P^2.

The definition `P=2*(R*Y)^2*U` gives `R<P`. Thus `Bstar<2P^2`. Since `L>1`, `G>F>Bstar`. Finally, `I>=G^2` for `H>=1`, and `D*F>1`, so

    sqrt(a1)>G>Bstar.

Meanwhile `K>1`, so `sqrt(a0)<P*K`; and

    h*(P+R)-K=(h-1)*(R+1)>=0.

Therefore

    0<sqrt(a0)<h*Bstar<h*sqrt(b1).

This holds throughout the full source domain, independently of the zero-set equations.

## 4. Exact finalizer equivalence

Retain the ratio bridge's integer polynomials

    Q=3*b*w*C-2*((b*w)^2-1),
    u=J*F,
    v=Q*F+J*(H-C),
    Mdiv=Q+H,
    m=K^2*Gcap-4*(C-K*Y)^2*Gcap-8*g*K^2.

The inherited universal bounds are `u>0` and `0<v/u<Mdiv-1`. The margin `m` is a computed integer polynomial, not a new variable and not an adjustable witness.

With the existing final coordinate `n>=0`, define

    Omega=u*m,
    Theta=u*(n+Mdiv)+v-Omega*(2*Mdiv+h*V),
    Final=(Theta^2-Omega^2*(a0+h^2*b1))^2
          -4*Omega^4*h^2*a0*b1.

Then

    exists n>=0: Final=0
        iff a0 and a1 are integer squares, u divides v, and m>0.

To prove the forward direction, `m=0` would give `Final=(u*(n+Mdiv)+v)^4>0`, so `Omega!=0`. Factorization over the real numbers gives

    Theta/Omega = r0+h*r1,

where `r0` and `r1` are signed square roots of `a0,b1`. This rational sum is nonzero by the lower separation bound. If `q=r0+h*r1` is nonzero rational, then

    r0=(q^2+a0-h^2*b1)/(2*q)

is rational, and `r1` is rational too. Rational square roots of integers are integers. Since `lambda` is an integer, the square condition for `b1=lambda^2*a1` is equivalent to the integer-square condition for `a1`: dividing an integer root by `lambda` gives a rational square root of the integer `a1`, hence an integer.

The integer

    Z=2*Mdiv+h*V+r0+h*r1

satisfies `Z>=2*Mdiv+h+1`. For example, the strict integer bounds `r0>=-h*Bstar+1` and `r1>=-V+Bstar+1` already suffice; the corrected padding gives an even stronger margin. The defining equality rearranges to

    n+Mdiv+v/u=m*Z.

The left side and `Z` are positive, so `m>0`. Its right side is an integer, so `u|v`.

For the converse, use any signed integer roots and keep the actual positive computed margin `m`. Put `k=v/u` and `n=m*Z-Mdiv-k`. Since `0<k<Mdiv-1` and `Z>=2*Mdiv+h+1`, this is a nonnegative integer. Substitution gives `Final=0`. Thus no extra variable, hidden divisibility assumption, or sign hypothesis has been introduced.

## 5. Division-free degree certificate

Define the polynomial

    Rnum=e*(64*r1*D^3+40*r2*D^2+28*r3*D+21*r4)
         +correction*D^4.

Then `D^4*T=e*tn*Nstar+Rnum`, and the exact ring identity is

    D^8*(T^2-lambda^2*D*F*G^2)
      =e^2*dn*Nstar^2
       +1024^2*D^8*(X*L^2-4*D*G*(C*D+1))
       +2*e*tn*Nstar*Rnum+Rnum^2.

Also

    V^2-b1
      =H^2*(T^2-lambda^2*D*F*G^2)
       +lambda^2*D*F*(H^2-1)+2*T*H*Bgap+Bgap^2.

The companion independent verifier expands these identities in the free polynomial ring `Z[A,C,D,e,i,H,P,R]`. It does not import the construction or another verifier. Its output also checks exact weighted degrees for every monomial, for all `t>=3`, and works under Python `-O`.

Use the inherited source degree and diagonal leading-coefficient data:

| Register | Degree | Leading coefficient |
| --- | --- | --- |
| A | 7t+2 | 2^12 |
| C | 3t | 2^5 |
| D | 20t+4 | 2^34 |
| e | 10t+3 | 2^19 |
| H | 3t+1 | 2^5 |
| P | 12t+3 | 2^21 |
| R | 3t | 2^4 |
| Omega | 115t+3W+31 | -2^211 |

The correction term uniquely supplies the leader of `Rnum`, degree `100t+23` and coefficient `2^182`. The four summands in the multiplied defect identity have degree bounds `326t+70`, `306t+62`, `333t+72`, and `200t+46`. The cross term uniquely dominates. As `D` is nonzero, subtraction of its eighth-power degree gives

    deg(T^2-lambda^2*D*F*G^2)=173t+40,
    lc(T^2-lambda^2*D*F*G^2)=2^324.

Moreover `T` has degree `153t+33`, coefficient `2^277`; thus `T*H` has degree `156t+34`, coefficient `2^282`.

In the second defect identity, `2*T*H*Bgap` uniquely dominates when `t>2`: its degree is `180t+40`, whereas the first summand has degree `179t+42`. Because the leading part of `Bgap` is `2P^2`,

    deg(V^2-b1)=180t+40,
    lc(V^2-b1)=2^326.

## 6. Final noncancellation, including homogeneous forms

Let `E0=u*(n+Mdiv)+v-2*Omega*Mdiv`. Resolve the inner expression as

    Theta^2-Omega^2*(a0+h^2*b1)
      =E0^2-2*E0*Omega*h*V
       +Omega^2*h^2*(V^2-b1)-Omega^2*a0.

The four term degrees are, respectively,

    236t+6W+66,
    389t+6W+99,
    410t+6W+104,
    278t+6W+76.

The third term uniquely dominates. Its square and the final subtracted norm term both have degree `820t+12W+208`, so their leading forms must be compared.

Use subscript 0 for a leading homogeneous form, rather than just a diagonal coefficient. The definitions give

    (a0)_0=h^2*(P_0)^4,
    (b1)_0=((T*H)_0)^2,
    (V^2-b1)_0=4*(T*H)_0*(P_0)^2.

Consequently the inner square contributes

    16*(Omega_0)^4*h^4*(P_0)^4*((T*H)_0)^2,

whereas the subtracted norm term contributes four times the same common form. Their difference is twelve times a nonzero common form, so the highest-degree terms cannot cancel. On the diagonal this is

    2^1496-2^1494=3*2^1494.

Thus the actual final polynomial has exact total degree

    820*t+12*W+208,

with diagonal leading coefficient `3*2^1494`. This proof is stronger than a bare syntactic degree bound and does not depend on numeric sampling.

## 7. Verification record and remaining inherited conditions

`check_majorant2048_independent.py` passes under `python3 -O`. Its receipt is `MAJORANT2048_INDEPENDENT.json`. The exact expanded defects have 179 and 283 monomials in the independent register ring. The script verifies the finite approximation identity, all four remainders, the division-free defect, the `V` defect, and the weighted-degree leaders. The inequalities and existential equivalence are proved above.

The remaining dependencies are precisely the inherited ratio bridge, the source/packing zero-set bridge, the concrete coefficient binding, and the mathematical simulation-to-consistency theorem. They are not enlarged by this adapter. The domain remains nine nonnegative coordinates after the stated successor substitutions, or nine positive coordinates after the corresponding shifts; this audit does not authorize an unguarded extension to arbitrary integer coordinates.

No defect remains in this corrected adapter. It is suitable for inclusion as the final nine-coordinate refinement, with the prior V8/T16 adapters retained only as optional independent fallback artifacts.
