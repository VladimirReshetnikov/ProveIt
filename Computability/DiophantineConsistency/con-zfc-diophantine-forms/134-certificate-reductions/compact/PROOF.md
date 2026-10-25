# An existing Pell denominator replaces the artificial scale

## Result, domain, and attribution

The two explicit polynomials `equation78.json` and `equation79.json` have
ten strictly positive integer unknowns. Their live arithmetic costs and
exact total degrees are respectively **78 / 630** and **79 / 468**.
They use the entire fixed indexed BFS943 coefficient tuple of package 133
at ProveIt commit `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`.
The coefficient port names are not quantified unknowns. Their literal
unsigned little-endian bytes and an independent finite reconstruction
from the published 436-character code are included.

The new step is to recover the first Pell index using only a large known
divisor of its error, and only afterwards recover the entire denominator.
It permits removal of the artificial scale `mu=q^2+1`. The carrier uses
the already evaluated square `Y^2`, although `Y` and `q-1` need not be
coprime. No claim of that false coprimality is used.

Pell doubling, the product-square finalizer, both transport weights, the
quotient substitution `Y=q^3*s`, and absorption of its integral quotient
into the padding coordinate have explicit predecessors. This packet
claims the new staged index argument, its completed composition with
those predecessors, and the two literal arithmetic circuits. It claims
neither a global minimum nor historical priority over the literature.

The conclusion is an ordinary theorem formalizable in ZFC, composed with
the identified native/refutation calibration:

    ZFC proves: no strictly positive zero of either polynomial
                if and only if Con(ZFC).

This is not a proof of either consistency or unsolvability. It is not a
new end-to-end Lean, Rocq, or encoded object-language ZFC certificate.

## 1. Complete definitions

The only unknowns are

    J,F,alpha,i,T,w,s,n,eta,zeta in Z_{>0}.

The coherent fixed tuple is `beta,K0,MC,MF`. Its inherited port box is
`beta>=31` odd, `K0>0`, and `0<MC<beta<MF<2beta`. Define

    q=beta*J+1, h=q-1, C=q-F-alpha, X=w*q, Y=q^3*s,
    k=eta+zeta, c=k*Y+eta, A=Y*(X+1)+1,
    Delta=A^2-1, H=4*A-5, D=Y^2, V0=X*D,
    E=1+V0*(V0+1)*k^2,
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    U=i*c^2, a=Delta*U^2*E, F0=1+a, G=E*F0,
    Fsq=1+4*a*F0, Q=Delta*(Fsq-1),
    b=c*(T+alpha)-R, V=Fsq*b-c,
    Kpos=X*(3*c-2*X)+2.

For the 78-operation polynomial put `L=V^2`; for the 79-operation
polynomial put `L=b*V`. In either case set

    M=h*D*H,
    Z=h*D*[H*(n-L*B)+Kpos]-H*[D*B+h*e],
    RG=M^2*G,
    P=Q*(Z^2-RG*V^2)+(RG-Z^2).

The requested single equation is `P=0`. Every intermediate is a polynomial
abbreviation, not an additional unknown. The circuit computes `A-1`
instead of `A`, using `Delta=(A-1)*((A-1)+2)` and `H=4*(A-1)-1`.

For proof notation only, let `delta=Q-1`, `Dy=Q*V^2-1`, `z=Z/M`,
`kappa=Kpos/H`, `rho=e/D`, `t=B/h`, `W=1+h*L`. Then identically

    P=delta*Z^2-M^2*G*Dy,
    z=n+kappa-W*t-rho.                         (1)

No divisibility is assumed in these rational identities.

## 2. Product-square extraction precedes all source semantics

Positive inputs give `q>=32`, `X>=q`, `Y>=q^3`, `k>=2`, `c>=3`,
`A>4`, `Delta>=3`, `U>=c^2`, `E>1`, `a>0`, `Fsq>c+1`, `Q>1`,
and `M>0`. For every integer `b`, `V=Fsq*b-c` is nonzero: if `b=0`
then `V=-c`, and otherwise `|V|>=Fsq-c>1`. Thus `Dy>0`.

The exact identities

    Fsq=(1+2*a)^2,
    Q=4*Delta^2*U^2*G

show that `G` is coprime to both `delta` and `Dy`. If `P=0`, division
by `M^2` gives `delta*z^2=G*Dy`. Every prime dividing `G` therefore has
even valuation in `G`, since a rational square has even valuation.
Consequently `G=g^2` for an integer `g>0`. Since `F0=1 mod E`,
`gcd(E,F0)=1`, and their positive product is square. Hence

    E=tau^2, F0=f0^2, g=tau*f0

with positive integers `tau,f0`. Now `y=|z|/g` is a positive rational
solution of

    Q*V^2-(Q-1)*y^2=1.                        (2)

The adjacent-Pell descent in the retained product-square proof forces
`y` integral. Briefly, for `y=r/m` in lowest terms, `m^2 | Q-1`.
For `v=|V|>1`, one has `v<y<Q*v/(Q-1)`. The norm-preserving map

    v'=(2Q-1)*v-2*(Q-1)*y,
    y'=(2Q-1)*y-2Q*v

has a nonzero integer first coordinate with `|v'|<v` and preserves the
reduced denominator `m` of the second coordinate. Descent reaches
`v=1,y=1`, forcing `m=1`. In particular

    z=epsilon*g*y is an integer, epsilon in {-1,1}.     (3)

Set `f=1+2a` and `I=2U*g`. Then

    f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2 | I,
    V=f^2*[c*(T+alpha)-R]-c.                  (4)

This is the doubled strong pair of the retained construction. Neither
the scale `mu` nor any residue modulo it is needed for root extraction.

## 3. Main folding and transport without the scale

The all-index folding theorem is uniform in the integer Pell base
`A>=3`. Its premises `c<=I`, `c^2|I`, (2), (4), and `V=-c mod f`
therefore hold. It gives `c=psi_A(p)` for an odd integer `p>=1`.
The first norm similarly gives

    k=2*psi_(2V0+1)(n0), n0>=1.

If `n0=1`, then `k=2`, `eta=zeta=1`, and `c=2Y+1` lies strictly
between `psi_A(1)=1` and `psi_A(2)=2A`, impossible. Thus

    k>=8*V0+4, c>kY>=k>8*X*Y^2>=8*q^7.       (5)

This is stronger than the previous scale-based `8q^5` bound. In
particular `c>X`, `Kpos>0`, and `kappa>0`. The unconditional mask bound
`R<q^4+(alpha+2)q^2`, together with (5), proves `b>c` before the sign
of `B` is known. Thus `V>0`. Also

    b-e=c*(T+alpha)-k+1>0, hence rho<b/D.      (6)

For `L=V^2`, the positive identity

    a^2-g^2=E*[Delta*U^2*E*(Delta*U^2-1)-1]>0

gives `g<a`, and then `V>(Fsq-1)b>ab>3g`. Equation (2) gives
`y<3V/2`, so `g*y<L/2`.

For `L=bV`, the unchanged fifth-index argument gives `b>4g`.
Here are its exact hypotheses and bounds. Since `c>=3`, the odd main
index is at least three; thus `c>=4Delta+3`. Therefore `V>4Q`.
Writing `S=Delta*I`, the positive Pell classification of (2) gives
`SV=chi_S(j)` with odd `j`. The values `j=1,3` yield `V=1,4Q-3`,
both excluded; hence `V>=16Q^2-20Q+5>8Q^2`. It follows that

    b>4Delta^2*(Fsq-1)=4Delta^3*I^2>4g.

Thus again `g*y<3bV/8<L/2`.

If the actual integer `B<=-1`, then `Wt<=-L-1/h`. Equations (1),
(3), (6) give

    n=epsilon*g*y-kappa+Wt+rho < L/2-L+b/D < 0.

The last strict inequality holds for both weights because `V>b>1`
and `D=Y^2>2`. This contradicts `n>0`. Consequently `B>=0`, and
its definition with `F>0` forces `C>0`.

The inherited outer mask inequalities now give `3q<R<q^4-2`.
The normalized strong-rank and signed auxiliary-index theorems require
only `c^2|I`, `c>2R`, `c>2p`, and the residues `V=-c mod f` and
`V=-R mod c`. They are supplied by (4), (5), and the usual positive
Pell growth bound. They give `p=R`. In particular `R` is odd; the
unchanged mask parity gives even `q` and odd `J`.

## 4. New staged recovery of the first index

This step replaces the previous coprime artificial-scale argument.
It does not assume that `Y` and `h` are coprime or that `rho` is integral.

Because `z` is integral, clearing only `hH` in (1) gives

    D divides h*H*e.                         (7)

But `Y=q^3*s`, so `q^6|D`; also

    gcd(q,h)=1, H=4Y(X+1)-1=-1 modulo q.

Hence `gcd(q^6,hH)=1`, and (7) implies `q^6|e`.

Let `P0=2XY^2+1`. The universal base-one Pell recurrence gives

    psi_P0(n0)=n0 modulo P0-1,
    k=2n0 modulo 4XY^2.                      (8)

Since `q^6|Y^2`, (8) and `q^6|e` imply

    q^6 divides 2n0-R-1.                     (9)

Furthermore `P0>A`, because
`P0-A=Y*(2XY-X-1)>0`. If `n0>=R`, monotonicity in the index and
base would give `k/2=psi_P0(n0)>=psi_A(R)=c`, contradicting
`c=kY+eta>k`. Thus `1<=n0<R`. Consequently

    |2n0-R-1|<R<q^4<q^6.

Together with (9), this proves `2n0=R+1`. Only now return to the
full congruence (8): it yields `4XY^2|e`, and therefore

    D|e and rho=e/D is an integer.           (10)

This order is essential. The index modulus `q^6` is a known divisor
of an already present polynomial; it is not a new denominator or a
new circuit register. The complete denominator need not be separated
by pairwise coprimality.

## 5. Projection and the inherited native endpoint

Write `R=2r+1`, so `r>=48`. The retained zero-offset ratio lemma is
explicitly uniform in every real `lambda>=1`, with

    A=lambda*Y*(X+1)+1,
    P0=2X*lambda^2*Y^2+1.

Use it at `lambda=1`, not at an unproved limiting value. It gives

    xi < psi_A(2r+1)/psi_P0(r+1)
       < xi*(1+1/[Y(X+1)])^(2r),
    xi=(X+1)^(2r)/X^r.

Since `Y<c/k<Y+1`, the same lower-bound argument gives
`Y>X^r/3` and hence `X^(r+1)<3Y(X+1)<H`.

By (10), the integral carrier gives `H|h*Kpos`. Since `H` is odd
and `Kpos=H*X*c-2*Kquad`, with
`Kquad=X*[X+2(A-2)c]-1`, cancel only the unit two. The universal
Pell projection then gives

    H divides h*(X-2^R)*(2^R*X+1).            (11)

The retained whole-product bound applies: its older multiplier `q^3*h`
was larger, and the same bounds `X>=q>=32`, `r>=48` are present.
The absolute value of the entire product in (11) is below
`X^(r+1)<H`; hence that product is zero, and `X=2^R`. No unit
assumption about a factor of the composite integer `H` is used.

Thus `kappa` is an integer. Now (1) and (10) show `Wt` integral;
since `W=1 mod h`, it follows that `h|B` and `t>=0` is integral.
The condition `q^3|Y` was built in from the start. The retained
fixed-minus auxiliary parity and the ratio/half-binomial rounding
arguments therefore have all their original hypotheses. Reconstruct
their fresh unscaled source at `A_source=Y(X+1)+2`. This does not
identify `A_source` with the present `A`. The whole indexed native
calibration then yields a finite syntactic ZFC refutation.

## 6. Positive completeness

A refutation gives the inherited canonical outer data with
`X=2^R`, `R=3 mod 4`, `r=(R-1)/2>=48`, `q^3|Y`, and integral
`t=B/h>=0`, with the required half-binomial identity. Keep these data
and choose the positive input `s=Y/q^3`. Form the new bases with
`lambda=1`, and set

    c=psi_A(R), k=2psi_P0(r+1), tau=chi_P0(r+1),
    eta=c-kY, zeta=k-eta.

The uniform ratio estimate and the same half-binomial bounds give
`0<eta<k`, so both new inputs are positive. Equation (8) yields
`e=k-R-1` a positive multiple of `4XY^2`; hence `rho>=1`.
The projection identity makes `kappa=Kpos/H` a positive integer.

Choose a positive seed Pell index at a multiple of the finite matrix
period modulo `c^2*tau`. Its pair `(f0,I0)` has `c^2*tau|I0`.
Set `i=I0/(c^2*tau)>0`; then `U=I0/tau`, `F0=f0^2`, and
`G=(tau*f0)^2`. Double the pair to obtain

    f=2f0^2-1, I=2f0*I0=2U*g.

This is exactly (4). The inherited auxiliary-completeness theorem
allows this doubled strong index without any extra parity restriction.
It supplies `T'=T+alpha>alpha`, positive `V,y`, and (2). Therefore
the new input `T=T'-alpha` is strictly positive.

For either specified `L`, set

    n=g*y+Wt+rho-kappa.                       (12)

All terms are integers. Moreover `f0>(A-1)I0>Xc>kappa`, so
`g=tau*f0>kappa`. Since `y>=1`, `Wt>=0`, and `rho>=1`, (12)
gives `n>0`. Its exact carrier is `z=g*y`, proving `P=0`.
Every quantified coordinate is positive. This is a fresh witness
construction, not an unjustified positive inverse shear.

## 7. Exact degree and arithmetic counts

Every live binary addition, subtraction, and multiplication is counted,
including fixed scalar products and squares. No exponentiation gate,
division, or root occurs. The circuits have 78 and 79 such rows.
Relative to package 133 the quotient normalization removes three
operations. Removing the scale and reusing `Y^2` removes three more.

The relevant exact register degrees are

    q 1, X 2, Y 4, c 5, A 6, Delta 12, E 22, U 11,
    a 56, Fsq 112, Q 124, G 78, b 6, V 118, M 15, B 2.

For `L=V^2`, `deg Z=253` and `QZ^2` is the unique top summand,
of degree 630. For `L=bV`, `deg Z=141`; now `-Q*M^2*G*V^2`
is the unique top summand, of degree 468. These are global degree
arguments, not degrees guessed from numerical samples.

Put `q0=beta*J`, `k0=eta+zeta`, `t0=T+alpha`. The entire leading
homogeneous components are respectively

    2^14*q0^382*w^46*s^112*i^20*k0^64*t0^4*(q0-F-alpha)^2,
    -2^10*q0^288*w^34*s^84*i^14*k0^46*t0^2.

They are nonzero for the actual positive fixed `beta`. The first has
coefficient `2^14*beta^382` at
`J^382*w^46*s^112*i^20*eta^64*T^4*F^2`; the second has coefficient
`-2^10*beta^288` at `J^288*w^34*s^84*i^14*eta^46*T^2`.
The checker propagates the complete exact leading polynomials through
all actual DAG rows and compares them with these formulas.

## 8. Proof and artifact boundary

`verify.py` verifies exact free-polynomial cut identities, every literal
circuit's topology and liveness, every leading form and claimed count,
the coefficient bytes and their whole-tuple binding, and deliberately
corrupted negative controls. `rebuild_coefficients.py` independently
reconstructs all four fixed numerals from the finite published code.
These checks do not enumerate all possible zeros. The unbounded
argument is the ordinary proof above together with the explicitly
retained universal Pell and native/refutation theorems.

`proof_sources/product_square.md` supplies the predecessor's doubled
root and transport arguments; `uniform_ratio.md` states and proves the
ratio estimate for every `lambda>=1`; `scaled_native.md` identifies the
universal folding, rank, projection, and fresh native-source interfaces;
`indexed_native.md` pins the actual indexed coefficient specialization.
The supplied `universal_pell.tex` additionally contains the full ordinary
source-61 statements and proofs of the folding, rank, parity and auxiliary
lemmas. The source ledger records each immutable repository file used here.
It is a mathematical dependency statement, not a claim that this packet
rebuilds every transitive proof-assistant dependency.
