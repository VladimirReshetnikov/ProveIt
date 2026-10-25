# Recover the main square before the first Pell square

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

## Result and comparison boundary

The literal polynomial `equation78_degree454.json` has ten strictly positive
integer unknowns, 78 live binary arithmetic operations, and exact total degree
454. It retains the entire four-coefficient tuple of the incoming
`ConZFC_Centered_Residues_2026-10-25` package at ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. The immediate parent has 76
operations and degree 464; that arrival also has a 77-operation degree-460
equation. Our change trades two or one extra operations for ten or six fewer
degrees. It does not improve the smallest known variable count or the
smallest operation count, and no global optimum or literature-wide priority
is claimed.

The new mechanism avoids the parent's polynomial doubling of a strong Pell
pair. A product-square test first recovers the square of `E*Dm` and a strong
Pell trace. Main-index folding then proves `Dm` square, only after which `E`
is recovered as a square. Assuming `E` square before folding would be circular.

The result is an ordinary theorem formalizable in ZFC, composed with the
named native/refutation calibration in the retained parent proof:

    ZFC proves: no strictly positive integer zero iff Con(ZFC).

It is neither a proof of consistency nor a new end-to-end Lean/Rocq or
encoded object-language ZFC derivation. Finite checks authenticate the
literal equation and its stated cost and degree; they do not replace the
unbounded proof below and its explicit inherited dependencies.

## 1. Complete polynomial

The only independent variables are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The four fixed integer ports are `beta,K0,MC,MF`. Their whole literal
coefficient payloads are supplied, unchanged, under `coefficients/`.
They satisfy `beta>=31` odd, `K0>0`, `0<MC<beta<MF<2beta`. All symbols
below are polynomial abbreviations, not extra quantified variables:

    h=beta*J, q=h+1, C=q-F-alpha,
    X=w*q, Y=q^3*s, k=eta+zeta, c=k*Y+eta,
    A=Y*(X+1)+1, Delta=A^2-1, H=4*A-5,
    ell=(X*Y)*(k*Y), E=1+ell*(ell+k),
    R=[h*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J,
    e=k-R-1, B=(K0+w)*C-F,
    Dm=1+Delta*c^2, U=i*A*c^2, S=E*Dm,
    a=Delta*U^2*S, F2=1+a, Q=Delta*a, G=S*F2,
    b=c*T-R, V=F2*b-c, L=b*V,
    K=X*(3*c-2*X)+2,
    M=h*(X*Y)*H,
    Z=h*(X*Y)*[H*(n-L*B)+K]-H*[(X*Y)*B+h*e],
    P=Q*[Z^2-M^2*G*V^2]+[M^2*G-Z^2].

The single equation is `P=0` on the stated strictly positive domain.
`F2` is a polynomial name; its being a square is a conclusion, not a
hidden operation. The literal DAG uses only addition, subtraction and
multiplication, including repeated multiplication for the small powers.

For proof notation only, put

    delta=Q-1, Caux=Q*V^2-1, z=Z/M,
    D=XY, kappa=K/H, rho=e/D, t=B/h, W=1+hL.

Two exact identities are

    P=delta*Z^2-M^2*G*Caux,
    z=n+kappa-W*t-rho.                              (1)

No integrality of the fractions in (1) is assumed at the start.

## 2. Three elementary coprimality statements

Every positive assignment gives `q>=32`, `X>=q`, `Y>=q^3`, `k>=2`,
`c>=3`, `A>4`, `Delta>=3`, `Dm>0`, `S>1`, `U>=A*c^2`, `F2>2c`,
`Q>F2>1`, and `M>0`. Also `Q=Delta^2*U^2*S>c^2` and
`F2=1+Delta*U^2*S>S`, so `F2>sqrt(S*F2)=g` once that root is recovered.
If `b=0` then `V=-c`; if `b` is a nonzero integer,
then `|V|>=F2-c>1`. Thus `V` is never zero, and `Caux>0`.

First, `F2=1+Delta*U^2*S` and `Q=Delta^2*U^2*S` imply

    gcd(S,F2)=1,
    gcd(S,delta)=gcd(S,Caux)=1.                     (2)

Second, `delta=Delta*F2-A^2`. Since `A|U`, one has `F2=1 mod A`, so

    gcd(F2,delta)=gcd(F2,A^2)=1.                    (3)

Third, reduction modulo `F2` gives `Q=-Delta` and `V=-c`, hence

    Caux=-Delta*c^2-1=-Dm mod F2.

But `Dm|S` and `F2=1 mod Dm`, so

    gcd(F2,Caux)=1.                                (4)

Equations (2)--(4) prove `gcd(G,delta*Caux)=1`. They do not assert
`gcd(E,Dm)=1`; that assertion is unnecessary and in general false.

## 3. Recover two roots, then fold the main index

At a positive zero, (1) gives `delta*z^2=G*Caux`. For every prime dividing
`G`, its valuations in `delta` and `Caux` vanish by (2)--(4). A rational
square has even valuations. Therefore `G=g^2` for an integer `g>0`.
The coprime positive factors `S,F2` of `G` are individually squares:

    S=sigma^2, F2=f^2, g=sigma*f, sigma,f>0.         (5)

At this stage neither `E` nor `Dm` has been declared square. Put
`y=|z|/g`; it is a positive rational solution of

    Q*V^2-(Q-1)*y^2=1.                             (6)

The adjacent-coefficient descent forces `y` integral. For clarity, writing
`y=r/m` in lowest terms yields `m^2 | Q-1`. If `v=|V|>1`, then
`v<y<Qv/(Q-1)`. The norm-preserving transformation

    v'=(2Q-1)*v-2*(Q-1)*y,
    y'=(2Q-1)*y-2Q*v

has a nonzero integer first coordinate and `|v'|<v`. Its second coordinate
has the same reduced denominator `m`, since `2Q-1=1 mod m`; its first
coordinate is integral because `m^2|Q-1`. After reflecting signs, descent
terminates at `|v|=1`, where `|y|=1`. Thus `m=1`, and

    z=epsilon*g*y is an integer, epsilon in {1,-1}. (7)

Define `I=U*sigma`. Now (5) gives the ordinary strong Pell pair

    f^2-Delta*I^2=1, Q=(Delta*I)^2, c^2|I.          (8)

All hypotheses of the parent's all-index folding lemma hold: `A>=3`,
`0<c<=I`, the integral adjacent norm (6), and `V=-c mod f`. For completeness,
write `f=chi_A(m)`, `I=psi_A(m)`, and `Saux=Delta*I`. Classifying (6)
gives `Saux*|V|=chi_Saux(j)`, `y=psi_Saux(j)`, where `j` is odd because
even traces are units modulo `Saux`. The odd quotient identity

    chi_t(2r+1)/t = Q_r(t^2),
    Q_r(1-A^2)=(-1)^r*psi_A(2r+1)

and `Saux^2=1-A^2 mod f` imply `psi_A(j)=+c or -c mod f`.
Reduce `j` modulo `2m` and reflect into `[0,m]`. Pell addition gives an
index `p` of the same odd parity with `psi_A(p)=+c or -c mod f`.
Since `psi_A(p)<=I<f/2` and `c<=I<f/2`, this congruence cannot wrap.
Therefore

    c=psi_A(p), p>=1 odd.                          (9)

This is the precise point at which the main radicand becomes square:

    Dm=1+Delta*c^2=chi_A(p)^2=d^2.

As `S=E*Dm=sigma^2`, one has `E=(sigma/d)^2`. A rational square that
is an integer is the square of an integer. Thus

    E=tau^2, sigma=tau*d, g=tau*d*f.                (10)

The first Pell root is recovered after the main folding. This ordered
recovery is the new mathematical step.

## 4. Transport and all remaining source hypotheses

The parent's first-Pell classification now applies to (10), because
`E=1+XY^2(XY^2+1)k^2`. With `P0=2XY^2+1`, it yields
`k=2psi_P0(n0)` for `n0>=1`. Its first index would force `k=2`,
`eta=zeta=1`, and `c=2Y+1`, strictly between the first two main ordinates.
Hence

    n0>=2, k>=8XY^2+4, c>kY>=k>8q^7, c>X, K>0.    (11)

We give the new strong-size estimate explicitly. Since `a=Delta*U^2*S`
and `g^2=S*(1+a)`,

    a^2/g^2=Delta*U^2*a/(1+a)>Delta*U^2/2>36.

Also `a>2c`. Thus `a>6g`, `F2>2c`, and for nonzero integral `b`,

    sign(V)=sign(b), |V|>=F2-c>a/2>3g, |V|>|b|,
    y<(3/2)|V|.                                    (12)

The case `b=0` is excluded by (6), because it would make
`y^2-c^2=(c^2-1)/(Q-1)` an integer strictly between zero and one.

To use the smaller transport weight `L=bV`, the parent's exclusion of
the third main index applies unchanged: if `p=3`, monotonicity forces
`n0=2`, and the exact remainder

    eta=4Y^2[X(X+2-2Y)+1]+8Y(X+1)+3-4Y

with `0<eta<k=8XY^2+4` forces `2Y-X` to be 1 or 2. This contradicts
`q|(2Y-X)` and `q>=32`. Therefore `p>=5`, and
`c>c3:=4Delta+3`. The auxiliary odd index from (6) cannot be 1, since
`|V|>1`. Index 3 would give `|V|=4Q-3`, hence one of

    F2*(b-4Delta)=c-c3,
    F2*(b+4Delta)=c+c3.

Both right sides lie strictly between zero and `2c<F2`, impossible.
So the auxiliary index is at least 5 and `|V|>8Q^2`. Since `Q>F2`,

    |b|>(8Q^2-c)/F2>8F2-1/2>4F2>4g,
    g*y<(3/8)|b||V|<L/2.                           (13)

The exact identity `e=b-cT+k-1` and (11) give `rho<|b|/D`. If `B<=-1`,
then `Wt<=-L-1/h`, so (1), (7), (13), and `D=XY>2` give

    n=epsilon*g*y-kappa+Wt+rho
      <L/2-L+|b|/D<0,

contrary to `n>0`. Therefore `B>=0`, which forces `C>0` from its definition.
The inherited outer mask inequality gives `3q<R<q^4-2`; (11) gives
`c>2R`. Pell growth also gives `c>2p`. The normalized rank theorem,
using (8),(9), now gives `f=chi_A(m)` with `pc|m` and `m>2p`.
The residues `V=-c mod f` and `V=-R mod c`, together with (6), give
`p=R` by the retained signed auxiliary-index theorem. Its hypotheses
are exactly those just established; it requires no doubled strong pair.

From here the parent's denominator and native arguments apply literally.
For clarity, their order is recorded. Integrality of `z` in (1) gives
`D|hHe`. Since `q^4|D=XY` and `gcd(q,hH)=1`, we obtain `q^4|e`.
The recurrence gives `k=2n0 mod 4XY^2`. Monotonicity from `P0>A`
and `c>k` gives `n0<R`. Thus `q^4|(2n0-R-1)` and
`|2n0-R-1|<R<q^4`, proving `2n0=R+1`.
Only now does the full recurrence give `4XY^2|e`, hence `D|e` and
integral `rho`.

The retained uniform ratio lemma, at scale one, supplies
`Y>X^((R-1)/2)/3` and the strict whole-product bound. Integral carrier
recovery supplies `H|hK`, and the universal projection gives

    H | h*(X-2^R)*(2^R*X+1).

The absolute value of this entire divisible product is below `H`; hence
`X=2^R`. This step cancels no arbitrary nonunit modulo `H`. It makes
`kappa` integral; then `W=1 mod h` in (1) yields `h|B` and integral
`t>=0`. Literal `q^3|Y`, the retained fixed-minus parity and exact
half-binomial rounding give the fresh source at base `Y(X+1)+2`.
The whole indexed native coefficient calibration therefore gives a finite
syntactic ZFC refutation. No coefficient port is replaced or mixed.

## 5. Constructive positive converse

Start from a finite refutation and the parent's canonical outer data:
`X=2^R`, `R=3 mod 4`, `R>3q`, `q^3|Y`, and integral `t=B/h>=0`.
Retain those data and the scale-one choices

    c=psi_A(R), d=chi_A(R),
    k=2psi_P0((R+1)/2), tau=chi_P0((R+1)/2),
    eta=c-kY>0, zeta=k-eta>0.

The uniform ratio and half-binomial lemma proves both last inequalities;
they are exactly the incoming parent's outer witnesses. It also gives
positive integral `rho=e/(XY)` and positive integral `kappa=K/H`.

Choose one positive strong Pell pair `(f,I)` whose ordinate is divisible
by `A*c^2*tau*d`. Such pairs exist by taking a positive multiple of the
finite period of the matrix `[[A,Delta],[1,A]]` modulo that integer; its
determinant is 1, so its powers form a finite group. Put

    i=I/(A*c^2*tau*d)>0, U=i*A*c^2.

Then `S=E*Dm=(tau*d)^2`, `I=U*tau*d`,
`F2=1+Delta*I^2=f^2`, `Q=(Delta*I)^2`, and `G=(tau*d*f)^2`.
Keep this strong pair fixed. The positive auxiliary reconstruction lemma
in `inherited/proof_sources/universal_pell.tex` requires only
`R=3 mod 4`, `c=psi_A(R)`, the strong norm, and `c|I`.
It therefore supplies positive integers

    Vstar=chi_(Delta I)(R)/(Delta I),
    y=psi_(Delta I)(R),
    T=(Vstar+c+R*f^2)/(c*f^2),

with `V=Vstar` and (6). There is no requirement that the strong pair be
doubled or have a prescribed odd multiplier.

Lastly set

    n=g*y+(1+hL)*t+rho-kappa, g=tau*d*f.

It is integral. Moreover `K/H<Xc` because `H>3` and
`K=3Xc-2X^2+2<3Xc`; and
`f>(A-1)I>(A-1)c>Xc`, since `A-1=Y(X+1)>X` and `I>=c^2`.
Thus `g>kappa`. With `y>=1`, `t>=0`, `rho>0`, one gets `n>0`.
Its carrier is `z=gy`, so the literal polynomial vanishes. All ten
independent variables are positive. This completes both existential
directions; negating them gives the stated consistency equivalence.

## 6. Exact arithmetic cost and degree

All 78 rows of the supplied DAG are live, including every input and fixed
port. The count is 46 multiplications, 18 additions and 14 subtractions.
Relative to the 76-operation parent, its old twelve-row strong/final-factor
subgraph is replaced by fourteen rows. Squares and scalar products count.

Give each quantified variable weight one and each fixed coefficient weight
zero. The decisive exact degrees are

    A 6, Delta 12, c 5, E 22, Dm 22, U 17,
    S 44, a 90, F2 90, Q 102, G 134,
    b 6, V 96, L 102, M 13, B 2, Z 117.

The term `-Q*M^2*G*V^2` has degree
`102+26+134+192=454`. Every other term in
`P=(Q-1)Z^2-M^2G(QV^2-1)` has strictly smaller degree (in particular,
`QZ^2` has degree 336). Therefore there is no top-degree cancellation.

Write `q0=beta*J` and `k0=eta+zeta`. The entire highest homogeneous part is

    [P]_454 = -16*q0^284*w^42*s^80*i^8*k0^38*T^2.   (14)

For example, the coefficient of
`J^284*w^42*s^80*i^8*eta^38*T^2` is `-16*beta^284`, nonzero for the
actual fixed positive beta. Formula (14) proves attainment of the global
degree at the supplied coefficients. The exact checker independently
propagates and compares all 39 coefficients of (14).

## 7. Inherited sources and scope of verification

The parent proof is `inherited/PROOF.md`, selected from the incoming
Centered Residues archive at the immutable commit named above. Its copied
`proof_sources/` includes the full ordinary universal rank, signed-index,
positive auxiliary, uniform-ratio, and indexed-native statements and proofs
used here. The coefficient tuple and licenses remain unchanged. These are
explicit mathematical dependencies, not a claim to have rerun their entire
transitive formal-assistant development.

`verify.py` checks the finite DAG, exact displayed polynomial cuts, whole
coefficient bytes, liveness, operation counts, all leading terms, and
deliberately changed circuits. It also replays the builder. Its small local
Pell controls exercise the new cofactor identities only; they are not roots
of the calibrated consistency equation and make no consistency inference.
The unbounded proof is the ordered argument in Sections 2--5 plus the
identified inherited source calibration.
