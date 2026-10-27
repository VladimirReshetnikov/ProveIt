# Thirteen positive variables, 178 paid operations, degree 86

This packet defines a different polynomial with exactly the same complete
positive zero set as the accepted 97/88 parent. Both witness maps preserve
all thirteen coordinates. The ordinary proof below is formalized in
`ThirteenScaledNormSyzygy86.lean`; the independent literal arithmetic audit
pays all operations and verifies the entire leading homogeneous polynomial
and the complete current coefficient tuple. These are separate checks.

## Exact parent and notation

The parent is the accepted 97-operation degree-88 graph
`../thirteen-second-first-norm-corrections/polynomial88.json`, SHA-256
`32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1`.
Its thirteen strictly positive integer coordinates remain
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`; its fixed ports are the complete
current 2011 tuple `beta,K0,MC,MF`. In particular MF is the once-shifted source
port, and the tuple has 47,313 uncompressed bytes. No historical 2501 ports
are substituted.

Use the parent's exact polynomial blocks, with its `qm` written b, its `B`
written G, its `N0,N1,Na` written P,Q,U, and its `R` written R:

    b = beta*J; q = b+1; X = w*q; Y = s*q^3; E = X*Y;
    k = eta+zeta; K = k*Y; ell = E*K; c = K+eta;
    a = E+Y; H = 4*a+3; delta = a^2+H;
    Q = (X+a*c+gamma*H)^2 - delta*c^2;
    P = (E*n+k-R)^2 - ell*(ell+k);
    C = q-F-alpha; G = (K0+w)*C-F;
    V = f^2*(c*T-R)-c;
    y = 1+4*(b*(m-(c*T-R)*V*G)-G);
    U = delta*(f^2-1)*(V^2-y^2)+y^2;
    Z = f^2-delta*(b*i*c^2)^2.

Here R is exactly the parent's scalar rank polynomial, with all four ports.
Let A88 be the already paid parent correction coefficient:

    A88 = 16*T^2*V * ((b*G)^2*V*(f^2-1)
           + 2*f^2*(V*C*(2*b*G-X*C)-(b*G)^2*f^2*R)).

Thus the old corrected auxiliary is U88 = U-A88*(P-1).

## New coefficients and polynomial

All definitions below are integer polynomials. No variable or coefficient is
inverted. Write

    A = k-4*gamma;
    S = 8*gamma*(P-1)+K*(Q-1);
    Gc = K0*C-F; g = k*s*q^2;
    u = X*R; v = T*K; e = u-v; h = G-q*Gc = w*C-b*Gc;

and define the two compact coefficient brackets

    L1 = C*e*(2*X*v+f^2*(3*u-v))
         + 2*f^2*T^2*C*X*(K*X*eta+g^2)
         - 4*f^2*Gc*v^2;

    L2 = C*K*X*u
         + h*(-2*v*e+f^2*(R*(4*v-3*u)-2*T*v*X*eta))
         + f^2*T*v*g*(2*Gc-C);

    Bcorr = 16*(f^2*T)^2*C*(L1+2*L2);
    Hcorr = 8*b*f^2*(f^2*T)^2*v^2*Gc*(b*Gc+C);
    Uc = A*(U-(A88+Bcorr)*(P-1))-Hcorr*S.

The new equation is

    (P*Q-1)^2 + (Z-1)^2 + (Uc-A)^2 = 0.                 (★)

This is deliberately a residual sum of squares. Substituting A*U into the old
unit sphere would be invalid unless A=1; no such assertion is made here.
The old three-square unit sphere and (★) are generally different polynomials.

## Conditional positivity of the scale

This argument uses only positive coordinates, beta>0, and Q=1. It does not
use P=1, U=1, Z=1, a native word, or a Pell witness construction.

Since b is a positive integer, q>=2, X=w*q>=2, and Y=s*q^3>=8.
Also k=eta+zeta>eta>0, gamma>0, c=k*Y+eta>0, a=(X+1)*Y>0,
and H=4*a+3>0.
Suppose A<=0, so k<=4*gamma. Then

    c = k*Y+eta < k*(Y+1) <= 4*gamma*(Y+1) <= 2*gamma*a.

The last inequality is equivalent to 2<= (X-1)*Y, which follows already
from X>=2 and Y>=2. Expanding the actual main norm gives the exact identity

    Q = (X+gamma*H)^2 + 2*a*c*X + H*c*(2*a*gamma-c).

Every summand is nonnegative and the first is at least 4; indeed the final
two summands are positive. Thus Q>1, contradicting Q=1. Consequently

    Q=1 ==> A>0,

so cancellation of A is justified only after independently recovering Q=1.
There is no global positivity assumption on A in the polynomial definition.

## Whole positive zero-set equivalence

The source-bound accepted lemmas used here are:

* `ThirteenCorrectedStrong.first_ne_neg_one p v hb hv`: P is not -1 on
  the positive domain, with beta>0.
* `ThirteenUnitSphere96.main_ne_neg_one p v`: Q is not -1 unconditionally.
* `ThirteenUnitSphere96.positive_zero_iff_residuals p v hb hv`: the old
  75-operation sphere vanishes iff P*Q=1, U=1, and Z=1.
* Its proof obtains Z=1 first using `strong_ne_neg_one`; only then does it
  invoke `auxiliary_ne_neg_one p v hs`, whose explicit premise is Z=1.
  That premise turns delta*(f^2-1) into a square and invokes
  `ShortSystem.square_aux_ne_neg_one`. This proof uses that exact
  conditional result, not an unproved unconditional sign of U.
* `ThirteenSecondFirstNormCorrections.positive_zero_iff75 true p v hb hv`
  identifies the complete positive zero set of the 97/88 parent with that
  75-operation sphere, with identical thirteen coordinates.

From (★), each integer square is nonnegative, hence P*Q=1, Z=1, and Uc=A.
An integer product equal to 1 has unit factors. The first two exclusions
therefore give P=Q=1, independently of Uc. Both ideal corrections then vanish,
so Uc=A*U. The preceding conditional scale lemma yields A>0, hence U=1.
The accepted residual characterization gives an old sphere zero, and the
accepted parent equivalence gives a 97/88 zero with the SAME coordinates.

Conversely, a 97/88 zero gives an old sphere zero and thus P*Q=1, U=1, Z=1.
Again the independent negative-unit exclusions give P=Q=1. Consequently
S=0, Uc=A*U=A, and every residual in (★) vanishes. This direction does not
need to assume or prove A>0 separately.

Thus both maps are the identity on all thirteen positive coordinates. No
canonical-only argument, sign assertion about V, signed-ordinate positivity,
extra native premise, or supplied target zero is used. The accompanying Lean leaf
inherits the exact current external ConZFC endpoint from the accepted
parent using its proved `positive_zero_iff88` and `exists_positive_zero_iff88`. This is not an internal HA, PA,
or ZFC proof and does not close the open HA calibration work.

## Exact paid graph and polynomial binding

`polynomial.json` retains the accepted parent's first 88 literal operations,
ending at `Pminus1=P-1`, and adds the explicit 90 rows listed in `audit.py`.
All 178 gates are live: 117 multiplications, 29 additions, and 32 subtractions.
All thirteen variable leaves and all four fixed numeral leaves are live.
Constant multiplications, coefficient formulas, residuals, and squares are
included. The graph has integer leaves and binary arithmetic only; no
subtraction, division, or large intermediate expression is free.

The source graph aliases `qm,B,N0,N1,Na,coeff` stand for
`b,G,P,Q,U,A88`. The new outputs `r148,r150,r155,r163,r169` are exactly
`Bcorr,A,S,Hcorr,Uc`. Each new row is checked by exact sparse polynomial
arithmetic, in two stages. First twelve independent cuts bind the entire
compact Bcorr/Hcorr coefficient formulas; the definitions of Gc and g are
checked separately. Next ten independent cuts bind the scale, syzygy,
corrected auxiliary, all three residual squares, and final sum. The prefix
is pinned byte-for-byte to the already audited parent. No random evaluation
is used to justify these identities or the whole-zero-set theorem.

## Exact degree and complete homogeneous leaders

Fixed ports have degree zero. The degree calculation works in the original
thirteen coordinates, including both eta and zeta; it does not rely on
specializing or identifying them. Write B=beta*J and k=eta+zeta. Full expansion
of the two norms and their syzygy gives degree(P)=22, degree(Q)=18,
degree(S)=21, and the exact independent factorization

    S21 = -4*B^13*k^2*s^4*w*(k-4*gamma).

For the other internal gates the auditor retains every monomial in the
eight highest layers of a rigorously propagated upper bound D, namely
all degrees at least D-7. Addition uses max(Dleft,Dright), multiplication
uses Dleft+Dright. Because no omitted summand can contribute at or above
that new threshold, these layers are exact. Propagated bounds are not
sharpened when cancellation occurs, except at P,Q,S, whose full expansions
are independently computed. At every gate a nonzero retained layer is
required; consequently the complete highest homogeneous polynomial of
every gate is known, even though lower layers are not fully expanded.

The highest relevant bound for Uc is 49. All layers of degrees 49 through
44 vanish and degree 43 is nonzero. Subtracting the degree-one A leaves
that leader unchanged. The two other residual squares have degrees 80
and 72. Thus the complete degree-86 output leader is exactly the square
of the complete degree-43 Uc leader. The final five gates are evaluated
from their complete leaders, without a needless full polynomial expansion.
The certificate stores every gate degree and every complete homogeneous
leader (deduplicated by exact hash), including that full final square.

The coefficient of

    J^27*f^6*T*s^3*w^4*eta^2

in Uc43 is exactly 64*beta^27. The coefficient of the doubled monomial
in the degree-86 output is exactly 4096*beta^54. The audit also verifies
that no other fixed-port monomial contributes to either selected unknown
monomial. The actual full beta is positive, so the selected coefficient
survives specialization to the complete current tuple. Degree 86 is
therefore exact for the actual equation, not merely a generic upper bound.
All other actual branch degrees and complete leaders are recorded as well.
For each of the 178 complete gate leaders, a nonzero coefficient modulo
1,000,003 after specialization to all four actual ports certifies that its
degree survives specialization. This uses exact nonvanishing; it is not an
identity test and is not used for the positive-zero-set proof.

## Current coefficients and proof boundary

The four complete ports are copied byte-identically from the accepted
97/88 packet. The auditor reconstructs every integer independently from
the 3297-entry current coefficient array and the actual radix-47 recipes.
It verifies each gzip hash, decompressed byte hash, byte count, bit count,
integer value, and the total 47,313 uncompressed bytes. MF is shifted by
beta exactly once. This does not replace the frozen native proof; it binds
the present graph to its actual complete ports.

The Lean leaf proves ring-homomorphism compatibility, evaluation of the
MvPolynomial, equality of the complete positive-zero predicates with the
parent, and

    (not PositiveZero currentPolynomial) iff DiophantineConsistency.ConZFC.

This is the existing external Lean proposition for the actual current
ports and actual ConZFC definition. No internal HA/PA/ZFC theorem, new
machine calibration, signed-domain extension, or global optimum is claimed.
The new polynomial is not identically equal to its parent; a positive
actual-port modular counterexample is recorded solely for nonidentity.
Exact modular dependence witnesses similarly certify that every variable
and fixed port affects the polynomial, not its zero-set equivalence.

The change is deliberately a tradeoff within the current 47,313-byte
coefficient tuple and its externally formalized thirteen-variable family:
the operation count rises by 81 from 97 to 178 while degree falls from 88
to 86. It is not a globally nondominated variables/operations/degree point.
The historical ordinary thirteen-variable88/51 and twelve-variable96/70
forms have better such metrics but separate larger compact44 coefficient
tuples and ordinary calibration scopes; the historical thirteen-variable
page retains 295,388 raw coefficient bytes. A transfer to the current tuple
is not established by this packet. No minimality claim follows.
Both accepted parent and exploratory search packets remain unchanged.

## Bound source pins

* Parent literal graph: `32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1`.
* Parent Lean source: `ea83a05732e96ebbadbab135f98018f5bcda115c887c1896b0f4be30a267bd22`.
* New Lean source: `53be78f9046b591dcd1a33421d3dae3e14764537ac19fa0906665e3e0829f253`.
* New focused checks: `9a4b58d6ff9eddb83ce2013d18da867211b70abffac03ba9de99bbc1f82c8c4f`.
* Actual native proof: `69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.
* Actual native certificate: `fae49c56a9c57d394335c8a47da395f000a0c25cb8267d1330104eddbbc7850f`.

Reproduction commands, exact final output hashes, cache provenance, and
failed author-run history are retained in README and the author receipt.
