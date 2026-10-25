# Cofinal index recovery with an admissible existing denominator

## Result and status

Four explicit polynomials in ten strictly positive integer unknowns are
supplied. Their arithmetic-circuit cost and exact total degree are:

| Carrier denominator | Transport weight | Binary operations | Degree |
|---|---|---:|---:|
| XY | V² | 75 | 626 |
| XY | bV | 76 | 464 |
| q⁴ | V² | 76 | 622 |
| q⁴ | bV | 77 | 460 |

The first and second are the useful new cost/degree frontier points among
these four: the 76/464 point dominates the 76/622 point. The 77/460 point
trades one more operation for four fewer degrees. Each uses the complete
indexed BFS943 fixed coefficient tuple copied from the latest incoming
Certificate Reductions package, with no mixed ports.

The claim is an ordinary mathematical theorem formalizable in ZFC,
composed with the explicitly identified native/refutation calibration:

    ZFC proves (no strictly positive zero) iff Con(ZFC).

No global minimum or historical priority is claimed. These improvements
do not decide consistency. The proof is ordinary mathematics, not a new
Lean/Rocq derivation or an emitted object-language ZFC proof. The new
contribution is the denominator criterion, its smallest-degree q⁴ choice,
the XY sharing choice, and the sound unshifted composition. The absolute
trace technique and Pell doubling are inherited and explicitly credited.

## 1. Whole polynomial

The ten unknowns are J,F,alpha,i,T,w,s,n,eta,zeta > 0. The four fixed ports
are beta,K0,MC,MF. Their inherited box is

    beta >= 31 odd, K0 > 0, 0 < MC < beta < MF < 2 beta.

Use the following polynomial abbreviations:

    h=beta J, q=h+1, C=q-F-alpha,
    X=wq, Y=q³s, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A²-1, H=4A-5,
    ell=(XY)(kY), E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    e=k-R-1, B=(K0+w)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    f²_symbol=1+4aF0, Q=Delta(f²_symbol-1),
    b=cT-R, V=f²_symbol b-c,
    Kpos=X(3c-2X)+2.

Here `f²_symbol` is a polynomial abbreviation; it is computed without
introducing f as an unknown. It equals (1+2a)² identically. Choose either

    D=XY or D=q⁴, and L=V² or L=bV.

Finally set

    M=hDH,
    Z=hD[H(n-LB)+Kpos]-H[DB+he],
    RG=M²G,
    P=Q(Z²-RG V²)+(RG-Z²).

The single equation is P=0 in the stated domain. All divisions below are
proof notation; there is no division, exponentiation instruction or
additional quantified variable in any emitted graph. The graph uses
XY as a shared expression in A-1=XY+Y and ell=(XY)(kY).

## 2. The admissible-denominator theorem

The same arithmetic proof works whenever D is an integer polynomial in
the ten unknowns such that, at every positive input,

    D>0, q⁴ divides D, and D divides 4XY².             (A)

The roles of the two divisibilities are different. The first recovers a
small, bounded index error; the second recovers the full rational carrier
only after that error has vanished. No claim that D is coprime to h is
made or needed. In particular:

    XY=q⁴(ws),   4XY²=(XY)(4Y);
    4XY²=q⁴(4ws²q³).

Thus both advertised D satisfy (A), and both satisfy D>=q⁴>2.

Let z=Z/M, kappa=Kpos/H, rho=e/D, t=B/h, and W=1+hL. Identically,

    z=n+kappa-Wt-rho,                                (B)
    P=(Q-1)Z²-M²G(QV²-1).

These identities make sense before any divisibility or sign of B is
known. In particular (B) is not initially an equality of integers.

## 3. Integral roots without a transport sign

Positive inputs imply q>=32, X>=q, Y>=q³, k>=2, c>=3, A>4, Delta>=3,
U>=c², E>1, f²_symbol>2c, Q>1 and M>0. For any integral b,
V=f²_symbol b-c is nonzero and |V|>1. The identities

    f²_symbol=(1+2a)²,
    Q=4Delta²U²G

give gcd(G,Q-1)=gcd(G,QV²-1)=1. If P=0, then

    (Q-1)z²=G(QV²-1).

The valuation of each prime dividing G is even: its valuations in Q-1
and QV²-1 are zero, and a rational square has even valuations. Therefore
G=g² for an integer g>0. Since gcd(E,F0)=1, both E=tau² and F0=f0² are
positive squares and g=tau f0. Put y=|z|/g. Then

    QV²-(Q-1)y²=1.                                  (C)

The rational adjacent-Pell descent in the copied parent proof shows that
y is an integer. Explicitly, if y=r/m is reduced then m² divides Q-1.
For v=|V|>1, v<y<Qv/(Q-1), and

    v'=(2Q-1)v-2(Q-1)y,
    y'=(2Q-1)y-2Qv

has nonzero integral first coordinate, |v'|<v, unchanged norm, and the
same reduced denominator m in its second coordinate. Indeed m²|Q-1
ensures v' is integral, while 2Q-1=1 mod m preserves the denominator.
Reflecting signs and descending reaches v=1, where y=1. Thus m=1,
and z=epsilon gy is integral, with epsilon=+1 or -1.

For proof purposes set f=1+2a and I=2Ug. Then

    f²=f²_symbol, f²-Delta I²=1,
    Q=(Delta I)², c² divides I.

Here is a self-contained proof of the signed all-index folding step.
Classify the strong norm as f=chi_A(m), I=psi_A(m), m>=1. With
S=Delta I, the adjacent norm gives S|V|=chi_S(j), y=psi_S(j). The trace
modulo S forces j odd. For j=2r+1 write chi_t(j)=t Q_r(t²), where
Q_0=1, Q_1(z)=4z-3 and Q_(r+1)(z)=(4z-2)Q_r(z)-Q_(r-1)(z).
The recurrence gives Q_r(1-A²)=(-1)^r psi_A(2r+1). Since S²=1-A²
modulo f, this gives psi_A(j)=+c or -c modulo f, because V=-c mod f.
The Pell addition laws give

    psi_A(j+2m)=-psi_A(j) mod f,
    psi_A(2m-j)=psi_A(j) mod f.

Reduce j modulo 2m and reflect about m. This supplies p in [0,m], with
p=j mod 2 and psi_A(j)=+psi_A(p) or -psi_A(p) modulo f. Since
0<c<=I and 0<=psi_A(p)<=I<f/2 for A>=3, the congruence forces
c=psi_A(p). Therefore p is positive and odd. This argument does not
require V>0 or a parity condition on m.

For proof notation put V0=XY². The first norm E=tau² gives

    k=2psi_(2V0+1)(n0), n0>=1.

If n0=1, k=2 and eta=zeta=1, so c=2Y+1 lies strictly between psi_A(1)=1
and psi_A(2)=2A. This is impossible. Consequently

    n0>=2, k>=8V0+4, c>kY>=k>8q⁷, c>X, Kpos>0.       (D)

No sign of B,C,R,b,V, or rho was used in these deductions.

## 4. Absolute transport bounds for the unshifted T

The pointwise inverse T_old=T-alpha of the removed shift need not be
positive. It is therefore not a soundness argument. We instead prove
the following pretransport estimates directly.

First b cannot vanish. Otherwise V=-c and (C) implies

    y²-c²=(c²-1)/(Q-1),

strictly between zero and one since Q>=9c⁴>c². The left side is integral.
Put D0=Delta U²>=243. Since a=D0E and g²=E(1+a),

    a²/g²=D0*a/(1+a)>D0/2>9.

Thus a>3g and a>=c. For nonzero integral b,

    sign(V)=sign(b), |V|>=f²_symbol-c>a>3g, |V|>|b|,
    y<(3/2)|V|.

If L=V², these inequalities immediately give gy<L/2.

For L=bV an additional index argument is needed. It is particularly
short here because q divides both X and Y. The main index p cannot be
one since c>=3. Suppose p=3, so c=4A²-1. If n0>=3, then

    k>32V0², c<64X²Y²<32X²Y⁵<kY<c,

where A<4XY and Y>=q³. Hence n0=2, k=8V0+4. Write u=X+2-2Y. The exact
remainder formula is

    eta=4Y²(Xu+1)+8Y(X+1)+3-4Y.

If u<=-1 this is negative because Y(X-1)>2(X+1). If u>=2, subtraction
of k leaves at least 4Y²+8Y(X+1)-4Y-1>0. The condition 0<eta<k thus
forces u=0 or 1, or equivalently 2Y-X in {1,2}. This contradicts
q|(2Y-X) and q>=32. Therefore p>=5 and

    c>c3:=4Delta+3.

Set S=Delta I, so Q=S². Positive Pell classification in (C), applied to
|V|, gives |V|=chi_S(j)/S for an odd j>=1. Index one gives |V|=1 and
is impossible. For index three, |V|=4Q-3, and the two signs would imply

    f²_symbol(b-4Delta)=c-c3, or
    f²_symbol(b+4Delta)=c+c3.

But 0<c-c3<c+c3<2c<f²_symbol. Neither right-hand side is a multiple of
f²_symbol. Thus j>=5 and |V|>=16Q²-20Q+5>8Q². Since Q>f²_symbol>2c,

    |b|>(8Q²-c)/f²_symbol>8f²_symbol-1/2>4f²_symbol>4g.

Therefore L=bV=|b||V|>0 and gy<(3/8)L<L/2 also in this case.

In both cases e=b-cT+k-1<b, using c>k and T>=1. Hence rho<|b|/D.
If B<=-1, then Wt<=-L-1/h. Equation (B) gives

    n=epsilon gy-kappa+Wt+rho
       <L/2-L+|b|/D<0,

since D>2 and either L=V² with |V|>|b|, or L=|b||V| with |V|>1.
This contradicts the actual positive input n. Hence B>=0 and C>0.

## 5. Rank first; bounded error second; full denominator third

The inherited outer mask estimate, now licensed by C>0, gives

    3q<R<q⁴-2.

The new bound (D) implies c>2R, and T>=1 gives b>=c-R>0 and V>0.
The retained normalized strong-rank and signed auxiliary-index theorems
have the same c²|I, c>2p, c>2R, V=-c mod f and V=-R mod c as before.
They give p=R. These results require neither T+alpha nor b>c. The usual
mask parity then gives q even and J odd.

The integral carrier z in (B), after multiplication by hH, gives

    D divides hHe.

Because H=4Y(X+1)-1=-1 mod q and h=q-1, gcd(q,hH)=1. By (A),

    q⁴ divides e.                                    (E)

The universal base-one Pell congruence is

    k=2n0 mod 4XY².                                  (F)

It follows that q⁴ divides 2n0-R-1. Moreover P0=2XY²+1>A. If n0>=R,
monotonicity in index and base gives k/2=psi_P0(n0)>=psi_A(R)=c, contrary
to c>k. Therefore 1<=n0<R, and

    |2n0-R-1|<R<q⁴.

Together with (E)--(F), this proves 2n0=R+1. Only now use the full
congruence (F): it gives 4XY²|e. Hypothesis (A) consequently gives D|e,
so rho is an integer. This is the precise point at which its integrality
is obtained. The complete denominator was never assumed coprime to h.

## 6. Projection and the fixed native endpoint

Once p=R, n0=(R+1)/2 and rho integral, the rest of the incoming
Certificate Reductions proof applies at lambda=1, unchanged. Write
R=2r+1. Since R>3q>=96, r>=48. The uniform ratio estimate gives
Y>X^r/3 and X^(r+1)<3Y(X+1)<H. From (B), H|hKpos. The universal Pell
projection, using that H is odd and cancelling only two, gives

    H divides h(X-2^R)(2^R X+1).

The whole-product height bound makes its absolute value less than H,
so X=2^R. This step does not cancel arbitrary factors modulo a composite
H. Then kappa is integral; (B) gives Wt integral; W=1 mod h gives h|B.
Thus t is a nonnegative integer. Also q³|Y was imposed from the start.

The retained fixed-minus parity, exact half-binomial rounding, and fresh
unscaled native reconstruction now have every original hypothesis. The
reconstructed source base is Y(X+1)+2, not the present A. The whole
indexed tuple calibration yields a finite syntactic ZFC refutation.

## 7. Positive completeness

Conversely a finite refutation gives the same canonical outer data as
the parent: X=2^R, R>3q, R=3 mod 4, q³|Y, and integral t=B/h>=0. Use
the parent's lambda=1 bases and its constructive ratio result to form

    c=psi_A(R), k=2psi_(2XY²+1)((R+1)/2),
    eta=c-kY>0, zeta=k-eta>0, tau=chi_(2XY²+1)((R+1)/2).

Then 4XY²|e, so (A) guarantees rho>=0 integral. The projection makes
kappa positive integral. A positive multiple of the Pell matrix period
modulo c²tau supplies a seed pair (f0,I0) with c²tau|I0. Set
i=I0/(c²tau)>0 and double the pair, giving exactly f=1+2a and I=2Ug.
The existing auxiliary theorem constructs integral positive V,y and

    T=(V+c+Rf²)/(cf²)>0.

No subtraction of alpha is made. For either weight, choose

    n=gy+(1+hL)t+rho-kappa.

The inherited bound f0>(A-1)I0>Xc>kappa gives g>kappa, so n>0. Its
carrier equals gy and the polynomial is zero. All ten independent inputs
are strictly positive. The two directions prove the claimed consistency
equivalence at the stated inherited proof boundary.

## 8. Exact global degrees and measured costs

All binary additions, subtractions and multiplications are counted,
including fixed scalar multiplication and squaring. There are no dead
gates, unused inputs or unused fixed ports. Compared with the latest
78/630 and 79/468 parents, removing T+alpha saves one addition. Reusing
XY in A-1 and the first norm saves one multiplication when D=XY.
Using the existing kY in ell=(XY)(kY) saves a second multiplication.
The q⁴ version
then adds the single square q²*q².

Put q0=beta J and k0=eta+zeta. The complete highest homogeneous
polynomials are:

    XY,V²:
      2^14 q0^378 w^48 s^110 i^20 k0^64 T^4 (q0-F-alpha)^2;
    XY,bV:
      -2^10 q0^284 w^36 s^82 i^14 k0^46 T^2;
    q⁴,V²:
      2^14 q0^378 w^46 s^108 i^20 k0^64 T^4 (q0-F-alpha)^2;
    q⁴,bV:
      -2^10 q0^284 w^34 s^80 i^14 k0^46 T^2.

Their degrees are 626,464,622,460 respectively. The selected coefficients
2^14 beta^378 and -2^10 beta^284 are nonzero for the actual fixed beta.
These are complete multivariate leading components, not numerical rays.
The independent verifier collects all 390 terms in each V² leading
component and all 47 in each bV leading component. It also verifies 32
or 33 exact free-polynomial cut identities covering every gate, every
raw coefficient byte hash and bit length, topology, liveness and counts.

The exact checks prove the circuit and arithmetic identities. The
unbounded Pell/index/native arguments are the ordinary proof above and
the copied sources; finite checks alone do not prove those theorems.

## 9. Source ledger

- Audit snapshot: ProveIt e0c98c629bf10d30b695884f6b1d2ab361bdf513.
- Latest parent: docs/incoming/ConZFC_Certificate_Reductions_2026-10-25.zip,
  compact/PROOF.md and equation78.json/equation79.json.
- Unshifted source: research/ten-positive-unshift-t-square/PROPOSAL.md and
  research/ten-positive-unshift-t-bv/PROPOSAL.md at the audit snapshot.
- Copied proof_sources/universal_pell.tex gives the source-61 normalized
  rank, signed-index, parity and auxiliary lemmas; the sign-free folding
  proof is supplied directly in section 3 above. uniform_ratio.md gives the
  lambda>=1 ratio theorem; indexed_native.md identifies the whole fixed
  coefficient specialization.

The artifacts retain the four literal coefficient payloads and their
finite constant recipe. They specify actual fixed integer polynomials;
the ports are not extra unknowns and no compiler run remains to produce
the advertised four equations.
