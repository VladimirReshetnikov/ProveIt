# Use the explicit Pell trace before squaring it

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

## 1. Result, domains and comparison

The five supplied ordinary polynomials have exactly ten independent unknowns,
all strictly positive integers. Their coefficients are the entire directly
indexed BFS943 radix67 tuple retained in `coefficients/`. Named registers are
polynomial abbreviations and introduce no additional unknowns.

| New literal circuit | Operations | Exact degree | Matched parent operations / degree |
|---|---:|---:|---:|
| trace75_degree402.json | 75 | 402 | 75 / 626 |
| trace76_degree352.json | 76 | 352 | 76 / 464 |
| trace79_degree290.json | 79 | 290 | 79 / 382 |
| trace80_degree258.json | 80 | 258 | 80 / 338 |
| trace87_degree232.json | 87 | 232 | 87 / 304 |

The new observation is that the doubled construction already exposes its
strong Pell trace as the polynomial `f=1+2a`. Its old auxiliary expression
nevertheless used `f^2`. The literal congruence `f=1 mod c` allows replacing

    old V = f^2(cT-R)-c  by  new V = f(cT-R)-c.

The second expression preserves both necessary residues and cuts the degree
of V. The trace is computed as `f=a+F0`, using the existing `F0=1+a` register. Thus all five circuits retain their parent's operation count. The resulting degree
decrease is 224, 112, 92, 80, or 72, respectively. In particular 87/232
improves both operation count and degree over the previously catalogued
121-operation degree-246 ten-positive construction. It is not a global
minimum theorem or a claim to improve the number of unknowns. Positive
integers must not be silently replaced by unrestricted integers.

The ordinary proof below, composed with the explicitly inherited native and
syntactic-refutation calibration, proves in ZFC that each polynomial has a
positive zero if and only if ZFC has a finite syntactic refutation. Negating
this equivalence gives the requested consistency statement. No consistency
assumption, consistency proof, new end-to-end Lean/Rocq object or encoded
object-ZFC derivation is claimed. The finite checker authenticates formulas,
not unbounded number-theoretic arguments.

The frozen parents are retained under `inherited/lucas` and
`inherited/cofinal`, with exact pins in `SOURCE_LEDGER.json`. The former
contains the latest second-order Lucas correction and the shorter q-cube
parent; the latter contains the two partial-scale charts. Their explicit
calibration uses all four fixed coefficient integers together, not merely
their elementary numerical bounds. Original licenses and notices remain.

## 2. Complete definitions

The independent variables are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The four fixed integers are `beta,K0,MC,MF`. In addition to their literal
byte specification, the retained finite coefficient recipe reconstructs
them. In particular `beta=2^590069-1`; the other ports are not independently
adjustable. For the elementary arithmetic below one uses only

    beta >= 31 odd, K0 > 0, 0 < MC < beta < MF < 2 beta.

Define h=beta J, q=h+1 and C=q-F-alpha. Choose one chart:

| Chart | Wbase | X | Y | D | Error numerator N |
|---|---|---|---|---|---|
| q3 | w | qw | q^3 s | XY | k-R-1 |
| q2 | w | qw | q^2 s | q^5 | k-R-1-q^4s |
| q1 | qw | q^2w | qs | q^6 | k-R-1-q^4s |
| lucas | w | qw | qs | 6q^6 | 6(k-R-1-q^4s)-XY^2(R+1)(R-1)(R+3) |

Here and below small fixed powers mean repeated multiplication. Further set

    k=eta+zeta, c=kY+eta, A=Y(X+1)+1,
    Delta=A^2-1, H=4A-5, v=XY^2,
    E=1+v(v+1)k^2,
    R=[h(q-F)+alpha](q^2-1)+(MC+qMF)J,
    B=(K0+Wbase)C-F,
    U=ic^2, a=Delta U^2 E, F0=1+a, G=E F0,
    f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2.

The first circuit uses chart q3 and L=V^2. The second uses chart q3 and
L=bV. The remaining three use their indicated charts and L=bV. In all cases

    M=hDH,
    Z=hD[H(n-LB)+K]-H[DB+hN],
    P=Q(Z^2-M^2GV^2)+(M^2G-Z^2).                 (2.1)

The single equation is P=0 on the stated domain. This is a complete ordinary
polynomial specification. Its literal acyclic graph and all coefficient
payloads are supplied. The quantities defined below with quotients are proof
notation only, never operations in that polynomial.

Let t=B/h, kappa=K/H, z=Z/M, and W=1+hL. Write

    N/D = rho-sigma.

For q3, rho=(k-R-1)/(XY) and sigma=0. For q2 and q1, rho=(k-R-1)/D
and sigma=s/q or s/q^2 respectively. For lucas,

    ebar=k-R-1-v(R+1)(R-1)(R+3)/6,
    rho=ebar/q^6, sigma=s/q^2.

The exact rational identities are

    P=(Q-1)Z^2-M^2G(QV^2-1),
    z=n+kappa+sigma-Wt-rho.                       (2.2)

None of these quotients is presumed integral initially.

## 3. Root extraction and the first folded index

All positive inputs satisfy q>=32, X,Y>=q, q|X,Y, k>=2, c>kY,
A>4, Delta>=3, U>=c^2, E>1, a>c and M>0. Hence f>2c and Q>c^2.
The following identities hold identically:

    f^2=1+4aF0,
    Q=Delta(f^2-1)=4Delta^2 U^2G,
    f-1=2Delta i^2c^4E.                           (3.1)

If b=0 then V=-c; otherwise |V|>=f-c>1. In particular V is never zero
and QV^2-1>0. Also G is relatively prime to both Q-1 and QV^2-1, since
Q is a multiple of G. At a zero, the first identity in (2.2) therefore
forces every prime valuation of G to be even: `G=g^2` with g>0 integral.
Since gcd(E,F0)=1, one separately has

    E=tau^2, F0=f0^2, g=tau f0.

The rational number y=|z|/g satisfies

    QV^2-(Q-1)y^2=1.                               (3.2)

The retained adjacent-coefficient Pell descent makes y integral. Here is
the needed rational-integrality argument explicitly. If y=r/m in lowest
terms, m^2 divides Q-1. For u=|V|>1, (3.2) gives
u<y<Qu/(Q-1). The norm-preserving map

    u'=(2Q-1)u-2(Q-1)y,
    y'=(2Q-1)y-2Qu

has nonzero integer first coordinate, |u'|<u, and preserves the reduced
denominator m of the second coordinate, because 2Q-1=1 modulo m.
After sign reflection, descent reaches u=1 and y=1. Thus m=1, and
z=epsilon gy is integral, epsilon=+1 or -1.

Put I=2Ug. Equations (3.1) yield

    f^2-Delta I^2=1, Q=(Delta I)^2, c^2|I, c<=I.   (3.3)

The retained signed all-index folding theorem uses (3.2), (3.3), and
V=-c modulo f. These hypotheses still hold with the new V. It gives

    c=psi_A(p),  p>=1 odd.                         (3.4)

Here psi_A is the Pell ordinate sequence with initial values 0,1 and
recurrence psi_A(j+2)=2A psi_A(j+1)-psi_A(j). The proof of the folding
statement is retained in `inherited/lucas/parent/proof_sources`; it uses
classification of the auxiliary Pell pair, odd quotient polynomials, and
reduction of an index modulo twice the strong index. It permits both signs
of V. It does not presuppose any sign of R or a transport quotient.

From E=tau^2, ordinary Pell classification also gives

    k=2psi_(2v+1)(n0), n0>=1.

At n0=1 one would have k=2, eta=zeta=1 and c=2Y+1, strictly between
psi_A(1)=1 and psi_A(2)=2A. This is impossible. Consequently

    n0>=2, k>=8XY^2+4, c>8XY^3>=8q^4, c>X, K>0. (3.5)

All statements up to this point precede the signs of B,C,R,b and V.

## 4. Low indices and signed transport with the unsquared trace

The old exclusion of main index p=3 uses only X,Y,k,c and is unchanged.
For completeness: if c=psi_A(3)=4A^2-1 and n0>=3, then k>32X^2Y^4
while c<16X^2Y^2<kY, a contradiction. Thus n0=2 and k=8XY^2+4.
Writing u=X+2-2Y gives

    eta=4Y^2(Xu+1)+8Y(X+1)+3-4Y.

For u<=-1 this is negative, using Y(X-1)>2(X+1). For u>=2 it is
greater than k. Thus u=0 or 1, and 2Y-X is 2 or 1. This contradicts
q|X,Y and q>=32. Hence p>=5 and

    c>c3:=4Delta+3.                                (4.1)

First b=0 is impossible: then (3.2) gives
y^2-c^2=(c^2-1)/(Q-1), strictly between zero and one. Therefore b is
nonzero, V has its sign, and |V|>|b|.

From a=Delta U^2E and g^2=E(1+a),

    a^2/g^2=Delta U^2*a/(1+a)>Delta U^2/2>9.

Thus a>3g, f-c>a>3g, and y<(3/2)|V|. For L=V^2 these inequalities
already imply gy<L/2.

For the bV weight classify (3.2) at the Pell parameter S=Delta I.
Its auxiliary index j is odd, since an even trace is a unit modulo S.
Index one would give |V|=1, already excluded. At index three,
|V|=4Q-3. The new, exact equations are

    f(b-4Delta f)=c-c3,  or
    f(b+4Delta f)=c+c3.                             (4.2)

Both right sides are strictly between zero and 2c<f, by (4.1). Neither
can be a multiple of f. This proves j>=5 without a sign assumption on V.
Thus |V|>=16Q^2-20Q+5>8Q^2. Since Q=Delta(f^2-1)>f^2 and c<f/2,

    |b|> (8Q^2-c)/f >8f^3-1/2 >4g.

It follows that L=bV=|b||V|>0 and gy<(3/8)L<L/2. In both weights,
therefore,

    L>0, gy<L/2, L>|b|.                            (4.3)

This is the essential signed transport estimate. The reduction has not
treated a positive variable as though it admitted arbitrary integer shifts.

## 5. Recover B and C, including all Lucas negative-rank cases

For each uncorrected chart e=k-R-1 satisfies
e<b because b-e=cT-k+1>0. Consequently rho<|b|/D. If B<=-1 then
Wt<-L. Since n,kappa are positive and sigma is nonnegative, (2.2),
z=epsilon gy and (4.3) imply

    n=epsilon gy-kappa-sigma+Wt+rho
      < L/2-L+|b|/D < 0,

as D>2. This contradicts n>0.

The Lucas chart has the same conclusion but requires a separate adverse
cubic argument. Let B_R=(R+1)(R-1)(R+3). If B_R>=0, then
rho<|b|/q^6 and the preceding argument applies. The only integers with
B_R<0 are R<=-4 and R=0. Put Pmask=(MC+qMF)J>0. The exact identity

    R=(hC+q alpha)(q^2-1)+Pmask                      (5.1)

gives C<0 in both exceptional cases.

If R=-r<=-4, then |C|>r/[h(q^2-1)]>r/q^3. In the Lucas chart
Wbase=w, so B=-(K0+w)|C|-F<=-1-w|C|, and
Wt<-(1+w|C|)L. The adverse term obeys

    delta0=v(r-1)(r+1)(r-3)/(6q^6)
            <w s^2 r^3/(6q^3).

Here b=cT+r>c and b>r. With the unsquared trace,
V=fb-c>(f-1)b. Thus for either allowed weight

    L>(f-1)r^2.

Moreover f-1=2a>s^2: indeed Delta>Y^2>=s^2 and U,E are positive.
Therefore w|C|L>delta0. Inserting this strict inequality in (2.2) gives

    n<L/2-(1+w|C|)L+|b|/q^6+delta0<0.

For R=0, one has C<=-1, b=cT>=c, and
V=fb-c>f-1 because c>1. Hence L>f-1>s^2. The adverse term is only
delta0=v/(2q^6)=w s^2/(2q^3), so again w|C|L>delta0 and the same
contradiction follows. Every integer rank has been covered.

Consequently every positive zero in every chart satisfies B>=0. Since
F>0 and K0+Wbase>0, the definition of B then forces C>0.

## 6. Recover the true main index and the inherited outer endpoint

Only now apply the authenticated mask estimate

    3q<R<q^4-2.

Together with (3.5) it gives c>2R, so b,V>0. Also c>2p by the
elementary Pell growth bound. The unchanged normalized rank lemma applied
to (3.3), (3.4) gives f=chi_A(m) with c|m and m>2p. The crucial new
residue is licensed by the last identity in (3.1):

    f=1 mod c, hence V=f(cT-R)-c=-R mod c.         (6.1)

The other residue remains V=-c modulo f. Therefore the retained signed
auxiliary-index theorem applies with exactly the same hypotheses and gives
p=R. The oddness of p makes R odd; the mask formula then implies q even
and J odd, as in the parents.

All remaining first-index, carrier, power projection, parity and rounding
arguments use only the following data, now established for the new zero:

    c=psi_A(R), E=tau^2, 0<eta<k, c=kY+eta,
    z integral, z=n+kappa+sigma-Wt-rho,
    W=1 mod h, B>=0, C>0, q even, 3q<R<q^4.

They never use the discarded squared factor in V. We detail their chart
dependencies to make this handoff precise.

For q3, integrality of z gives XY|hHe. Since q^4|XY and
gcd(q,hH)=1, this gives q^4|e. The first Pell congruence is
k=2n0 modulo 4XY^2. Monotonicity of its base versus A gives n0<R.
The bounded congruence therefore gives 2n0=R+1. The full recurrence
then gives 4XY^2|e, hence rho integral. Clearing h in the remaining
carrier yields H|hK.

For q2 and q1, integrality first gives D|(e-q^4s), hence q^4|e.
The visible first-Pell modulus is divisible by q^4 in both charts,
so again 2n0=R+1. Since gcd(H,D)=1, one already gets H|hK before
assuming rho integral. The retained uniform ratio bound and whole-product
projection force X=2^R. As q|X, q=2^m with m>=5, and R>3q>=6m
implies q^6|X. Now the full recurrence implies D|e in both charts.
The remaining carrier yields q|s for q2 or q^2|s for q1, together
with h|B. This restores q^3|Y. The native transport base is Wbase,
which is qw in q1, exactly as in the retained cofinal proof.

For lucas, Section 5 of `inherited/lucas/PROOF.md` applies verbatim.
At r0=(R+1)/2 the expansion

    2psi_(1+2v)(n)=2n+8v*binom(n+1,3)+32v^2 Z_n

has Z_n a nonnegative integer. It proves ebar integral, then
q^6|(ebar-q^4s) and q^4|ebar. With d=2n0-R-1 the exact identity

    6(ebar-d)=v d[(2n0)^2+(2n0)(R+1)+(R+1)^2-4]
               +192v^2 Z_n0

first yields q^3|d and then q^4|d, including primes 2 and 3.
Because n0<R and |d|<R<q^4, d=0. Only then does the expansion give
q^6|ebar and nonnegative integral rho. The original divisibility now
gives q^2|s, so sigma is integral and clearing h gives H|hK.
No factor 6 is improperly canceled modulo q.

In every chart the retained uniform ratio estimate with R=2r+1 gives
Y>X^r/3 and X^(r+1)<H. The universal projector and its strict bound
on the entire divisible product imply X=2^R and integral positive
kappa. The remaining carrier gives h|B, since W=1 modulo h.
Thus the exact native outer endpoint has

    X=2^R, q^3|Y, t=B/h>=0 integral,
    (K0+Wbase)C-F=t(q-1).

The fixed-minus parity theorem and half-binomial rounding are precisely
those in the parents. They reconstruct fresh original-source witnesses at
the source base Y(X+1)+2, not at the new auxiliary base A. The whole
indexed tuple then yields a finite syntactic ZFC refutation. This last
step uses the actual retained native/refutation calibration, not a theorem
for arbitrary coefficient ports satisfying an interval box.

## 7. Constructive positive completeness

A finite syntactic refutation supplies the corresponding parent's canonical
outer data. In particular R=3 modulo 4, R>3q, X=2^R, q^3|Y,
t=B/h>=0 integral, c=psi_A(R), and the first Pell witnesses with
0<eta<k. Choose the same positive seed strong pair (f0,I0), with
c^2 tau|I0, and set i=I0/(c^2 tau). Doubling it gives

    f=2f0^2-1=1+2a, I=2f0I0=2Ug.

The canonical positive auxiliary pair Vstar,y in the parent satisfies

    Vstar=f^2(c T_old-R)-c,
    Q Vstar^2-(Q-1)y^2=1,
    T_old=(Vstar+c+Rf^2)/(cf^2)>0 integral.

Keep this pair fixed. Define instead

    T_new=(Vstar+c+Rf)/(cf)
         =f T_old-((f-1)/c)R.                     (7.1)

It is an integer because c|(f-1) identically; equivalently, the parent's
stronger auxiliary congruence and gcd(c,f)=1 give divisibility by cf.
It is strictly positive because Vstar,c,R,f are positive. The formula
proves Vstar=f(c T_new-R)-c exactly. This positivity argument is necessary:
an arbitrary inverse shift of a positive input would not suffice.

The same outer choices give integral kappa>0 and rho>=0. For q3,
sigma=0; for the other charts sigma=Y/q^3 is a positive integer and
sigma<=Y. The canonical source bounds give kappa<Xc and
f0>(A-1)I0>2Xc, hence g=tau f0>kappa+sigma. With the new b and its
new chosen L, set

    n=gy+(1+hL)t+rho-kappa-sigma.                  (7.2)

This is an integer and is strictly positive. All independent coordinates
have therefore been constructed positively; the new carrier has z=gy and
the final polynomial vanishes. This is a direct existence construction.
It does not claim a bijection between the full old and new positive zero
sets, nor require an arbitrary new zero to have its auxiliary b divisible
by f.

Sections 3--7 prove both existential directions, entirely without assuming
that a refutation exists or does not exist.

### 7.1 An explicit polynomial map from every old positive zero

There is also a direct algebraic completeness map. Define the polynomial
d=2Delta i^2c^3E, so f=1+cd. For any old assignment put

    T_new=f T_old-dR.

Then b_new=cT_new-R=f(cT_old-R)=f b_old, and consequently
V_new=f b_new-c=f^2 b_old-c=V_old as a free polynomial identity.
For the V-squared weight retain n_new=n_old. For the bV weight put

    n_new=n_old+(f-1)L_old B, L_old=b_old V_old.

As L_new=f L_old, this gives
n_new-L_new B=n_old-L_old B. Every other carrier term and final norm
term is unchanged, so the complete new polynomial pulls back to the complete
old polynomial under this explicitly polynomial map.

At every old positive zero the retained parent proof gives R<c/2,
B>=0 and b_old,V_old>0. Thus T_old>=1 implies
T_new>f-(f-1)/2>0; and n_new>=n_old>0. This proves completeness
directly for the whole parent positive zero set. It is a map from old zeros
to new zeros, not an assertion that every new zero has an integer inverse.
The proof above still supplies the independently necessary soundness of all
new positive zeros.

## 8. Exact degrees and the scope of finite verification

Put q0=beta J, k0=eta+zeta, C0=q0-F-alpha, and
B0=k0 s T-q0^2(q0-F). Complete highest homogeneous parts are

    [P75]_402 =  2^10 q0^242 w^32 s^70 i^12 k0^40 T^4 C0^2,
    [P76]_352 = -2^8  q0^216 w^28 s^62 i^10 k0^34 T^2,
    [P79]_290 = -2^8  q0^158 w^26 s^60 i^10 k0^34 T^2,
    [P80]_258 = -2^8  q0^126 w^26 s^58 i^10 k0^32 B0^2,
    [P87]_232 = -9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0^2.

These are whole top components, not evaluations along one ray. They are
nonzero at the actual beta>0; e.g. the last has coefficient
-9*2^10 beta^100 at J^100 w^26 s^60 i^10 eta^34 T^2.
The polynomial B0 records the degree tie between cT and R in the
q-linear charts. Dropping that tie would give an incorrect full top form.

For the principal Lucas chart the exact degrees of a,f,Q,G,b,V,M,Z
are 36,36,80,50,4,40,11,57. The unique dominant term is
-Q M^2 G V^2 of degree 232. The term QZ^2 has degree 194.
Every intermediate top form is independently propagated by the checker.

`verify.py` checks the complete graph topology and liveness, all unknowns
and fixed ports, exact polynomial cuts covering every actual gate, the full
parent/child gate relation, every coefficient byte, source-file hashes,
each complete highest homogeneous part, and targeted actual operator
corruptions. Its expected formulas are independent of the producer. Its
sparse arithmetic helper is retained with attribution. `build.py --check`
reconstructs every new graph byte for byte from frozen parent data.

No checker searches for a consistency witness or infers an unbounded theorem
from finitely many test points. The unbounded proof above and its named
inherited interfaces are separate from these finite algebraic checks.

## 9. Further question

The low auxiliary index bound is stronger than the transport proof needs.
It also gives an absolute bound for L=b^2: from |b|>8f^3-1/2, g<f/2 and
|V|<f|b|+c<(3/2)f|b| one gets gy<(9/8)f^2|b|<b^2/2.
The ordinary absolute transport estimate therefore survives. The negative
Lucas-rank argument requires a separate adverse-term estimate because b^2
no longer contains the factor f-1 used in Section 5. That estimate is not
provided here. Consequently no b-squared
endpoint is asserted here. The five delivered equations all use their
explicitly proved V-squared or bV weights.

Other useful next questions are whether this explicit trace can reduce the
large-degree nine-positive constructions, and whether a trace-linear
residue can simplify signed compact constructions without adding a sign
assumption. Those are research questions, not established endpoint claims.

