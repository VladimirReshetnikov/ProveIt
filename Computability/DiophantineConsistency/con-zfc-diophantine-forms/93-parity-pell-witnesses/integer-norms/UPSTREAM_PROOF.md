# Quotient compression and a separated rational norm

## 1. Results and comparison boundary

This component specifies four ordinary polynomials with fixed integer
coefficients. Every coordinate below ranges over **all integers**.

| Packet | Unknowns | Zero-set residuals | Exact degree | Literal binary operations |
|---|---:|---:|---:|---:|
| `integer23_degree10` | 23 | 11 | 10 | 131 |
| `integer17_degree88` | 17 | 5 | 88 | 114 |
| `integer16_degree192` | 16 | 4 | 192 | 134 |
| `integer16_degree184` | 16 | 4, combined by a unit product | 184 | 135 |

The complete polynomials are given by `equations/*.json`. The first three
are sums of squared residuals. The fourth uses the positive unit-product
finalizer in Section 8.1. Ordered polynomial registers are
abbreviations, not additional existential variables. Fully inlined expressions
and literal binary arithmetic DAGs are also supplied. All powers have fixed
nonnegative integer exponents; no division, variable exponent, bounded
quantifier, proof-search oracle, or unnamed witness occurs in a polynomial.

The inspected repository is ProveIt at
`c1a102936aca437e9999530a0111e6ddab56dc6d`. Its already delivered incoming
packages include a 24-integer degree-10 equation and a 19-integer degree-88
equation. Thus the first and second rows improve those variable counts by
one and two, respectively, without changing degree. The last two rows trade a
higher degree for one further integer coordinate. They do not supersede the
repository's fewer-variable, much higher-degree Jones/Sun reductions.
In particular this is not a claim to the minimum possible variable count,
degree, operation count, or description length. The 17-variable DAG has five
more operations than the incoming 19-variable DAG's stated 109.

The new quotient step combines two integer congruence witnesses into one.
The new root step merges an ordinary square root with a rational Pell root;
an exact separation identity and rational Pell descent recover both original
integer roots. The 23-variable form combines compatible reductions already
present separately in the incoming packages.

Composing the new reductions proved here with the explicitly named ordinary
correctness theorems of the source gives, for each listed polynomial P,

    ZFC proves: [there is no integer tuple x with P(x)=0] iff Con(ZFC).

Here Con(ZFC) uses the repository's fixed recursive syntactic refutation
predicate. The inherited native/compiler, signed Pell, and K215/refutation
calibration theorems are dependencies; their complete semantic proofs are
not re-established by finite code checks. This component supplies no new
end-to-end Lean/Rocq or encoded internal-ZFC certificate. It neither asserts
unsolvability nor assumes or proves consistency. Its claim is the equivalence.

## 2. Six completely fixed coefficients

Use the coherent source-34 tuple `mixed-parity-unrounded-1064921`:

    beta = 2^1064921 - 1,
    K0 = its literal native K coefficient,
    MC = its literal low-mask coefficient,
    MF = its literal high-mask coefficient already shifted by beta,
    cone_A = 2^1113,
    cone_B = 2^666104.

The four native coefficients have their actual compressed minimal
little-endian integer bytes in `coefficients/payloads/`; the two guard
coefficients are supplied in the same format. A byte string b_0,...,b_(l-1)
denotes the integer sum b_i*256^i. `coefficients/BINDING.json` specifies every
raw SHA-256 and length. The six raw encodings total 615,883 bytes. Hashes
authenticate these bytes; hashes themselves are not substituted for coefficients.

The finite source-34 builder, literal machine table, and ordered 943-tile list
are retained under `coefficients/recipe/`. The native mathematical coefficient
proof is retained under `upstream/`. All six coefficients are positive, and
the authentic tuple satisfies

    beta >= 17, beta = 1 (mod 3),
    0 < MC < beta < MF < 2 beta, K0 >= 0,
    cone_A >= 2, cone_B >= 2.

No coefficient depends on the result of searching for a refutation. Do not
mix this tuple with the distinct compact44, original31, or H2082 tuples, and
do not shift MF a second time.

## 3. Two elementary guard facts

Write

    Pos(p1,p2,p3) = 1+p1^2+p2^2+p3(p3+1).

Every integer value of Pos is positive. Conversely every positive integer
n is represented: the three-square theorem represents 4n-3, which is 1
modulo 4 and never of the forbidden form 4^a(8b+7). Exactly one square is
odd and two are even. Writing them as (2p3+1)^2,(2p1)^2,(2p2)^2 proves the
claim after division by four.

For arbitrary integers x,y the source-68 nearest-square lemma is

    x>0 and y>0
      iff exists t,p1,p2,p3:
       xy-(t^2-x-y+1)^2 = Pos(p1,p2,p3).             (3.1)

For soundness the positive right side gives xy>0. If both x and y were
negative, the square on the left would exceed xy. For completeness put
N=x+y-1 and m=floor(sqrt(N)). There is a neighboring square t^2 with
|t^2-N|<=m. If N is not a square, m^2<N; if it is a square choose t^2=N.
Thus (t^2-N)^2<N<=xy, using xy-N=(x-1)(y-1)>=0. Represent the positive
difference by Pos. The square root is used only to choose witnesses in
this proof, never as a polynomial operation.

For q,F,C put

    d=(cone_A*F)(cone_B*C)-(q-cone_A*F-cone_B*C)^2,
    alpha=q-F-C.

If d>0, then F,C,alpha,q have the same strict nonzero sign. Indeed put
U=cone_A*F and B=cone_B*C. From UB>(q-U-B)^2, U and B have a common
nonzero sign and

    |q-U-B| < sqrt(UB) <= (|U|+|B|)/2.

Therefore q has their sign and

    |q| > (|U|+|B|)/2 >= |F|+|C|.

This forces alpha to have that sign as well. This signed implication is
universal. Its converse is not asserted. For the source's canonical accepting
witnesses, source71 separately proves the calibrated estimates
q/2<=cone_A*F<4q/5 and q/2<=cone_B*C<3q/5, which ensure d>0. That
upstream existence restriction is inherited unchanged here.

## 4. The 17-integer polynomial

The seventeen independent coordinates are

    J,C,z,f,h,r,v,w,tau,nu,gamma,T,c,t,p1,p2,p3.

Define only polynomial abbreviations:

    J0 = 3J+1,             q = beta*J0+1,
    W = 4(3w+1),           X = qW,
    Y = (2v+1)q^3,         E = XY,
    a = (X+1)Y,            H = 4a+3,
    Delta = a^2+H,
    F = (K0+W)C-(q-1)z,    alpha = q-F-C,
    R = (q-F)(q^3-q)-C(q^2-1)+(MC+q MF)J0,
    k = R+1+hE,            eta = c-Yk,       zeta = k-eta,
    I = (2r+1)c^2,         V = c(Tf-1)-Rf^2,
    m = XY^2,              B0 = mk,         s0 = X+gamma H,
    d = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Z = eta zeta.

Its five residuals are

    A1 = tau^2+(2tau-k)B0-1,
    A2 = 2ac s0+s0^2-Hc^2-1,
    A3 = I^2-Delta(f^2-1),
    A4 = (V+nu)^2-I^2 nu(2V+nu)-1,
    A5 = dZ-(t^2-d-Z+1)^2-Pos(p1,p2,p3).

The equation is P17=A1^2+A2^2+A3^2+A4^2+A5^2=0.

The first and fourth rows are centered Pell norms. Defining the restored
roots tau_old=tau+B0 and y_old=nu+V gives the exact identities

    A1 = tau_old^2-m(m+1)k^2-1,
    A4 = I^2(V^2-y_old^2)+y_old^2-1.                (4.1)

Likewise, D=ac+s0 restores A2=D^2-Delta c^2-1. The transport equation is
identically zero by the definition of F. The packing expression for R is
the exact original expression after substituting alpha=q-F-C.

## 5. Combining the two congruence witnesses

The signed native source has two simultaneous integer identities

    V=of-c,                 V=jc-R.                  (5.1)

Assume c!=0 and c divides f^2-1. Then (5.1) is equivalent, after projection
of its private witnesses j,o, to the single-coordinate expression

    V=c(Tf-1)-Rf^2,    T an arbitrary integer.        (5.2)

Here no f-divisibility restriction is imposed on T.

For the forward direction, c divides of+R by (5.1), and

    f(of+R)-o(f^2-1)=o+Rf.

Hence T=(o+Rf)/c is an integer. Multiplying (5.2) out proves that its value
is exactly V. For the reverse direction let b=(f^2-1)/c, an integer, and set

    o=cT-Rf,                j=Tf-1-Rb.               (5.3)

Then V+c=fo and V+R=cj. This is a bijection on the quotient witnesses when
c!=0, conditional on the proved divisibility. The rational expressions in
this witness-restoration proof introduce neither division nor a new b
coordinate into P17.

### Why the required divisibility is available before using (5.1)

It would be circular to invoke a theorem whose proof first uses the missing
congruences (5.1). The relevant source orientation proof is organized so that
its strong-rank bootstrap precedes the auxiliary congruence step. We record
that order explicitly.

At a P17 zero, (3.1) gives d>0 and eta*zeta>0. The determinant soundness
lemma makes F,alpha,C share q's nonzero sign. With Q=|q|, the source's
sign-free fixed-mask estimate yields

    Q>=16,                 Q(Q^2-1)<R<Q^4-2.

The integer W=12w+4 is nonzero with |W|>=4; 2v+1 is odd and nonzero.
Thus U=|X|>=4Q, Z0=|Y|>=Q^3, and M=|E|>=4Q^4>3R+1. The positive
product eta*zeta implies that eta,zeta have a common sign, so K=|k|>=2
and 0<|eta|<K. Consequently

    K(Z0-1)<|c|<K(Z0+1).                             (5.4)

In particular c!=0. Put B=|a+2| and P=|2XY^2+1|. These satisfy P>B>=2,
B>R, and |c|>K. Classifying the restored first and main norms in (4.1)
gives positive indices n0,p such that

    K=2 psi_P(n0),           |c|=psi_B(p),            p>n0.

The sign-uniform recurrence modulo M, together with k=R+1+hE, gives
one of the two signed congruences +/-2n0=R+1 mod M. The positive branch
implies n0>=(R+1)/2. The negative branch implies n0>R. In either case
p>n0>=24. Ordinary Pell growth therefore gives

    |c|>B(B^2-1)^2,         |c|>2p,       |c|>2R.

These are exactly the inputs to the ordinary strong-rank lemma applied to
A3, since 2r+1 is nonzero. Before any use of (5.1), it supplies an index
l with

    |f|=chi_B(l),           p divides l.

The standard Pell divisibility identity implies
psi_B(p) divides psi_B(l). Since
f^2-1=(B^2-1)psi_B(l)^2, it follows in particular that

    c divides f^2-1.                                  (5.5)

This is the required pre-auxiliary divisibility. The full source statement
also supplies |c| divides l and l>2p, but those extra conclusions are not
needed to justify the new quotient. The exact inherited proof is retained
as `upstream/ORIENTATION_PROOF.md`, Sections 3--4.2. Its auxiliary-congruence
step begins only in Section 4.3. The quotient identity itself also appears
as an interface in the repository's `NATIVE_PELL_STEP_DOWN.md`; the new use
here is to delete one existential integer from the finished fixed equation.

### Soundness and completeness of P17

For soundness, recover b and hence j,o by (5.3), then restore all monic
coordinates and both centered roots. Every arithmetic row of the incoming
37-variable affine quartic now vanishes. The two positive guard arguments
d and eta*zeta have Pos representations, so restore the two old private
triples. This gives a zero of that authenticated source equation, which has
the inherited finite-refutation equivalence.

For completeness, take any zero of the same 37-variable source. Its existing
strong bootstrap supplies (5.5). Form T=(o+Rf)/c and change from alpha to C.
The source transport equation gives the displayed definition of F. Forget
the monic coordinates, set tau=tau_old-XY^2 k and nu=y_old-V, and use (3.1)
on the already positive d,eta*zeta to choose the four joint-guard variables.
This is a P17 zero. No fresh restriction on canonical computation witnesses
is introduced by either new quotient or transport step.

The finite auditor restores every arithmetic row of the literal 37-variable
packet. Four are exactly the four new arithmetic residuals; one is plus or
minus R(cb-f^2+1), exposing the sole use of (5.5); all remaining arithmetic
rows are polynomial identities. This verifies the transcription and the
complete arithmetic interface, without pretending to prove (5.5) by sampling.

## 6. A rational two-root norm with integer recovery

The following lemma is independent of the native compiler.

**Lemma.** Let A,Q,S,V be integers with A>0, Q>1, and S^2>A. Set
delta=Q-1 and Bnum=S^2(QV^2-1). Then

    exists n in Z:
      [delta(n^2-A)-Bnum]^2-4 delta A Bnum=0          (6.1)

is equivalent to the existence of integers u,y satisfying

    u^2=A,                 QV^2-(Q-1)y^2=1.         (6.2)

More precisely every zero of (6.1) recovers such integers u,y, and every
pair in (6.2) gives a zero by n=u+Sy.

If V=0 then Bnum=-S^2<0, so the left side of (6.1) is a square plus the
strictly positive integer 4 delta A S^2. Therefore any zero has |V|>=1.
Put B=Bnum/delta, a rational number. Then B>=S^2>A. Divide (6.1) by
delta^2 to obtain

    (n^2-A-B)^2=4AB.

Here n cannot be zero, since that would force A=B. The identity

    (n^2+A-B)^2-4n^2 A=(n^2-A-B)^2-4AB

shows that u=(n^2+A-B)/(2n) is rational and u^2=A. Thus u is an integer:
a rational number with integer square has denominator one in lowest terms.
The number s=n-u is rational with s^2=B. Since S!=0, y=s/S is rational and
satisfies the second equation of (6.2). The following descent makes y an
integer. This proves soundness; completeness is the direct norm factorization.

### Rational Pell descent, with attribution to source69

For any integer Q>1 and integer V, a rational y satisfying
QV^2-(Q-1)y^2=1 is an integer. Write y=a/d in lowest terms with d>0.
The norm implies d^2 divides Q-1. Neither V nor y is zero. Change signs to
make V,y positive. If V=1, then y=1. If V>1, put

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The first coordinate is integral because d divides Q-1. The determinant-one
identity preserves QV^2-(Q-1)y^2. The denominator of y' in lowest terms is
still exactly d, because 2Q-1=1 mod d and gcd(a,d)=1. Also y>V and
QV>(Q-1)y, whence -V<V'<V. The preserved norm excludes V'=0. Replace
V',y' by absolute values and use strong induction on V to reach V=1 while
preserving d. At that point d=1. The source69 proof is retained and credited;
the new contribution is its use with the explicitly separated norm (6.1).

## 7. The 16-integer polynomial

Delete tau,nu from the P17 coordinates and add one unrestricted integer n.
Keep every P17 register except those involving these two deleted roots.
Define

    A0=1+m(m+1)k^2,          S=k(2m+1),
    delta=I^2-1,
    L=delta[n^2+2n(B0+SV)+2B0SV-mk^2-1]+S^2(1-V^2),
    N=L^2-4 delta A0 S^2(I^2V^2-1).

The equation is

    P16 = A2^2+A3^2+A5^2+N^2 = 0.                    (7.1)

These are four squared integer-polynomial residuals in exactly sixteen
integer unknowns. The polynomial N is the numerator in (6.1) with
Q=I^2 and the shifted integer coordinate

    n_total=n+B0+SV.

Indeed the exact identity

    delta(n_total^2-A0)-S^2(I^2V^2-1)=L

is obtained by cancellation of the two leading V^2 terms. The complete
literal identity is checked separately in `verify.py`.

### Guard-only separation: there is no circular Pell assumption

At a P16 zero, A5=0 first gives d>0 and eta*zeta>0. As in Section 5,
Q0=|q|>=16, |W|>=4, |Y|>=Q0^3, |k|>=2, and

    |c|>|k|(|Y|-1)>=2(16^3-1)>1.

These facts use only the guard, coefficient definitions, and integer affine
residue restrictions. They use neither the missing first norm nor the missing
auxiliary norm. Hence |I|=|2r+1|c^2>1, so Q=I^2>1. Also
|m|=|X|Y^2>1, whence m(m+1)>0 and A0>0. Finally

    S^2-4A0 = k^2-4 >= 0.                           (7.2)

Thus S^2>=4A0>A0 and all hypotheses of Section 6 hold before extracting
either missing root. This exact identity replaces any need to compare two
unknown Pell ranks or to assume either desired root is already integral.

Apply the lemma to N=0. It gives integers tau_old,y_old with
tau_old^2=A0 and I^2V^2-(I^2-1)y_old^2=1. Set

    tau=tau_old-B0,        nu=y_old-V.

The two omitted P17 rows now vanish, while its other three rows are
unchanged. Thus a P16 zero yields a P17 zero and then a finite refutation.

Conversely any P17 zero has the two restored integer roots in (4.1). Choose
n=tau+S*nu; then n_total=tau_old+S*y_old and the norm vanishes. This proves
existence equivalence on all integer assignments. No additional canonical
tableau or divisibility restriction is used in this root compression.

## 8. Exact degrees and coefficient witnesses

All degree statements count only the listed unknowns. The six fixed integer
ports have degree zero. In P17, the degrees of X,Y,E,a,R,k are respectively
2,4,6,6,5,7. Both eta and zeta have degree 11. The determinant d has degree
4 after the transport pivot. The five residual degree upper bounds are

    24,14,14,14,44.

Only the joint guard reaches degree 44. Its leading part is -eta_top^4, where

    eta_top=-2^4*3^8*beta^7*h*J^7*w*v^2.

Therefore

    [h^8 J^56 w^8 v^16] P17 = 2^32*3^64*beta^56 > 0.

This proves exact degree 88 after specializing to the authentic fixed tuple,
not just a formal gate-degree bound.

For P16, deg m=10, deg S=17, and deg V=7. The displayed L has degree 48;
its leading part is -S_top^2 V_top^2. The other term in N has degree at most
94, so N has degree 96 with leading part S_top^4 V_top^4. In particular

    S_top=2^8*3^13*beta^11*h*J^11*w^2*v^3,
    V_top=f^2(324*beta^3*J^3*w*C-81*beta^4*J^4*z).

The degree-192 coefficient with no C factor is

    [h^8 J^120 w^16 v^24 z^8 f^16] P16
       =2^64*3^136*beta^120 > 0.

The other three squared residuals have degrees at most 28,28,88. Hence the
exact degree is 192. The centering in n is substantive: the direct uncentered
weighted norm would give the larger upper degree 216.

The finite verifier computes exact homogeneous components, including possible
leading cancellations, and verifies both displayed coefficient formulas. It
never treats an unverified gate-degree bound as an exact polynomial degree.

### 8.1. A positive unit-product finalizer lowers 192 to 184

Put G=A2^2+A3^2+A5^2 and retain N from Section 7. Define

    P16_unit=G+N+GN=(1+G)(1+N)-1.

For every integer assignment G>=0. Thus if P16_unit=0, the positive
integer 1+G multiplies the integer 1+N to give 1. Necessarily G=0 and N=0.
The converse is immediate. This is an exact integer zero-set equivalence
with P16; no sign or congruence restriction on N is required.

The degree is 88+96=184. The preceding leading forms give

    [h^12 J^116 w^16 v^28 z^4 f^8] P16_unit
       =2^64*3^132*beta^116 > 0.

The circuit uses the expanded form G+N+GN to share G and costs 135
binary operations, one more than the degree-192 sum-of-squares control.
Both literal polynomials are retained; the degree-184 version is the
preferred sixteen-variable endpoint when degree has priority over that
one operation.

## 9. Twenty-three unrestricted integers at degree ten

This companion has independent coordinates

    J,F,alpha,z,f,h,r,v,w,tau,eta,zeta,nu,gamma,o,j,E,a,I,t,p1,p2,p3.

Here the names F,alpha,E,a,I are coordinates rather than the corresponding
P17 expressions. Definitions shared with P17 retain their meanings where
applicable, but now set

    J0=3J+1, q=beta J0+1, W=4(3w+1), X=qW,
    Y=a-E, k=eta+zeta, c=Yk+eta, V=fo-c,
    C=q-F-alpha, H=4a+3, Delta=a^2+H,
    B0=E(c-eta), s0=X+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J0.

The determinant d, Z=eta*zeta, Pos, and joint guard A5 have the same formulas.
The eleven residuals are

    a-E-(2v+1)q^3,
    E-X(a-E),
    tau^2+(2tau-k)B0-1,
    2ac s0+s0^2-Hc^2-1,
    k-1-hE-R,
    (K0+W)C-(q-1)z-F,
    V+k-1-cj-hE,
    I-(2r+1)c^2,
    I^2-Delta(f^2-1),
    (V+nu)^2-I^2 nu(2V+nu)-1,
    A5.

Their sum of squares is P23. It is obtained directly from the incoming
37-integer affine quartic: replace its six private guard coordinates by
four joint-guard coordinates; translate its first and auxiliary roots; then
delete the twelve monic coordinates N,X,L,C2,F2,Baux,g,Delta,D,P,c,V.
The source coordinate restorations are

    N=q^3, X=qW, L=q^2-1, C2=c^2, F2=f^2, Baux=I^2,
    g=nu(2V+nu), Delta=a^2+4a+3, D=ac+s0, P=k+B0,
    c=(a-E)k+eta, V=fo-c,
    tau_old=tau+B0, y_old=V+nu.

Every map is integral and polynomial. The monic deletions and root shifts
are bijections of the arithmetic zero sets; only the private positivity
witnesses use existential extension. The verifier checks every one of the
22 old arithmetic rows exactly: twelve become identities, and the remaining
ten match the ten displayed arithmetic rows once each, up to sign. It also
checks the literal arguments of both old guards.

The eleven residual degrees are at most 4,3,4,5,4,2,3,5,4,5,4. Only the
I definition contains r, and therefore

    [r^2 a^4 eta^4] P23 = 4.

This proves exact degree ten uniformly in every fixed coefficient. The
count 23 is 37-6+4-12. This composition combines the incoming residue
orientation with the incoming paired root translations; neither input on
its own has this 23-variable degree-10 endpoint.

## 10. Reproduction and evidence

Run, with Python 3.10 or later and no third-party dependencies:

    python3 build.py
    python3 verify.py
    python3 -O verify.py

The generator emits all four literal packets, fully inlined residuals, and
binary DAGs. The separate verifier does not import it. Exact sparse integer
polynomial arithmetic verifies the local identities, every retained arithmetic
source row, and the selected highest-degree coefficients. Exact canonical
term-algebra comparison binds the DAG to the displayed formulas. Liveness,
topology, all variable counts, and all scalar operations are audited. Actual
fixed integer bytes and their required bounds are authenticated.

The signed modular evaluations use actual coefficient values and are labeled
diagnostics. Small rational-root exercises are likewise diagnostics; Section 6
is the proof. None of these programs searches for a ZFC refutation.

The ordinary Pell interfaces used in Section 5 are unbounded mathematical
dependencies, not finite test results. The final consistency equivalence
likewise inherits the native compiler and calibrated machine endpoint. An
external standard-model theorem and a proof within a specifically encoded
object-language ZFC system are different certificates. This component does
not remove the repository's open end-to-end formalization obligations.

## 11. Attribution

The calibrated determinant is from source71; nearest-square joint positivity
is from source68; residue orientation is from source70; rational Pell descent
is from source69. The paired root translations and transport pivot are already
present separately in the reviewed incoming packages. The strong quotient
identity is already exposed as a repository Pell interface. The contributions
here are its explicit variable-removing use at the finished signed endpoint,
the separated weighted rational norm and its exact composition, and the
23-variable degree-10 synthesis. No external historical-priority claim is made.
Independent AI-assisted checks are not external human peer review.

All input filenames, retained byte hashes, and the reviewed snapshot are in
`SOURCE_PINS.json`. Inherited source notices and licenses are preserved under
`licenses/`. New contribution text and code may be used under the repository's
MIT No Attribution terms, subject to those preserved third-party notices.
