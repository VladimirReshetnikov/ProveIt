# A ten-integer companion using batched quadratic coefficient tests

## Result

The explicit division-free polynomial in `generated/signed10_b2.json` has
exactly ten unrestricted integer variables, exact total degree **449,607,016**,
and an evaluator with **773 binary arithmetic operations** (223 additions,
25 subtractions and 525 multiplications). It uses 17 nonliteral fixed leaves.
Every fixed leaf has a finite recipe from the supplied complete native tuple;
none is an unspecified enumeration index or an extra unknown.

Its lack of integer zeros is provably equivalent in ZFC to Con(ZFC), using
the inherited calibrated 31-variable positive quadratic system and the
explicit Lucas bridge of Sun 2026, together with source 31's previously proved
coprime square merger, quintic divisibility merger and final norm. The new
step compresses all 22 quadratic residual tests directly, before taking any
sum of squares. This avoids the quartic base-5 positional encoding entirely.

At the pinned source 31 baseline, the ten-integer equation has degree
589,042,901,992,797,851,562,527,064 and 1,442 operations. This companion
reduces the degree by a factor exceeding 10^18 and the operation count by 46.4%.
The independently developed nine-natural-variable companion uses the same
quadratic source compression with the Jones ratio interface.

This is an ordinary mathematical proof and exact finite certificate, not
an end-to-end Lean/Rocq theorem. Sun's ten-integer bridge is a 2026 preprint;
the nine-natural-variable companion does not depend on that preprint.

## 1. Fixed quadratic source and coefficient recipes

Let r_0,...,r_21 be the 22 quadratic residuals of source 31's positive system,
shifted from positive coordinates x_i to n_i=x_i-1>=0. Its 31 natural
coordinates have the fixed order recorded in `data/parent_quartic31.json`.
The fifth original residual is E-X(a-E), so at the all-one original vector
it equals 1. Consequently a simultaneous zero n is nonzero.

The complete four-port tuple is the new
`wang943-complemented77-length8807-prime56611` binding. All four compressed
payloads and `../compiler/COEFFICIENT_BINDING.json` are supplied;
MF means its already shifted MF_source port. No coefficient is imported
from a different tuple.

Write

    r_j(n)=sum_(|alpha|<=2) p_(j,alpha) n^alpha,
    c_(j,alpha)=(2-|alpha|)! product_i alpha_i! p_(j,alpha).

There are 136 nonzero symbolic weighted coefficient records. A record is
an integer polynomial in the four positive fixed ports. Let C be one plus
the sum, across all records and all their coefficient monomials, of
`abs(coefficient)*2^(sum exponent_i*bit_length(port_i))`.
Then every |c_(j,alpha)|<C. The supplied data give

    bit_length(C)=1,359,515.

Choose the explicit even exponent and constant

    e_beta=1,359,528,       beta=2^e_beta.

Thus beta>2048C and beta=1 modulo 3. `data/constants_b2.json` specifies every
record and the bound recipe, and the verifier checks the actual four-port
payloads against that recipe. The large constant beta is only 169,942 bytes
when written as an unsigned binary magnitude, and compresses to a few
hundred bytes. It is entirely independent of the existence of a ZFC proof.

## 2. Pair-sum positions and isolated target digits

The 32 positions, including the zero position for the constant term, are

    0,10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,
    371,374,382,494,499,525,566,578,610,647,681,685,741,777,783,799.

All 528 unordered pair sums, including repeated entries, are distinct.
This is exhaustively checked in the artifact. Let a_1,...,a_31 be the
positive entries in order, and define

    M=799,        d=4M+1=3197,        H=22d=70334,
    e(alpha)=sum_i alpha_i a_i.

Zero padding shows that e is injective for |alpha|<=2. Define

    E_j(T)=sum_(|alpha|<=2) c_(j,alpha) T^(2M-e(alpha)),
    E(T)=sum_(j=0)^21 T^(jd) E_j(T).

All exponents are nonnegative. For any n_i>=0, put c(T)=1+sum_i n_i T^a_i.
The coefficient of T^(jd+2M) in c(T)^2E(T) equals 2r_j(n).

To prove this, c(T)^2 has degree 2M, and E_j has degree at most 2M.
The contribution from row j lies wholly within [jd,jd+4M], and these
22 intervals are disjoint because d=4M+1. Within one interval, equality
of exponents requires equal pair sums and hence the same alpha. Its
multinomial coefficient cancels the factorial weight in c_(j,alpha),
leaving 2p_(j,alpha)n^alpha. No other row reaches that target.

## 3. All source polynomials

There are two source unknowns f,g. Define

    b=1+3f,                   B=beta*b^2,
    ell=sum_(i=1)^31 B^a_i,
    lambda=sum_(t=0)^(H-1) B^t,
    Zmask=sum_(j=0)^21 B^(jd+2M),
    N0=B^(M+1),               N1=4B^H,
    N=N0*N1=4B^71134,
    mask=N0-1-(b-1)ell,
    Jcode=2(1+g)^2 E(B)+B lambda,
    Scode=g+N0*Jcode,
    Tcode=mask+N0*(B-2)Zmask,
    Rcode=(Scode+Tcode+1)N+Tcode+1,
    X=(N-1)Rcode,             Y=N^2,
    Ccap=bB^M.

These are literal integer polynomials. Every exponent and every summation
limit is a displayed fixed integer. The DAG expands powers by repeated
squaring, sums by sparse Horner evaluation and geometric identities, and
shares repeated arithmetic. There are no variable exponents or divisions.

## 4. Proof of the source interface

### 4.1 Size and sign bounds before assuming a power of two

Suppose f!=0, b is a square, and 0<=g<2Ccap. Since b=1+3f, one has f>0
and b>=4. Then B=beta*b^2>2048Cb^2, so B>4b.

The highest exponent in E is H-2M-1. Every coefficient has absolute
value <C, and different blocks/exponents do not collide. Hence

    |E(B)|<2C B^(H-2M-1).

Moreover 1+g<=3bB^M, so

    |2(1+g)^2E(B)|<36Cb^2 B^(H-1)<B^H.

The baseline satisfies

    B^H<=B lambda<2B^H.

Therefore 0<Jcode<3B^H<N1. Also g<N0. The base-B digits of mask are
B-b at the selected positions a_i and B-1 elsewhere up through M; thus
0<=mask<N0. Since the highest target exponent is H-2M-1, the positive
integer (B-2)Zmask is <N1. Hence

    0<=Scode<N,             0<=Tcode<N.

Consequently Rcode>=N+1 and X>=N^2-1>3b, while Y=N^2>max(b,256).
Furthermore b=1 mod 3 and beta=1 mod 3 imply B=1 mod 3 and N=1 mod 3,
so 3 divides X. These are precisely the size and divisibility hypotheses
needed for the downstream Lucas bridge.

### 4.2 Binomial divisibility is a simultaneous carry test

Now suppose additionally that b is a power of two. Then B,N0,N1,N are
powers of two. Sun 2021 Lemma 2.2, with p=P=2, gives

    N^2 | binomial(2X,X) iff tau_2(Scode,Tcode)=0.

The strict two-block bounds split the right side into

    tau_2(g,mask)=0,
    tau_2(Jcode,(B-2)Zmask)=0.

Sun 2021 Lemma 2.4 allows arbitrary distinct digit positions and yields

    tau_2(g,mask)=0 iff
    g=sum_i n_i B^a_i for some0<=n_i<b.

For such decoded n, define

    K=(1+g)^2 E(B)+(B/2)lambda,

so Jcode=2K. In the corresponding formal polynomial, every coefficient
is B/2+A_t, and

    |A_t|<=C(1+sum_i n_i)^2<1024Cb^2<B/2.

Thus all coefficients lie strictly between 0 and B and form the actual
base-B digits without carries. At the j-th selected position,

    digit_(jd+2M)(K)=B/2+2r_j(n).

Since multiplying both binary summands by two does not change whether
there are carries,

    tau_2(Jcode,(B-2)Zmask)=0
    iff tau_2(K,(B/2-1)Zmask)=0.

At each selected block, B/2-1 has all its lower log2(B)-1 bits set.
A digit strictly between 0 and B adds without a carry exactly when it
equals B/2. There are no other nonzero mask digits. The last carry test
is therefore equivalent to every r_j(n)=0.

### 4.3 Completeness and soundness

For soundness, the source conditions f!=0,0<=g<2Ccap, b a square and
power of two, and Y|binomial(2X,X) decode a simultaneous natural zero.

For completeness, choose a simultaneous natural zero n. It is nonzero
because the fifth residual at 0 equals 1. Choose b=4^q larger than all n_i,
with q as large as desired, and f=(b-1)/3>0. Set g=sum_i n_i B^a_i.
Then b<=g<Ccap, and the preceding digit calculations show both carry
tests hold and hence Y|binomial(2X,X). This also supplies arbitrarily
large f as demanded by the original source interface.

Finally Ccap=2^(e_beta*M)b^(2M+1) has the prescribed positive monomial
shape. The general source theorem's other hypotheses have all been
proved explicitly. Nothing downstream depends on the source polynomial
having arisen from a quartic sum of squares.

## 5. The unchanged ten-integer Lucas bridge and finalizer

The byte-exact inherited proof is supplied in
`inherited/SIGNED10_PROOF.md`, Sections 4–7, with a separate mathematical
review in `inherited/INDEPENDENT_MATHEMATICAL_REVIEW.md`. The original
finalizer implementation is also included there. The old positional
source and binding metadata in these archival files are inactive;
the new source and current complete binding are the ones specified above.

The complete unknown list is `(f,g,h,k,l,w,x,y,z,m)` in Z^10. Use X,Y,Ccap
from Section 3, and define the following polynomial abbreviations:

    L=lY; U=2LX; V=4gwY; W=bw;
    A=U(V+1); B1=2X+1; C1=B1+(A-2)h;
    Pn=U^2V; K1=X+1+k(Pn-2);
    S=2A-5; T=3WC1-2(W^2-1);
    r1=(Pn^2-4)K1^2+4;
    Delta=8Ccap^3 g K1^2
          -g^2[32(C1-K1L)^2 Ccap^3+g^2K1^2];
    O=f^2l^2Delta; xi=zx;
    D=(A^2-4)C1^2+4; E1=C1^2Dxi;
    F=4(A^2-4)E1^2+1;
    G=2(A+2)(A-2)^2E1^2-1;
    Omega=16E1;
    H1=C1+(B1-C1)F+Omega*F*y;
    I=(G^2-1)H1^2+1;
    r0=b[1+(3O-4)b^2z^2];       r2=DFI.

The proof-level specializations of Sun 2026 Propositions 6.1 and 6.2
apply to the three-part source contract in Section 4. Their proofs use
no other feature of the original coefficient code. The positive bridge
is the case p=P=2, Q=1 of Sun 2021 Theorem 4.12; the reverse bridge
uses the estimates of Sun 2021 Theorem 4.13 and replaces its Lucas
certificate by Sun 2026 Theorem 3.1. The required freedom to prescribe
the second Lucas witness modulo the first is Sun 2026 Theorem 4.1. The
positive branch has O>=4. Source 31 merges b-square and O>0 into r0-square
without adding a witness, by a coprime Pell argument, and uses

    Pi(v)=(v^3-v-1)(v^2+23),
    Sigma=xi*S^5,
    t=T+Sy,
    Theta=(t^3-tS^2-S^3)(t^2+23S^2).

The polynomial Pi has no rational zero and has a zero modulo every
positive integer. Its homogeneous form has the following precise property:
Sigma|Theta forces S|T and xi!=0; conversely, for S|T and xi!=0 there
is a residue class of y modulo |xi| for which Sigma|Theta. Sun's full
residue interpolation realizes that class while retaining the Lucas
certificate. This is an existential compatibility assertion, not a
pointwise equivalence for arbitrary fixed y. As S is odd and never zero,
Theta is never zero.

For the converse valuation implication, if a prime satisfies
v_p(S)>v_p(T), then v_p(T+Sy)=v_p(T). The two factors defining Theta
have respectively valuations 3v_p(T) and 2v_p(T), because their leading
terms have uniquely least valuation. Thus v_p(Theta)=5v_p(T)<5v_p(S),
contradicting divisibility by S^5. If S|T, write q=T/S; then
Theta=S^5 Pi(q+y), so prescribing Pi(q+y)=0 modulo |xi| suffices.

The residue claim for Pi has a short proof. For odd primes p!=23, either
the cubic has a simple root, or its irreducible degree-three Frobenius
permutation is even and its discriminant -23 is a nonzero square, making
the quadratic factor have a simple root. Hensel lifting applies. At p=23
the cubic has the simple root 3. At p=2, -23=1 modulo 8 has a 2-adic square
root. Chinese remaindering supplies every positive modulus. Neither
factor has a rational root, by the rational-root theorem and negativity
of -23.

Let

    w0=1, w1=r0, w2=r0(Pn^2+K1^2+3),
    Z=Sigma*m-Theta,
    A_i=Sigma^2*w_i^2*r_i (i=0,1,2),
    Vn=Z^2+A_2-A_0-A_1,
    Wn=Vn^2+4Z^2A_2-4A_0A_1.

The delivered equation is

    F10 = Wn^2-16Vn^2Z^2A_2 = 0.

It is the norm product over the eight choices of signs of
`Z-Sigma*(±sqrt(r0)±w1*sqrt(r1)±w2*sqrt(r2))`. This identity is only a
proof device; the delivered formula has no radicals. Source 31 proves
the signed weights separate the roots even for candidate negative
radicands and covers the Sigma=0 case by F10=Theta^8!=0. A zero therefore
gives exactly the square/divisibility conditions of the reverse bridge.
Conversely its positive bridge produces all required Pell and residue
witnesses, and then an integer m makes one norm factor vanish.

Thus

    exists Z^10:F10=0 iff exists N^31:all r_j=0
                        iff a finite ZFC refutation exists.

Negation gives the requested consistency equivalence. The imported
calibration and compiler proofs are fixed at the pinned repository;
this construction neither proves Con(ZFC) nor tests its truth.

## 6. Exact complexity and verification

The compressed source has degrees X=426804,Y=284536. Its final scaled
radicands have degrees 13,947,118, 24,764,324, 112,401,754; the squared norm
center is lower. Thus the highest-degree part of F10 is A_2^4, giving
degree 449,607,016. The verifier independently evaluates leading diagonal
coefficients at three primes, proving that this structural bound is
attained at the actual fixed coefficient specialization.

`verify.py` uses a second coefficient derivation: for each
quadratic it takes the value and gradient at the all-one vector plus
the unchanged homogeneous quadratic part. This independently confirms
the builder's binomial-shift coefficients. It then checks 528 pair sums,
all fixed-port hashes and coefficient bounds, the exact norm identity,
literal scalar formulas versus the emitted DAG at 36 signed modular
assignments, and all intermediate named registers. These checks certify
the finite artifact and are separate from the universal source proof.

## Sources and status

* ProveIt pin `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, source 31-sun10:
  inherited literal source, native tuple, finalizer and finite verification code.
* Sun 2021, Further results on Hilbert's Tenth Problem,
  https://arxiv.org/html/1704.03504v7, Lemmas 2.2 and 2.4 and the
  proof of Theorem 3.1, and Theorems 4.12 and 4.13.
* Sun 2026, Ten unknowns for Hilbert's tenth problem over the integers,
  https://arxiv.org/html/2609.01594v2, Theorems 3.1 and 4.1 and
  Propositions 6.1 and 6.2. This is the September 2, 2026 preprint revision.
* The current synthesis contributes the direct quadratic batching,
  finite Sidon-position specialization, source proof, and its two
  applications through the Jones and Sun interfaces. No claim of
  first use of Sidon sets in all Diophantine literature is made.
