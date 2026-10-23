# Quartic monomial coding by a Bose-Chowla B4 set

## Result and precise status

The division-free circuit `generated/b4_signed10.json` defines a fixed
integer-coefficient polynomial in the ten unrestricted integer variables

    f, g, h, k, l, w, x, y, z, m.

Its total degree is **107,286,763,576**. Its supplied arithmetic circuit
uses **2,204** binary additions, subtractions, and multiplications, including
multiplication by fixed numerals. Reuse and fixed leaves are free. The
coefficient tuple is the complete 121-by-8801 Wang943 tuple of package 31,
pinned to ProveIt commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.

The new mathematical step is a replacement of positional quartic monomial
coding by an additive B4 code. It preserves the number and domains of the
outer witnesses. Composed with the same K215/compiler/quartic endpoint and
the same published and preprint Sun bridge used in package 31, it proves,
by ordinary mathematics formalizable in ZFC,

    exists an integer zero of F_B4  <=>  not Con(ZFC).

Classical negation gives the requested equivalence for absence of integer
solutions. This is not a proof of Con(ZFC), not a kernel-checked endpoint,
and not a minimum-variable or globally optimal degree theorem. The
ten-integer reduction is Sun's theorem. Bose-Chowla sets are classical.
The claim here is the explicit source-coding adapter, its proof, and its
quantified improvement to the pinned instance, not priority for the
underlying general ideas.

Package 31's best ten-integer circuit has degree
126496*5^31+27064 and 1442 operations. The new degree is about 5.49*10^15
times smaller, while its circuit uses 762 more operations. These are
different measures and neither equation dominates the other on all of them.

## 1. Fixed source and imported mathematical dependencies

Let P0(n_1,...,n_31) be the sum of squares of the 22 quadratic residuals
in `data/parent_quartic31.json`, after substituting n_i+1 for every original
positive coordinate. This parent file is byte-exact with SHA256

    1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.

All four coefficient ports are fixed integers, bound together by
`data/coefficients_binding.json`. Their compressed, unsigned little-endian
payloads are included. The port order is (beta,K0,MC,MF), with MF already
shifted as in the parent compiler. The port bit lengths are
(1064921,1070004,1064921,1064922).

The imported ordinary endpoint is

    exists n in N^31, P0(n)=0  <=>  K215 halts blank
                                <=>  ZFC has a finite refutation.

Here N includes zero. The native-window/Pell compiler and literal K215
calibration are substantial dependencies. Neither finite circuit testing
nor a hash establishes these mathematical implications. This adapter
changes neither the tuple nor that endpoint. Source details and the old
bridge/finalizer proof are retained in `upstream_SIGNED10_PROOF.md`.

The polynomial P0 has degree four and P0(0)>0. Indeed its fifth residual,
E-X(a-E), equals 1 when every positive parent coordinate is 1. Write

    P0(n)=sum_{|alpha|<=4} p_alpha n^alpha,
    c_alpha=(4-|alpha|)! product_i(alpha_i!) p_alpha.

The file `data/constants.json` gives all 402 nonzero weighted-coefficient
recipes. Its retained leading zero in each alpha vector is a source-file
convention; it is not an input digit or an additional unknown. The verifier
reconstructs every recipe by exactly expanding the 22 shifted squares.

Set beta_S=2^4269882. If H=max_alpha |p_alpha|, the inherited exact
coefficient certificates establish

    beta_S > 2*24*33^4*H.

The power is even, beta_S is a square power of two, and its materialized
compressed payload is included. No coefficient depends on whether a
refutation exists or on a search for one.

Besides the inherited compiler endpoint, the proof imports Sun's following
ordinary arithmetic results:

* Sun 2021, Lemma 2.2: the two-block no-carry/binomial transformation used
  below; its proof is independent of the choice of digit positions.
* Sun 2026, Propositions 6.1 and 6.2: the forward and reverse binomial
  bridges, and Theorem 4.1: full residue-class interpolation in the modified
  Lucas certificate.
* Package 31's elementary quintic, coprime positivity, and norm finalizer
  lemmas, reproduced in the accompanying upstream proof. Their hypotheses
  involve only the source interface, not its positional encoding.

Primary sources are Sun, *Further results on Hilbert's Tenth Problem*,
Sci. China Math. 64 (2021), 281-306, arXiv:1704.03504v7,
https://arxiv.org/html/1704.03504v7, especially Lemmas 2.2, 2.4, 2.6 and
the proof of Theorem 3.1; and Sun, *Ten unknowns for Hilbert's tenth problem
over the integers*, arXiv:2609.01594v2 (2026 preprint),
https://arxiv.org/html/2609.01594v2. The latter dependency is a preprint,
and no new formal verification of its Lucas theorems is asserted here.

## 2. The additive code and its exact certificate

An integer sequence 0=w_0<w_1<...<w_31 is suitable if the sums of four
elements, allowing repetition and disregarding order, are all distinct.
Equivalently, the map

    alpha -> sum_{i=1}^{31} alpha_i w_i

is injective on |alpha|<=4: pad each multi-index to length four using w_0.
Injectivity of these short sums is the property needed by coefficient
recovery. Superincreasing positional weights are sufficient, but not
necessary.

The supplied weights, including the homogenizing zero, are

    0, 42609, 49910, 91724, 155840, 213052, 290241, 337708,
    340502, 351998, 388348, 417182, 480443, 513128, 534148,
    563475, 579595, 636647, 639228, 692126, 725139, 732225,
    748536, 754497, 817940, 820267, 829985, 858576, 870324,
    879730, 907673, 942302.

Put T=942302, Lc=4T=3769208. The weights are listed in
`bose_chowla32.json`; the i-th positive weight is assigned to the i-th
variable in the parent quartic's literal ordering.

There are binomial(35,4)=52360 four-element multisets. The checker enumerates
them all and verifies that their sums are already distinct modulo
M=2^20-1=1048575, which implies distinct integer sums. This finite check
is short and independent of the finite-field explanation below.

For a mathematical construction, work in the 20-dimensional binary
quotient by X^20+X^3+1 and write theta=X. The included exact computations
give theta^M=1 and theta^(M/p)!=1 for p=3,5,11,31,41, all prime divisors
of M. Therefore theta has order M. Its M powers and zero exhaust the
2^20 residue classes, so every nonzero element is a unit: this also proves
that the quotient is a field without assuming irreducibility in advance.
Its unique 32-element subfield consists of the roots of c^32=c.

Take the 32 discrete logarithms a_c defined by theta^(a_c)=theta+c for
c in that subfield. If two sums of four such logarithms agree modulo M,
then the corresponding products of four factors theta+c agree. Subtracting
the two monic degree-four polynomials cancels their leading terms and
leaves a polynomial of degree at most three over the subfield. The element
theta has degree four over this subfield, so this difference is zero.
Unique factorization then identifies the two multisets. This is the
standard Bose-Chowla argument: R. C. Bose and S. Chowla, *Theorems in
the additive theory of numbers*, Comment. Math. Helv. 37 (1962/1963),
141-147, https://doi.org/10.1007/BF02566968.

Translate every logarithm by -535448 modulo M, choose representatives in
[0,M), and sort. Translation preserves four-sum uniqueness and gives the
displayed weights. This origin follows the largest cyclic gap of the
logarithm set, reducing the maximum weight to 942302. The code generator
regenerates the logarithms, the translation, and every four-sum check.

## 3. Coefficient extraction with arbitrary B4 weights

For an indeterminate t define

    C_n(t)=(1+sum_i n_i t^{w_i})^4,
    D(t)=sum_{|alpha|<=4} c_alpha t^{Lc-alpha.w}.

All exponents in D are nonnegative because alpha.w<=4T. Distinct alpha
have distinct exponents. The multinomial theorem and B4 injectivity give

    [t^Lc] C_n(t)D(t)=24 P0(n).

Proof: the term indexed by beta in C_n has coefficient
4! n^beta/((4-|beta|)! product beta_i!) and exponent beta.w. A product
term can reach exponent Lc only when beta.w=alpha.w. Injectivity forces
alpha=beta, and the factorial weights cancel. This proves the identity
without any estimate or modular assumption.

If 0<=n_i<b and H=max|p_alpha|, every coefficient q_j of C_n(t)D(t)
satisfies

    |q_j| <= 24 H (1+sum_i n_i)^4
           <= 24 H (1+31(b-1))^4.

Indeed every coefficient of C_n is nonnegative, their sum is C_n(1), and
every coefficient of D has magnitude at most 24H. Its distinct exponents
were needed here to avoid collecting unrelated coefficient terms. The
product has degree at most Lc+4T=8T.

## 4. Explicit new two-witness source interface

For integer f,g set, in order,

    b=1+3f,                     B=beta_S b^4,
    ell=sum_i B^{w_i},           D=D(B),
    N0=B^{T+1},                  N1=4 B^{8T+1},
    N=N0 N1,                    Ccap=b B^T,
    Mcode=N0-1-(b-1)ell,
    Tcode=Mcode+(B-2)B^{Lc}N0,
    Jcode=2(1+g)^4 D+sum_{j=0}^{8T} B^{j+1},
    Scode=g+Jcode N0,
    Rcode=(Scode+Tcode+1)N+Tcode+1,
    X=(N-1)Rcode,               Y=N^2.

Every sum length and exponent is fixed. These are ordinary integer
polynomials in f,g. In particular, the enormous but finite geometric
sum is evaluated by a binary addition-chain circuit, never by variable
exponentiation or division.

**Source-interface theorem.** If P0 has a natural zero, then for every
positive bound Z there are f>=Z and b<=g<Ccap such that b is a square
power of two and Y divides binomial(2X,X). Conversely, if f!=0,
0<=g<2Ccap, b is a square power of two, and this binomial divisibility
holds, then P0 has a natural zero. In addition, under f!=0, b square,
and 0<=g<2Ccap, one has 3|X, X>3b, and Y>max(b,256), even without
assuming b is a power of two.

### 4.1 Bounds before applying the binary lemmas

Because b=1 mod 3 and b is a square, f!=0 forces f>0 and b>=4. Thus
B is positive, B>=2b, and all source quantities are ordinary integers.
The strict coefficient bound implies

    B/2 > 24H(1+31(b-1))^4,
    B > 2+2*24H(32b)^4.

For the second inequality, beta_S>2*24*33^4 H and H>=1 leave more than
2 units of margin after replacing 33 by 32 and multiplying by b^4.

The constant term of P0 is positive. Consequently D(B)>0: its leading
term is 24P0(0)B^Lc, all other exponents are below Lc, and their total
absolute contribution is at most 24H sum_{j=0}^{Lc-1}B^j<B^Lc.
Also D(B)<=24H sum_{j=0}^{Lc}B^j.

The mask Mcode has base-B digit B-b at every w_i and B-1 elsewhere
from position 0 through T. Hence 0<=Mcode<N0. The target block satisfies
0< (B-2)B^Lc <N1, and therefore 0<=Tcode<N.

For 0<=g<2Ccap one has g<N0 and 1+g<=2bB^T<=32bB^T. Using the preceding
bound for D and B>2+2*24H(32b)^4,

    0<Jcode
      < ((B-2)+B)/(B-1) * B^{8T+1}
      = 2 B^{8T+1}<N1.

Thus 0<=Scode<N. These statements hold before the no-carry or source
zero conditions; no sign hypothesis is being inferred from a later norm.

Since beta_S is an even power of two and b=1 mod 3, B=1 mod 3 and
N=4B^{9T+2}=1 mod 3. Therefore 3 divides X. Furthermore
Rcode>=N+1, N>B>=b, and N>=4 imply X=N-minus-one times Rcode>3b.
Finally Y=N^2>max(b,256). The constants in this instance make the strict
inequalities immediate.

### 4.2 The mask decodes arbitrary witness positions

Now assume b is a power of two. Then B,N0,N1,N are powers of two.
Write tau_2(A,B)=0 to mean that adding the nonnegative integers A and B
in base two produces no carries, equivalently their bitwise AND is zero.
The mask description gives

    0<=g<2Ccap and tau_2(g,Mcode)=0
      <=> g=sum_i n_i B^{w_i}, with 0<=n_i<b.

Indeed B-b has ones precisely in the high binary bits of a B-digit,
whereas B-1 has ones in every bit. Thus the only free bits of g are the
low log_2(b) bits at the allowed positions w_i. The bound g<N0 excludes
higher positions. Conversely every displayed code fits and is <Ccap.
No superincreasing condition on the w_i enters this argument: they only
need to be distinct positions.

### 4.3 One digit detects P0=0 exactly

For decoded g write (1+g)^4D(B)=sum_{j=0}^{8T}q_j B^j, using the
formal coefficients from Section 3. Define

    Jprime=sum_{j=0}^{8T}(q_j+B/2)B^j.

The strict coefficient bounds give 0<q_j+B/2<B, so these are the actual
base-B digits of Jprime, including digits for zero coefficients. Since
Jcode=2Jprime,

    tau_2(Jcode,(B-2)B^Lc)=0
      <=> tau_2(Jprime,(B/2-1)B^Lc)=0.

The mask B/2-1 has ones in every low bit of the digit at Lc and nowhere
else. The digit there lies in [1,B), so no carries occur precisely when
it equals B/2. This is equivalent to q_Lc=0, and Section 3 identifies
q_Lc=24P0(n). This is an exact coefficient argument, including negative
coefficients; no random evaluation is used to justify it.

### 4.4 Binomial divisibility and the two implications

Because Scode,Tcode each consist of two nonoverlapping blocks below N,
and N0 is a power of two,

    tau_2(Scode,Tcode)=0
      <=> tau_2(g,Mcode)=0 and tau_2(Jcode,(B-2)B^Lc)=0.

Sun 2021 Lemma 2.2, specialized to p=2 and 0<=Scode,Tcode<N with N a
power of two, gives

    tau_2(Scode,Tcode)=0
      <=> N^2 divides binomial(2X,X),

for the exact Rcode and X defined above. Combining the last three
subsections proves the reverse implication of the source-interface
theorem and its forward implication for any sufficiently large square
power b.

To finish completeness, given a natural zero n and bound Z, choose an
even exponent 2s large enough that b=2^(2s)>max_i n_i and
(b-1)/3>=Z. Since 4^s=1 mod 3, f=(b-1)/3 is an integer. At least one n_i
is nonzero because P0(0)>0, so g=sum n_i B^{w_i}>=B>=b. Its upper bound
is g<Ccap, by the ordinary geometric-sum bound and max_i n_i<b.
The mask and coefficient arguments give the required divisibility.

Finally Ccap is of Sun's required monomial form: Ccap equals
2^(4269882*T) b^(4T+1), and 4269882*T is even. Thus all of the source
interface, including cofinal f and the exact exponent shape of its bound,
has been proved anew.

## 5. The ten-integer equation and unchanged outer reduction

Use the new polynomials X,Y,Ccap above in the bridge formulas in Sections
4-7 of `upstream_SIGNED10_PROOF.md`. For convenience the resulting finite
definition is as follows; all capital letters denote registers, not
additional unknowns:

    L=lY, U=2LX, V=4gwY, W=bw,
    A=U(V+1), Bsmall=2X+1, C=Bsmall+(A-2)h,
    Pn=U^2 V, K=X+1+k(Pn-2), S=2A-5,
    Tsmall=3WC-2(W^2-1), R2=(Pn^2-4)K^2+4,
    Delta=8 Ccap^3 g K^2-g^2(32(C-KL)^2 Ccap^3+g^2K^2),
    O=f^2 l^2 Delta, xi=zx,
    Dsmall=(A^2-4)C^2+4, E=C^2 Dsmall xi,
    F=4(A^2-4)E^2+1, Gstar=2(A+2)(A-2)^2 E^2-1,
    Omega=16E, Hstar=C+(Bsmall-C)F+Omega F y,
    Istar=(Gstar^2-1)Hstar^2+1,
    r=Tsmall+Sy, Sigma=xi S^5,
    Theta=(r^3-rS^2-S^3)(r^2+23S^2),
    r0=b(1+(3O-4)b^2z^2), r1=R2, r2=Dsmall F Istar,
    weight0=1, weight1=r0, weight2=r0(Pn^2+K^2+3),
    center=Sigma m-Theta, Ai=Sigma^2 weighti^2 ri (i=0,1,2),
    Vnorm=center^2+A2-A0-A1,
    Wnorm=Vnorm^2+4center^2 A2-4A0A1,
    F_B4=Wnorm^2-16Vnorm^2 center^2 A2.

The requested equation is F_B4=0. No radicals, divisions, variable powers,
or extra quantified registers occur in this definition.

For soundness the quintic pi(t)=(t^3-t-1)(t^2+23) has no rational root,
so Theta is never zero when S!=0; S is always odd. If Sigma=0 the final
norm equals Theta^8, so a zero forces xi!=0. The separating weights then
make r0,r1,r2 integer squares and force Sigma|Theta. The homogeneous
quintic valuation argument gives S|Tsmall. Coprimality of b and its
positivity bracket, together with b=1 mod3 and z!=0, gives b square
and O>0. Sun's reverse bridge supplies the source interface conditions,
and Section 4 recovers a zero of P0.

For completeness the source theorem gives arbitrarily large f and the
positive binomial bridge gives the other initial witnesses. The Pell
argument gives z>0 with r0 square and O>=4. Sun's full residue interpolation
chooses xi divisible by z, with y in the residue class required by the
quintic merger. Set x=xi/z. Then r1,r2 are squares and Sigma|Theta.
An appropriate integer m makes one linear factor of the norm vanish.
This proves the equivalence in both directions. The exact statements,
sign details, zero cases and proofs of these unchanged finalizer lemmas
are retained in the upstream proof.

## 6. Circuit construction and finite verification

The program evaluates the coefficient polynomial using the identity

    B^(4T-alpha.w)
      =(B^T)^(4-|alpha|) product_i (B^(T-w_i))^alpha_i.

Every exponent on the right is nonnegative. A sparse multivariate Horner
scheme shares these powers and coefficient recipes. This is a polynomial
identity, not division by a power of B, so the emitted circuit is valid
on arbitrary integer assignments as well as the positive source branch.

The independent scalar verifier instead evaluates the literal 402-term
sum with exponents Lc-alpha.w. It checks every named source, bridge and
norm register modulo three primes on 36 assignments per variant. These
tests detect transcription mistakes; they do not prove the universal
arithmetic lemmas or decide whether any solution exists.

The exact total degree is proved by a division-free DAG upper bound and
a nonzero coefficient after substituting one indeterminate for all ten
variables. For the main circuit the coefficient at degree 107286763576
is 16 modulo 101 (also 599 modulo 1009 and 622356 modulo 1000003), so
the upper bound is attained. One nonzero modular coefficient suffices.
The exact coefficients of the three-radicand norm are independently
expanded and compared with all eight signed formal factors.

Run, from this directory:

    python3 b4_code.py
    python3 build_b4_sun10.py
    python3 verify_b4_sun10.py

Only the Python standard library is used. The verification regenerates
the finite field code, all 52360 multiset checks, all 402 source
coefficient records, fixed payload hashes and bounds, formal norm
identities, modular transcription checks, and degree witnesses.

## 7. Further research

1. Replace the generic Bose-Chowla code by a code separated only against
   the actual support of the quartic. The detector needs each source
   monomial distinguished from all degree-at-most-four monomials, not
   necessarily pairwise distinction among absent monomials. This could
   reduce the maximum exponent substantially, but an exhaustive
   support-aware certificate and a new bound proof are required.
2. Optimize shared addition chains for the 62 code and complementary
   exponents. The present degree gain costs arithmetic gates; there is
   room to reduce that cost without changing the polynomial.
3. Generalize the adapter to degree delta using a B_delta set of n+1
   elements, and determine the best degree/operation tradeoff. Classical
   Bose-Chowla sets over a field of size q>=n+1 give maximum weights
   below q^delta. For fixed delta this removes the exponential dependence
   on n in this part of the source coding.
4. Adapt the same coefficient coding inside the Jones nine-natural
   route. Its positional and index interface require a separate proof;
   the current ten-integer result does not by itself establish that
   adaptation.
5. Formalize the source-interface theorem and attach it to a formally
   verified Sun bridge. The present result has exact finite certificates
   and an ordinary proof, but is not a replacement for that formal task.
