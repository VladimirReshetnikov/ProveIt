# Pell doubling replaces the last norm by one product square

## Result and scope

Two complete polynomials are supplied, each in ten strictly positive
integer unknowns and with the same four literal coefficient integers as
the pinned ProveIt indexed-source equation.

| Artifact | Transport weight | Operations | Exact degree |
|---|---|---:|---:|
| `equation_84.json` | V^2 | 84 | 436 |
| `equation_85.json` | bV | 85 | 328 |
| Pinned uncentered parent | b, with a two-root norm | 89 | 288 |

The new mechanism is **Pell doubling before root elimination**. Its
polynomial identity makes the auxiliary modulus a multiple of the
combined first/seed radicand. That enforces the needed coprimality
automatically. One product-square equation then forces all required
roots. No new unknown, coefficient port, prime parameter, or hidden
existential condition is introduced.

The lower-operation point saves five gates relative to the 89-operation
parent. The degree-328 point saves four gates, while raising degree by
40. These are explicit operation/degree tradeoffs, not a fewer-variable
record, a global optimum, or a claim of historical priority.

**Prior product-square work.** The incoming Shared Binomial Certificates
package already contains a single product-square construction in eleven
unrestricted integers (111/966 and 112/882). It enforces coprimality by
multiplying the strong ordinate by A times the main radicand. This is
retained for comparison in `provenance/prior_product11_proof.md`; the
source ledger pins its immutable archive member. Product-square
extraction itself is therefore not claimed as new. The distinction here
is the doubled trace Fsq=(1+2a)^2, which makes Q a multiple of the whole
combined G and removes that saturation factor in the ten-positive
kernel. Classical Pell doubling already appears in the repository's
index-folding arguments; the new claim is this particular construction
and its verified numerical tradeoffs, not the doubling identity.

The new unbounded arithmetic reduction is proved below. The consistency
interpretation composes with the pinned ordinary native/source
calibration, exactly as in the parent. The copied proofs and source
ledger identify the retained interfaces; they are not a new end-to-end
Lean build or an internal-ZFC proof object. Neither polynomial's
unsolvability nor Con(ZFC) is being asserted separately.

## 1. Complete equation

The four fixed positive integers beta,K0,MC,MF are supplied literally in
`coefficients/`, with exact byte hashes and bit lengths in both circuit
files. They are the **whole directly indexed BFS943 tuple** of the pinned
parent, not independently substituted ports. In particular,

    beta>=31 odd, K0>0, 0<MC<beta<MF<2beta.

The only unknowns are

    J,F,alpha,i,T,w,Y,n,eta,zeta in Z_{>0}.

Every other symbol in the following display is a polynomial abbreviation:

    q=beta J+1,       h=q-1,           C=q-F-alpha,
    X=wq,            mu=q^2+1,
    k=eta+zeta,      c=kY+eta,
    A=mu Y(X+1)+1,   Delta=A^2-1,     H=4A-5,
    V0=X mu^2 Y^2,   E=1+V0(V0+1)k^2,
    R=[h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    e=k-R-1,         B=(K0+w)C-F,
    U=i c^2,         a=Delta U^2 E,   F0=1+a,
    G=E F0,
    Fsq=1+4aF0,
    Q=Delta(Fsq-1)=4 Delta^2 U^2 G,
    b=c(T+alpha)-R,  V=Fsq b-c,
    Kpos=X(3c-2X)+2,
    P=q^3 h,         M=P mu^2 H.

Choose L=V^2 for the 84-operation equation, or L=bV for the
85-operation equation. Define

    Z=P mu^2[H(n-LB)+Kpos]
        +H[mu^2(hY-q^3 B)-P e],
    RG=M^2 G.

The single equation, in its optimized literal evaluation form, is

    N = Q(Z^2-RG V^2)+(RG-Z^2) = 0.                  (1)

For the proof only, put

    delta=Q-1, Dy=QV^2-1.

Identity (1) is equivalently

    delta Z^2-M^2 G Dy=0.                            (2)

The optimized form saves one operation by sharing RG. Neither delta
nor Dy is a separate gate in the shipped evaluator. All arithmetic
in (1) and its definitions is polynomial. The divisions and square
roots below are proof notation only.

The circuit uses `Am1=A-1`, `Dtau=E`, `DpI2=a`, `Df=F0`,
`Fsqr=Fsq`, `Dg=G`, `Bt=B`, `cTR=b`, `Hp=H`, `Mtot=M`,
and `Znum=Z`. These naming conventions add no quantified variables.

## 2. Early positivity

Positive inputs imply q>=32, X>=q, mu>=1025, k>=2 and c>=3.
The full Pell base A is greater than 4; Delta>=3, U>=c^2, E>1,
a>0, F0>1, Fsq>c+1, Q>1, delta>0, H>0, and M>0. No sign for
B or C has yet been used.

The integer b can initially be zero or have either sign. If b=0,
then V=-c and |V|>=3. If b is nonzero, then |V|>=Fsq-c>1.
Therefore Dy=QV^2-1>0 for every positive input. At a zero of (2),
z=Z/M is a nonzero rational number and both radicands below are
positive.

## 3. Automatic coprimality and root recovery

The central identities are

    Fsq=(1+2a)^2,
    Q=4 Delta^2 U^2 G.

Since Q is an integer multiple of G,

    delta=-1 mod G,  Dy=-1 mod G,
    gcd(G,delta Dy)=1.                                (3)

Dividing (2) by M^2 gives delta z^2=G Dy. For every prime dividing
G, its valuations in delta and Dy are zero by (3). Its valuation
in G must consequently be even, because the valuation of a rational
square is even. Thus G is the square of a positive integer g. This
does not require M to be coprime to G or any other factor.

Also F0=1+Delta U^2 E is 1 modulo E, so gcd(E,F0)=1. Their positive
product G is square. Hence

    E=tau^2, F0=f0^2, g=tau f0

for positive integers tau,f0. Set y=|z|/g. Then y is a positive
rational number satisfying

    QV^2-(Q-1)y^2=1.                                 (4)

### Rational adjacent-Pell descent

For any integer Q>1 and nonzero integer V, equation (4) forces y
integral. Write v=|V| and y=r/m in lowest positive terms. Clearing
denominators gives m^2 dividing Q-1. If v>1, then

    v<y<Qv/(Q-1).

The norm-preserving transformation

    v'=(2Q-1)v-2(Q-1)y,
    y'=(2Q-1)y-2Qv

has integral v', keeps the same reduced denominator m in y', and
satisfies -v<v'<v. Integrality follows from m^2 dividing Q-1;
denominator preservation follows from 2Q-1 congruent 1 modulo m.
The first coordinate cannot vanish, because its norm is 1 and Q-1>0.
Reflect signs and descend on the positive integer |v|. At v=1,
equation (4) gives y=1, so the unchanged denominator is m=1.
Consequently

    z=epsilon g y, epsilon in {-1,1}, y a positive integer.       (5)

### The doubled strong Pell pair

Define, in the proof,

    f=1+2a, I=2Ug=2U tau f0.

These are positive integers. The identities above give

    f^2=Fsq,
    f^2-Delta I^2=1,
    Q=(Delta I)^2,
    c^2 divides I.                                   (6)

The strong pair in (6) is the Pell double of the seed pair
(f0,U tau). This is the reason for the polynomial choice Fsq.
The main/auxiliary kernel now has exactly its accepted form,

    V=f^2[c(T+alpha)-R]-c,
    QV^2-(Q-1)y^2=1.

No saturation by A or the main radicand is necessary: (3) supplied
all the coprimality directly.

## 4. Recover the main kernel before the transport sign

The retained all-index folding theorem applies to (6), c<=I,
c^2|I, the auxiliary norm and V=-c modulo f. It gives

    c=psi_A(p), p>=1 odd.

Here psi denotes the standard Pell ordinate. The first norm E=tau^2
gives

    k=2 psi_(2V0+1)(n0), n0>=1.

The possibility n0=1 gives k=2 and c=2Y+1, strictly between
psi_A(1)=1 and psi_A(2)=2A, and is impossible. Therefore

    k>=8V0+4, c>kY>=k>8q^5, c>X, Kpos>0.             (7)

The unchanged unconditional mask estimate is

    R<q^4+(alpha+2)q^2.

Since T>=1 and alpha>=1,

    b-c>=c alpha-R
        >8q^5 alpha-q^4-(alpha+2)q^2>0.

Thus b>c>=3 and V>0 have been proved before the sign of B.

Put kappa=Kpos/H>0, s=Y/q^3>0, rho=e/mu^2, t=B/h and W=1+hL.
The exact carrier identity is

    z=n+kappa+s-Wt-rho.                               (8)

It holds as a rational identity without any divisibility premise.
The exact difference

    b-e=c(T+alpha)-k+1>0

also gives the useful one-sided estimate rho<b/mu^2. It does not
presume e>=0.

## 5. Soundness with the free V^2 weight

Let d=a=Delta U^2 E. Since Delta U^2>=3 and E>1,

    d^2-g^2=E[(Delta U^2)E(Delta U^2-1)-1]>0.

So g<a. From Fsq-1=4aF0>a and b>c,

    V=Fsq b-c>(Fsq-1)b>ab>3g, and V>b.

Equation (4) gives y/V<sqrt(Q/(Q-1))<3/2. Hence

    gy<V^2/2.

If B<=-1, then Wt<=-V^2-1/h<-V^2. Combining (5) and (8),

    n=epsilon gy-kappa-s+Wt+rho
       <V^2/2-V^2+V/mu^2<0,

contrary to n>0. Thus B>=0, and B=(K0+w)C-F with F>0 forces C>0.

## 6. Soundness with the smaller-degree bV weight

The fifth auxiliary-index argument already used in the parent provides
a sharper transport bound. Since c>=3, the folded odd p cannot be 1.
Therefore p>=3 and

    c>=psi_A(3)=4A^2-1=4Delta+3.

Since b>c,

    V>(Fsq-1)c>4Delta(Fsq-1)=4Q.                     (9)

By (6), Q=S^2 with integer S=Delta I>=2. Equation (4) becomes

    (SV)^2-(S^2-1)y^2=1.

Positive Pell classification gives SV=chi_S(j) for a positive index
j. Modulo S, even-index traces are +/-1, so j must be odd. The first
two odd possibilities give V=1 and V=4Q-3, both excluded by (9).
Thus j>=5, and monotonicity gives

    V>=chi_S(5)/S=16Q^2-20Q+5>8Q^2.

The last inequality holds for Q>=3, in particular for Q=S^2>=4.
As Fsq>2,

    b=(V+c)/Fsq
       >8Delta^2(Fsq-1)^2/Fsq
       >4Delta^2(Fsq-1)
       =4Delta^3 I^2>4g.                             (10)

The final strict bound uses I=2Ug with U,g>=1. Therefore, with L=bV,

    gy<(3/2)gV<3bV/8<L/2.

If B<=-1, equations (5) and (8) now give

    n<L/2-L+b/mu^2<0,

because V>1 and mu^2>2. Again B>=0 and C>0. This proves the lower-degree
transport theorem without assuming parity, rank p=R, carrier
divisibility or decoded native-source conditions in advance.

## 7. Later arithmetic decoding retains its hypotheses

After either transport argument, all later parent interfaces apply in
the same order:

1. C>0 gives 3q<R<q^4-2.
2. The normalized strong-rank and signed auxiliary-index theorems use
   c^2|I, c>2R, c>2p and the same fixed-minus residues. They give p=R.
3. Odd p gives R odd; the same mask parity gives q even and J odd.
   Only now is gcd(mu^2,P H)=1 invoked.
4. The rational carrier is integral by (5). The changed transport term
   L is an integer, and W=1+hL remains 1 modulo h. The unchanged
   denominator argument gives mu^2|e and n0=(R+1)/2.
5. The same ratio estimates and whole-product projection infer X=2^R
   by bounding the entire product P(X-2^R)(2^R X+1). No arbitrary
   factor is cancelled modulo a composite H.
6. The remaining fractions give integer kappa,s,t, q^3|Y and h|B.
   Fixed-minus parity, exact half-binomial rounding and the fresh
   unscaled source reconstruction at Y(X+1)+2 give the accepted
   native source and a finite syntactic ZFC refutation.

The retained strong theorem does not require its index to be odd or its
ordinate divided by c^2 to have a prescribed parity. Doubling the seed
pair therefore does not remove a hypothesis needed by this chain.
The denominator arguments need an integral carrier, not an additive
decomposition into signed roots. The product gy supplies that integrality.

## 8. Positive completeness by doubling a fresh seed period

Conversely, a finite refutation supplies the same canonical outer,
first and main data as the parent: A,c,k,tau,R with

    c=psi_A(R), E=tau^2, R=3 modulo 4,
    integer t>=0, rho>=0, s>0, kappa>0.

The determinant-one matrix [[A,Delta],[1,A]] has finite order modulo
N0=c^2 tau. Choose a positive multiple of this order. Its seed Pell
pair (f0,I0) has N0|I0; further multiples can make it as large as needed.
Put

    i=I0/(c^2 tau)>0, U=i c^2=I0/tau.

Then a=Delta I0^2=f0^2-1, F0=f0^2 and g=tau f0. Double this actual
seed pair:

    f=2f0^2-1=1+2a, I=2f0 I0=2Ug.

All the literal definitions Fsq,Q are now exactly the corresponding
strong quantities. Only one Pell period with prescribed divisibility
was chosen. There is no unproved simultaneous solvability claim for
unrelated Pell equations.

The parent's auxiliary-completeness theorem applies to this doubled
strong pair. Its hypotheses are A>=2, R>=3 with R=3 modulo 4,
c=psi_A(R), the strong norm and c|I. It does not impose parity on
the strong index or I/c^2. It supplies T'=T+alpha>alpha, V>0 and
y>V, with the literal b,V definitions and auxiliary equation (4).
An explicit witness is

    S=Delta I,
    V=chi_S(R)/S, y=psi_S(R),
    T'=(V+c+R f^2)/(c f^2).

The retained odd-index identities give integrality, and the retained
auxiliary growth argument gives T'>alpha. The inputs i,T are rebuilt;
they are not copied from a differently scaled or undoubled source.

For either positive weight L, set W=1+hL and choose

    n=gy+Wt+rho-kappa-s.                              (11)

Every term is integral. The seed pair already satisfies

    f0>(A-1)I0>Xc>kappa,

and the first canonical norm gives tau>Y>=s. As f0,tau>=3,
g=f0 tau>f0+tau>kappa+s. Since y>=1 and Wt,rho>=0, equation (11)
gives n>0. Its carrier is z=gy, and (2), hence (1), vanishes.

This constructs all ten positive inputs from each finite refutation.
Together with soundness and the whole retained native calibration it
proves, by ordinary arithmetic formalizable in ZFC,

    ZFC proves [no positive zero of either polynomial] iff Con(ZFC).

## 9. Exact operation counts

Each circuit is a complete topological list with no dead gates or
unused inputs/ports. Every binary product, sum and difference is counted,
including squares and multiplication by fixed scalar literals. The
fixed leaves use the parent's unchanged convention.

The doubled auxiliary square Fsq=1+4aF0 adds three live operations
relative to the old kernel. Removing the old integral V center saves
one. Replacing the old two-root norm by the optimized product-square
test saves seven. Thus the free V^2 weight costs

    89+3-1-7=84 operations.

The bV weight uses one extra multiplication, for 85. Their exact
breakdowns are respectively (50,19,15) and (51,19,15) for products,
sums and differences.

The finalizer's elementary saving is the full polynomial identity

    (Q-1)Z^2-RG(QV^2-1)
        =Q(Z^2-RG V^2)+(RG-Z^2).

This is evaluation reuse, not a new equivalence or an uncounted
division.

## 10. Exact total degrees and leading forms

The degree bounds for A,c,U,E,a,F0,G,Fsq,Q,V,M are respectively

    5,2,5,18,38,38,56,76,86,80,13.

For L=V^2, Z has degree at most 175; hence delta Z^2 has degree
at most 436 while M^2 G Dy has degree at most 328.

For L=bV, b has degree 4 and L has degree 84, so Z has degree at
most 99. Now delta Z^2 has degree at most 284, while the other
term still has degree at most 328. The following nonzero highest
homogeneous forms prove that both stated bounds are attained.

Write q0=beta J and k0=eta+zeta. The common leading forms include

    A0=q0^3 wY, c0=k0Y,
    U0=i k0^2 Y^2,
    E0=q0^10 w^2 Y^4 k0^2,
    a0=i^2 q0^16 w^4 Y^10 k0^6,
    G0=i^2 q0^26 w^6 Y^14 k0^8,
    Fsq0=4a0^2,
    Q0=4i^4 q0^38 w^10 Y^22 k0^12,
    b0=-q0^3(q0-F),
    V0_aux=-4i^4 q0^35 w^8 Y^20 k0^12(q0-F),
    M0=4q0^11 wY,
    B0=w(q0-F-alpha).

For L=V^2 the unique dominant final term is delta Z^2, giving

    2^14 q0^200 w^46 Y^104 i^20 k0^60
       (q0-F)^4(q0-F-alpha)^2.                        (12)

The coefficient of J^200 w^46 Y^104 i^20 eta^60 F^4 alpha^2 is
2^14 beta^200>0, and its degree is 436.

For L=bV the unique dominant final term is -M^2 G Dy, giving

    -2^10 q0^156 w^34 Y^78 i^14 k0^44(q0-F)^2.        (13)

Its coefficient of J^156 w^34 Y^78 i^14 eta^44 F^2 is
-2^10 beta^156, nonzero for the actual beta. Its degree is 328.
There is no cancellation with the lower-degree other summand.

The verifier independently combines the exact gate-by-gate degree
upper bounds with complete univariate polynomial replay over a finite
field using the actual fixed coefficient tuple. Nonzero coefficients
at degrees 436 and 328 give independent attainment certificates.

## 11. Reproducibility and proof boundary

Run `python3 verify.py`; the checker uses only the standard library.
It checks both complete input signatures, graph topology, liveness,
every actual gate against the displayed polynomial interfaces, all
four literal coefficient byte hashes and bit lengths, their coefficient
box, the doubled-Pell and finalizer identities, the complete carrier,
global degree upper bounds and actual-tuple nonzero leading rays.
It also checks 5,880 small coprimality controls and rejects five actual
gate mutations per equation. Normal and optimized-Python runs have
the same required checks; they do not rely on assert statements.

The coefficient files are gzip-compressed canonical unsigned
little-endian byte strings. The source ledger also retains the complete
symbolic constant specification, the parent equation and the ordinary
proof interfaces. The new circuits and the four integers specify
actual finite polynomials, not a promise that a general compiler
could eventually emit one.

Finite audits do not prove Pell classification, the native/compiler
calibration, or consistency. The new root/sign/completeness arguments
are ordinary unbounded proofs; the last native-to-refutation step is
the explicitly inherited theorem. A new formal derivation inside an
encoded object ZFC has not been emitted.
