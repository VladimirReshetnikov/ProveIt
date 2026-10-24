# Independent review of the ten-positive degree-912 construction

## Verdict and boundary

**PASS for the new arithmetic reduction, literal circuit, and degree claim.**
No gap was found in the unbounded existence equivalence after independently
checking the sign extraction, the order of the positivity bootstrap, the
residue argument, and the fresh auxiliary construction. The literal graph
has 126 live binary operations (75 multiplications, 34 additions, 17
subtractions) and exact total degree 912. It uses the complete, unchanged
compact44 coefficient tuple and ten strictly positive unknowns.

This review is independent of the packet's builder and checkers: the review
program imports none of their code and uses a separate exact-polynomial
implementation, SymPy. The mathematical review does not purport to
re-prove the native tableau compiler or the K215-to-refutation calibration.
Those ordinary unbounded theorems remain inherited dependencies, exactly
as the packet states. Neither the construction nor this review proves
Con(ZFC), and neither is an end-to-end proof-assistant certificate.

## What was checked without bounded witness assumptions

### 1. Every root is real, and signed-subset separation is sufficient

Let b=c(T+F+alpha)-R. The integer V=Df*b-c cannot vanish: if b=0 then
V=-c; if b is nonzero, |V|>=Df-c>c. Thus QV^2-1>0 before C>0 or any index
recovery. The use of four positive real magnitudes in the norm argument is
legitimate.

The two superincreasing orders are valid independently of C and R:

- If b=0, then c<y<c+1, d/H<c, t>2c+1, and
  f-t>(a+1)c(c-1)>2c+1. The order is d/H, y, t, f.
- If b!=0, then y>|V|>=f^2-c>2f and f>t+d/H.
  The order is d/H, t, f, y.

These prove that *every* nonempty signed subset is nonzero, not merely
that one root dominates. In a multiquadratic extension, distinct rational
square classes give independent character eigenspaces. A rational signed
sum would therefore force a vanishing signed subset in each occupied
nontrivial square class. The superincreasing property excludes this, so
all four roots are rational. This is a valid extraction argument, even if
several roots share the same nontrivial square class.

Three roots are integral immediately. The adjacent-coefficient descent
for the fourth root is also sound and requires no source indices. With
Q>1, V integral, and y=b/m in lowest terms,
Q V^2-(Q-1)y^2=1 gives m^2|(Q-1). For positive V>1 and positive y,
y>V and

    y/V < sqrt(Q/(Q-1)) < (2Q-1)/(2(Q-1)).

Consequently V'=(2Q-1)V-2(Q-1)y is a positive integer smaller than V.
The companion y' preserves the norm and the reduced denominator m,
because gcd(2Q-1,m)=1. Replacing a companion coordinate by its absolute
value when needed does not change the norm or denominator. Descent reaches
V=1, where y=1, forcing m=1. This closes the rational-denominator case.

### 2. Pell growth really precedes positivity of C

The integral first and main roots classify with
P=2XY^2+1 and A=a+2. The first equation has positive fundamental solution
(t,k)=(2XY^2+1,2), so its solutions have k=2 psi_P(m).
The main equation has c=psi_A(p). Since c>1, p>=2. If m=1, k=2 and
eta=zeta=1, hence c=2Y+1<2A=psi_A(2), a contradiction. Therefore m>=2,
k>=4P>8XY^2, and c>8XY^3>=8q^9.

No assumption X is divisible by q, C>0, or R>0 occurs here. This is the
crucial order change relative to an argument that would assume the native
bound on R too early.

### 3. The shifted auxiliary coordinate provides the needed one-sided bound

The actual mask inequalities give |R|<q^3(q+h), h=F+alpha, without C>0.
For example, expand R as a constant part smaller than q^4, a negative F
coefficient of magnitude less than q^3, and a positive alpha coefficient
smaller than q^3. Since h>=2 and c>8q^9,

    c*h > q^3(q+h) > |R|.

Thus b=c(T+h)-R is positive and smaller than c(T+2h), and V>1. Write y for
the positive auxiliary root. The exact difference formula and the exact
identity

    delta-(Delta-1)*Df = Delta*(I^2-1)>0

show

    0<y-V<V/delta<c(T+2h)/(Delta-1).

Using c<k(Y+1) and Delta-1>4(Y+1) gives

    y-V<k(T+2h)/4<k(T+h)/2=L/2.

For either sign of the main root,

    gamma=(d_*-a*c-X)/H-X/q+(k-R-1)/q^5
         <2c/H+k/q^5+|R|/q^5.

Every subsequent bound in the printed chain is valid. In particular,
2c/H<k/2 and q>=16 yield gamma<3k/4+h/4<k+h/2. Finally,

    k*T+k*h-2k-h
      = k*(T-1)+(k-1)*(h-1)-1 >= 0

for T>=1, k>=2, h>=2, so gamma<L/2. There is intentionally no lower bound
on gamma; none is needed. The signed strong and auxiliary roots obey
f_*<=f<Cf and y_*<=y<V+L/2. Consequently the merged equality gives r>n>0
for all sixteen choices of signs. This yields Bt>0 and only then C>0.

The fresh translation T+F+alpha and the same translated coordinate in
L=k(T+F+alpha) are both essential to this proof as written. The review's
same-size mutations removing either occurrence are rejected by exact
local circuit identities.

### 4. The residue recovery is in a noncircular order

After C>0, and only after it, the native inequalities 3q<R<q^4-2 give
c>2R. Main Pell growth gives c>2p. The inequality m<p used in the
predecessor also holds independently: P>A, and m>=p would imply
k=2 psi_P(m)>psi_A(p)=c, contradicting c>k.

The normalized strong equation has I=i*c^2. Strong divisibility and
composition give p*c dividing its positive Pell index, hence an index
divisible by c and greater than 2p. With S=Delta*I, the auxiliary norm has
S^2=Q, c|S, V=-c mod f, and V=-R mod c. All hypotheses of the retained
signed auxiliary-index lemma are now satisfied; it gives p=R without
assuming the main-root sign or either missing residue.

The integral centers L,V,Cf do not affect denominator clearing. Integrality
of r+gamma first yields q^5 | q^4 X-v, because gcd(H,q)=1 follows from
q=2 mod 3 and H=3 mod q. The first Pell recurrence and 1<=m<R then give
q^4 | 2m-R-1 with absolute value below q^4, hence R=2m-1. Only now is
v=k-2m known to be a positive multiple of 4XY^2, and hence of q^5. Thus
q|X. Finally (q-1)(d_*-b0)/H is integral.

The remaining separation uses the genuine growth bound
Y>X^((R-1)/2)/2-1>q*2^R. The printed Pell congruences modulo H are correct:
substitute Delta=a^2, use A-a=2, A+a=2a+2, and
2(2a+2)=H+1. A negative main-root sign produces a positive integer
(q-1)(1+2^R X)/H strictly below one, impossible. The positive sign then
forces X=2^R by the second integer-of-absolute-value-below-one argument.
Only after this are gamma, r, and the transport quotient recovered as
integers. No cancellation using gcd(H,q-1)=1 occurs or is needed.

The normalized source reconstruction T_source=f*(T+h) gives exactly
c(T_source*f-1)-R*f^2=V, so the source interface is matched without an
unjustified divisibility requirement on an old auxiliary coordinate.

### 5. Canonical completeness uses fresh witnesses in the correct order

The canonical outer source coordinates and strong pair are fixed first.
The retained odd-index quotient construction at S=Delta*I gives

    V*=chi_S(R)/S,
    y*=psi_S(R),
    Told=(V*+c+R*f^2)/(c*f^2).

Its two congruences are modulo f^2 and c, with gcd(f^2,c)=1, so Told is an
integer. This is a newly constructed auxiliary pair, not an arbitrary
source pair whose quotient is assumed adjustable.

Since R>=7, V*>=S^(R-1)>=S^6, f^2<S^2, and S>=c^2. Hence
Told>S^4/c>=c^7>q>h. Moreover S^4/c>Cf, using
Delta^4>A and I^3/c>=1. Therefore T=Told-h>0, L=k*Told>Cf, and L>k.
These quantities are formed before r and n.

The canonical v is a positive multiple of 4XY^2, so v/q^5>X/q. Thus the
new gamma is positive. The source transport quotient has t0>=q, and the
first-root interval with s<k gives r>qW-2k>2L. Finally
n=r+gamma+f+y*-L-V*-Cf is a positive integer. There is no extra congruence
condition on Y, no appeal to cofinal choices of a fixed quotient, and no
circular dependence of an earlier witness on n.

## Exact algebra and literal-circuit evidence

The independent script reconstructs all sixteen linear radical factors
in a five-variable integer polynomial ring. Their full product has 495
terms; replacing the four even root powers by the four radicands and
clearing delta^8 gives exactly the literal graph's norm, also 495 terms.
It separately checks all 62 named local circuit identities against a new
transcription of the printed equations, graph topology, full liveness,
the ten-variable list, the four fixed ports, and every charged operation.

Negative controls preserve operation count and liveness:

1. Replacing the final norm scalar 64 by 63 fails the exact full-norm test.
2. Replacing Told by T in cT fails the exact local identity.
3. Replacing Told by T in L fails the exact local identity.

A count, a hash, or sampled evaluations alone would not justify the new
reduction. Here the norm and local identities are complete symbolic
polynomial equalities. The 270 rational inequality diagnostics include
h>=q and very large h; they are supplementary checks, not the proof of
the inequalities.

## Exact degree and nonzero leading form

The formal Laurent proof was reviewed independently. Scaling all ten
unknowns by lambda gives K=M*H degree 11, V degree 38, Cf degree 16, ell
degree 10, b0 degree 10, and delta degree 42. The exact defects imply:

- K*(sqrt(Dt)-ell) has degree at most 12.
- K*(sqrt(Df)-Cf) has leading term -K*I^2/(2Cf), degree 17.
- K*(sqrt(Dy)-V) has degree at most 7.
- M*(sqrt(Dd)-b0) has degree at most 11.
- Z-K*(ell+Cf+V)-M*b0 has degree at most 15.

These orders are valid in the Laurent field over the rational-function
field of the inputs. Each radicand has a square leading coefficient, so
the chosen formal branches exist; this imposes no restriction on integer
witnesses.

The sixteen linear factors have degrees 49 (eight factors), 27 (four),
21 (two), and 17 (two). In the last pair the strong-root defect of degree
17 dominates even the main-root center of degree 16, independently of its
sign. Thus all leading factors are nonzero. The exact product degree is
576, and clearing delta^8 adds 336, giving 912.

The independent script simplifies the product of those actual leading
factors, not merely the claimed exponent sum, and obtains

    2^44*(3*beta*j)^558*i^38*(eta+zeta)^86
         *X^68*s^154*(T+F+alpha)^8.

The coefficient of j^558 i^38 eta^86 X^68 s^154 T^8 is
2^44*(3*beta)^558>0. Four independent exact univariate specializations of
the literal graph over two finite fields attain degree 912 with the
claimed leading coefficient. These verify attainment and graph agreement;
the universal upper bound is the Laurent proof, not finite sampling.

## Coefficients and repaired provenance details

The four actual payloads are present, minimally encoded, and agree with
both their raw/compressed hashes and the retained source44 binding:

- beta: 590069 bits.
- K0: 592884 bits.
- MC: 590069 bits.
- MF: 590070 bits, already shifted exactly once.

The local source pins were checked byte-for-byte. The review independently
parsed all 430 transitions from the pinned k215.tm and compared them,
entry-for-entry, with the supplied transition JSON.

Two packaging defects found during review were repaired by the author:

- UPSTREAM_BINDING.json referenced a historical filename not shipped in
  this packet. It now resolves to the actual retained binding file.
- The historical binding records the hash of a different transition-JSON
  serialization, not the packet's reconstructed minimal JSON. The packet
  now explicitly documents both hashes, pins its local JSON, and checks
  its exact transition equality to the pinned machine before rebuilding
  coefficients. The historical binding itself and the four coefficient
  byte values were not changed.

This distinction avoids claiming byte identity where only the transition
semantics and regenerated coefficients agree.

## Reproduction

From a Python environment with SymPy installed, run:

    python independent_review.py
    python -O independent_review.py

The review script resolves the original packet at
../../positive/ten_centered relative to this directory. The two machine
receipts and complete logs accompany this review. The source packet's own
standard-library-only normal/-O verifier is a separate reproduction path;
it is not a dependency of this independent check.
