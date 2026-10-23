# A finite additive code for quartic coefficient extraction

## Result and attribution

The 31 source variables need not occupy the digit positions `5,5^2,...,5^31`.
The only use of these positions in Sun's coefficient-extraction proof is to
make all monomials of total degree at most four occupy distinct exponents.
A 32-element Bose--Chowla B4 set, with one element translated to zero, gives
the required property. This is an application of classical additive coding,
not a new B4 construction or new general unknown-count theorem.

The frozen weights are the 32 entries of `weights_certificate.json`, starting
with zero and ending at W=610895. The first entry is the padding coordinate;
the other entries are assigned in order to the 31 source variables.
The source input a is specialized to zero, so it needs no digit position.

Primary sources used:

* R. C. Bose and S. Chowla, *Theorems in the additive theory of numbers*,
  Commentarii Mathematici Helvetici 37 (1962/63), 141--147.
  Original paper: https://www.cs.umd.edu/users/gasarch/COURSES/858/S13/BoseChowla.pdf
* Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*, Sci. China Math.
  64 (2021), 281--306, arXiv:1704.03504v7, Lemmas 2.2, 2.4, 2.6 and
  the proof of Theorem 3.1. https://arxiv.org/html/1704.03504v7
* Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  arXiv:2609.01594v2 (2026), especially Proposition 2.1, Theorems 3.1 and
  4.1, Propositions 6.1--6.2. https://arxiv.org/html/2609.01594v2

The concrete coefficient identity and its full proof are stated below.
The complete carry and size argument is independently supplied in the
companion audit notes. The ten-integer finalizer is unchanged from source31.

## Explicit construction of the finite set

Work in the quotient R=F2[x]/(x^20+x^3+1), with theta the class of x.
The supplied standard-library script enumerates all 2^20-1 nonzero bit
patterns as consecutive powers of theta, returning to one on the next step.
Thus every nonzero element is a unit, so R is a field and theta is primitive.
This finite check avoids relying on a table of primitive polynomials.

Let Q=2^20-1=1048575 and q=32. Its subfield F32 consists of zero and
the 31 powers theta^(33825j), 0<=j<31. These are exactly the roots of
u^32=u. Frobenius shows that this set is closed under addition and
multiplication. Since theta has order Q, it cannot belong to F32 or F1024;
its degree over F32 is four.

For each a in F32, let e(a) be the unique exponent in [0,Q) such that
theta^e(a)=theta+a. The 32 logarithms are listed as `raw_logs` in the JSON.
Suppose the sums of two multisets of four such exponents agree modulo Q.
Exponentiating gives equality of products of four factors theta+a.
The difference of the two monic degree-four polynomials product(T+a)
has degree at most three and vanishes at theta. Because theta has degree
four over F32, the difference is the zero polynomial. Unique factorization
then gives equality of the two multisets.

Multiplication by 208418 is invertible modulo Q. Apply that multiplier to
every e(a), translate by -97920 modulo Q, and take the sorted representatives
in [0,Q). These operations preserve uniqueness of four-term sums modulo Q.
The translated set contains zero. The result is

    0, 51609, 55430, 68596, 78030, 89463, 90233, 110498,
    110508, 128615, 136498, 211819, 241519, 305379, 312706,
    314312, 369115, 417382, 429683, 435112, 450230, 462314,
    469608, 490199, 501539, 507151, 524944, 550792, 559943,
    573626, 607799, 610895.

The integer maximum is W=610895. The multiplier was found by a finite scan
of units modulo Q and the translation removes its largest cyclic gap,
437680. No optimality among all B4 sets is claimed or needed.

Independently of this construction, `weights.py` enumerates all
binomial(35,4)=52360 nondecreasing four-tuples and verifies that their sums
are distinct modulo Q. It also provides an SHA256 checksum of the ordered
enumeration. Integer equality implies equality modulo Q, so the verification
also proves uniqueness as ordinary integer sums.

## Quartic coefficient-extraction theorem

Let w0=0<w1<...<w31=W be the displayed weights. For an exponent vector
alpha=(alpha1,...,alpha31) of total degree at most four, set

    e(alpha)=sum_i alpha_i w_i.

Pad alpha by 4-|alpha| copies of the zero weight. Uniqueness of four-term
sums implies that e(alpha)=e(beta) only when alpha=beta, for every pair
of exponent vectors of total degree at most four. This is the full simplex,
not merely the monomials present in the source polynomial.

Write P(n)=sum_alpha p_alpha n^alpha for the fixed source quartic and define

    c_alpha=(4-|alpha|)! product_i alpha_i! p_alpha,
    H=4W,
    D(t)=sum_alpha c_alpha t^(H-e(alpha)).

All exponents of D are nonnegative. For any n1,...,n31, the coefficient
of t^H in

    (1+sum_i n_i t^w_i)^4 D(t)

is exactly 24 P(n).

Proof. A product of a term indexed by beta in the multinomial expansion
with the reversed term indexed by alpha contributes at degree H precisely
when e(beta)=e(alpha). Hence only alpha=beta contributes. The multinomial
coefficient 4!/((4-|alpha|)! product_i alpha_i!) cancels the corresponding
factor in c_alpha. Summing the remaining terms gives 24P(n). QED.

The total degree of this univariate product is at most H+4W=8W.
No residual term can contaminate the distinguished coefficient.

## Why the old numerical coefficient bound still suffices

Let L=max_alpha |p_alpha| and retain the source31 constant
beta_S=2^4269882. Its existing coefficient certificate gives

    beta_S > 33^4 * 4! * 2L.

The new construction changes exponents, not P or its weighted coefficients.
Thus the same bound remains applicable without recomputing the parent tuple.
In particular, for b>=4 and B=beta_S*b^4 we have

    B/2 > 24L*(1+31(b-1))^4.

Each coefficient of D has absolute value at most24L, because its exponents
are distinct. For 0<=n_i<b, each coefficient of the product above has
absolute value strictly below B/2. Adding B/2 to every coefficient through
degree8W therefore creates strictly positive base-B digits less than B.
The distinguished digit equals B/2 exactly when P(n)=0. This is precisely
the one-digit no-carry test in Sun's Lemma2.6, with new positions.

Since P(0)>0, the leading coefficient of D is 24P(0)>0. Every other term
has exponent below H. As 24L<B-1,

    |D(B)-24P(0) B^H| < B^H,

so D(B)>0. This positivity is used even before g has been decoded.

## Complete replacement formulas

For the integer variables f,g put b=1+3f and B=beta_S*b^4. Let

    ell=sum_i B^w_i,             H=4W,  Jtop=8W,
    D=sum_alpha c_alpha B^(H-e(alpha)),
    N0=B^(W+1),                 N1=4B^(8W+1),
    N=N0*N1=4B^(9W+2),
    mask=N0-1-(b-1)*ell,
    T=mask+(B-2)B^H*N0,
    J=2(1+g)^4*D+B*sum_(i=0)^Jtop B^i,
    S=g+J*N0,
    R=(S+T+1)*N+T+1,
    X=(N-1)*R,                  Y=N^2,
    Ccap=b*B^W.

All remaining Sun/source31 bridge and norm formulas are unchanged.
Here H=2443580, Jtop=4887160, N exponent9W+2=5498057.

The sums and powers have fixed, explicitly bounded integer indices; all
are ordinary polynomial expressions and can be compiled to binary +,-,*
gates. No digit-extraction, divisibility, primality test, exponent variable,
radical, or finite-field operation occurs in the final equation.

## Bounds needed before decoding

Assume f!=0, b is a square, and 0<=g<2Ccap. Then b=1mod3 forces
f>0 and b>=4. In particular 2b<=B, so g<N0. The mask has digits B-b
at the selected w_i and B-1 elsewhere, hence0<=mask<N0.
Since H<=8W, the displayed T satisfies0<=T<N.

For the remaining bound use g+1<=2bB^W and

    2*24L*(2b)^4 < B-2.

The bound on D and the two geometric sums give

    0<J
       < ((B-2)+B)/(B-1) * B^(8W+1)
       =2 B^(8W+1)
       <N1.

Thus0<=S<N. Also beta_S is an even power of two and b=1mod3,
so B=1mod3 and N=1mod3. Consequently3 dividesX. Moreover
R>=N+1>B>=b, N>=4, and Y=N^2>max(b,256), so X>3b.
These are the exact source size hypotheses needed for the unchanged
Lucas/binomial bridge, including their strict versions.

When b is additionally a power of two, B,N0,N are powers of two.
Sun's arbitrary-position mask lemma decodes g into 31 digits n_i<b.
The quartic identity above makes the second block's no-carry test
equivalent to P(n)=0, and his carry-to-binomial lemma gives

    Y divides binomial(2X,X) iff the two-block carry count is zero.

The positive direction chooses b=2^(2s) sufficiently large with b=1mod3,
so f=(b-1)/3 is arbitrarily large; because P(0)>0, any root has a nonzero
coordinate and its packed g is at leastB>=b. It also satisfies g<Ccap.
The reverse direction decodes a zero of P from the preceding equivalences.
This establishes the required generalized source proposition in full.

## Scope of the result

This transformation makes an enormous reduction in the degree caused by
source-variable packing. It preserves the ten unrestricted integer
unknowns of the Sun/source31 finalizer. It does not reduce their number,
prove global minimality, settle Con(ZFC), or provide a new formal proof
assistant certificate. All coefficient and machine/compiler dependencies
of the fixed source31 quartic remain explicit and unchanged.
