# Nine positive or nonnegative unknowns using the same sparse quadratic source

## Result and domain

The primary equation in generated/multitarget_nine_positive.json has nine
strictly positive integer unknowns, 682 live binary arithmetic operations,
and exact total degree 33,332,620. The companion natural-domain equation
has nine nonnegative unknowns, 685 operations, and the same degree. The
equations are not asserted to have the consistency property over all integers.

The positive equation improves on package45's 788 operations and degree
129,875,980. It uses the same established Jones ratio and norm finalizer,
with the new sparse source of this package. The underlying parent is the
raw31-variable quadratic parent from package40; package45 used a shifted
60-operation variant. We do not assert pointwise equality with package45's
polynomial. Both parent presentations have the inherited calibration to
finite ZFC refutations, with the same complete native coefficient tuple.

The final polynomial is exactly the formula in sections4--5 of the copied
upstream/PACKAGE45_NINE_PROOF.md, after replacing its two-variable source
by the source given here. Those sections include the complete ordinary
proof of the finalizer and the precise Jones ratio theorem dependencies.
The following argument checks every source hypothesis needed to use them.

## 1. Coefficients and source

Use the original22 raw quadratic residuals and the same 94 weighted
coefficients, weights w_i, and targets E_j certified in ../SOURCE_PROOF.md.
In particular W=max w_i=799, Hmax=max E_j=7243, Kcode=Hmax+2W=8841.
The support-sensitive extraction identity is exact, and D(B) has leading
coefficient2 at exponent7243. The input coordinates of the parent remain
strictly positive.

Every weighted coefficient satisfies |c|<Mcoef=2^2134927. This uses the
same port-bit bounds as package45; build_nine.py checks the stronger exact
recipe bound for every new coefficient. Set the fixed ordinary integer
b_floor=2^2134939=4096Mcoef. Its complete binary payload is supplied.

First use a mixed domain epsilon,phi,n>=0 and g,h,s,w,i,j>=1. Define

    b=b_floor+epsilon, B=b^3, ell=sum_i B^w_i,
    Dcode=sum_(j,alpha) c_(j,alpha) B^(E_j-alpha.w),
    N0=B^(W+1), N1=4B^(Kcode+1), N=N0*N1,
    Mask=N0-1-(b-1)ell,
    Targets=sum_j B^E_j,
    Tcode=Mask+(B-2)*Targets*N0,
    Jcode=2(1+g+ell)^2*Dcode+B*sum_(k=0)^Kcode B^k,
    Scode=g+Jcode*N0,
    R=(N-1)*[(Scode+Tcode+1)*N+Tcode+1],
    Gcap=32*b*B^W.

The main changes from package45 are that the raw parent is retained,
the digit successor is added once as ell inside Jcode, and the targets
are the individually certified sparse positions.

## 2. Unconditional positivity and the broad range

Because Dcode has leading coefficient2 and every other coefficient has
absolute value less than Mcoef, and B-1>Mcoef,

    Dcode>2B^Hmax-Mcoef*sum_(k<Hmax)B^k>B^Hmax>0.

This is independent of g. The low mask is positive, as in the package40
source proof; hence Tcode,Jcode,Scode>0 on every outer assignment.
Therefore R>=N>=8 and R>=b. Also Gcap,b>0, so every unconditional numerical
hypothesis of Jones's ratio bridge is satisfied.

Suppose g<4bB^W. Integrality gives1+g<=4bB^W, while ell<2B^W.
Since b>=b_floor>=2,

    1+g+ell<5bB^W,    g<N0.

Using Dcode<Mcoef*B^(Hmax+1)/(B-1), the sparse part of Jcode is less than

    50*Mcoef*b^2*B^(Kcode+1)/(B-1).

Because b>=4096Mcoef, 50Mcoef*b^2< B/64, so after adding the geometric
mask the result is strictly below4B^(Kcode+1)=N1. Thus0<Scode<N.
Also0<Tcode<N follows from (B-2)Targets<B^(Hmax+1)<N1.
No polynomial-zero or digit-validity premise was used in these bounds.

## 3. Exact source equivalence

Assume in addition b is a power of two. Then B,N0,N1,N are powers of two.
The central-binomial identity in the copied package45 proof gives

    N^2 divides binomial(2R,R)
       iff no binary carries occur between Scode and Tcode.

The low word forces g=sum_i z_i B^w_i with0<=z_i<b. Set p_i=z_i+1.
The exact support-sensitive coefficient identity gives

    [Z^E_j](1+sum_i p_i Z^w_i)^2 D(Z)=2r_j(p).

Every coefficient has magnitude at most

    Mcoef*(1+sum_i p_i)^2 <= Mcoef*(32b)^2 <= B/4 < B/2.

The high mask therefore forces every r_j(p)=0, exactly as in
../SOURCE_PROOF.md. This proves soundness of the new source for every
0<g<4bB^W.

Conversely, given a positive parent solution p, choose an arbitrarily
large power of two b>=b_floor with b>max p_i. Let epsilon=b-b_floor and
g=sum_i(p_i-1)B^w_i. The all-ones parent tuple is not a solution, so g>0.
The geometric bound gives g<bB^W, hence32g<Gcap. Both no-carry tests hold,
so N^2 divides binomial(2R,R). This is precisely the stronger completeness
condition required by Jones's ratio_complete theorem.

The ratio_sound theorem produces8g<Gcap, hence g<4bB^W, before source
soundness is used. There is no circular assumption that the base is binary
or that g already decodes a parent solution.

## 4. Finalizer, consistency equivalence, and coordinate translations

Use sections4--5 of upstream/PACKAGE45_NINE_PROOF.md verbatim for the
polynomial tail and its proof. Their required premises have all been
proved above. The completed equation has a zero in the mixed domain iff
the positive quadratic parent has a solution. The inherited parent/K215
calibration makes this equivalent to a finite ZFC refutation.

For nine positive coordinates, replace epsilon,phi,n by their coordinates
minus1 and retain the six coordinates already positive. For nine natural
coordinates, retain epsilon,phi,n and replace each of g,h,s,w,i,j by its
coordinate plus1. These are bijections of the respective witness domains.
Negating solvability yields the stated ZFC-provable equivalence to Con(ZFC).

The native compiler and Jones arithmetic results are inherited ordinary
mathematical dependencies. This package supplies explicit circuits and
finite audits, not a new end-to-end Lean/Rocq or object-level ZFC derivation.

## 5. Exact degree

Let t=deg N=3(Hmax+3W+2)=28,926. On the diagonal where every outer variable
is one indeterminate, N has leading coefficient4 and R has degree3t and
leading coefficient16. The newly translated sparse term in Jcode has
upper degree3Hmax+6W=3Kcode, while the geometric term has degree
3(Kcode+1). Thus the geometric term still strictly dominates; the packed
successor translation does not change the tail degree formulas.

The exact degree ledger in section6 of upstream/PACKAGE45_NINE_PROOF.md
applies with this new t and unchanged W=799. Its telescoping identity

    V1^2-a1
      =(C^2-1)(AE)^2(GH)^2
       +D(E^2-1)(GH)^2+DF(H^2-1)

resolves the leading cancellation in the primary equation. The separate
700-operation positive certificate circuit and703-operation natural
certificate circuit evaluate the same polynomial using that identity.
Its total-degree upper bound is

    1152t+12W+280=33,332,620.

The diagonal leading coefficient is exactly2^2050, independently of the
native coefficient tuple. In particular it is nonzero. The audits also
certify it modulo three primes using the actual fixed coefficients.
The primary circuit has only682 (or685) operations; certificate circuits
are not the primary evaluators and are not used for the operation claim.

## 6. Reproduction

Run from this directory:

    python3 build_nine.py
    python3 verify_nine.py

The verifier checks all live gates, the domain bijections,60 independent
literal source/tail replays, the cancellation-resolved polynomial, the
exact abstract telescoping identity, and the degree certificate modulo
three primes. ../code/verify_source.py supplies the independent exact
symbolic extraction and parent-binding certificate shared by both domains.
The checks remain active with python -O.

## 7. Exact evaluator sharing

The primary evaluator uses two identities that preserve the polynomial
exactly. Since Omega=u*m, its center is evaluated as

    Theta=u*(n+Mdiv-m*(2*Mdiv+V0*V1))+v.

Put b0=Omega^2*a0 and b1=Omega^2*V0^2*a1. Then

    F9=(Theta^2-b0-b1)^2-4*b0*b1.

These are arithmetic factorizations, not extra constraints or new
variables. They save three binary operations relative to the direct
685-operation implementation of the new source with the inherited tail.
The700/703-operation degree certificate forms remain separate equal-
polynomial evaluators.
