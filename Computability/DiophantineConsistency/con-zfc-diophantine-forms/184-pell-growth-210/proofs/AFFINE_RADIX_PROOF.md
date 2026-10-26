# The CRT index also supplies an affine self-radix base

## Exact result and semantic interface

This is a new ordinary arithmetic reduction of the incoming CRT-index-anchor
source. It is not merely a polynomial coordinate identity, because the
self-radix power request is changed. Its soundness and completeness are proved
below. All other source equations and all principal Pell pairs are retained.
The mathematical argument composes with the inherited numerical-calculus and
ZF/ZFC calibration; no new end-to-end proof-assistant build is claimed.

The old base was

    D_old = B [2+4(C+A_1+...+A_8)].

Replace it by

    D = 2(C+F+1),             q = D^x.

The second equality is still certified by the original finite polynomial Pell
request. It is not an exponentiation operation in the delivered equation.
The retained CRT-index divisibility equation is

    B eta = C+F+1.

Thus D is a multiple of B without requiring a product gate in its definition.
The actual representative C is even and has the existing principal Pell pair
used as the semantic anchor. F is even and positive, authenticated before the
radix bootstrap by the unchanged growth request (or by any replacement growth
certificate with the same proved interface). All variables are unrestricted
integers before the signs are recovered.

In the uncontracted source the coordinate indices are F=x2, C=2*x17, and
D_old=x194. The old base-definition residual is deleted, and every occurrence
of x194 is replaced by

    2+2*x2+4*x17.

This is affine. Consequently every residual remains quadratic, and compaction
removes exactly one coordinate and one residual. The full square frame must
undergo this same substitution: it now bounds the actual affine D. Reusing the
old numerical frame without this update would be invalid.

## 1. Retained Pell interpretation, with no sign circularity

The shared square frame includes every actual requested base, output and
nominal exponent, including D. The unchanged frame and anchor argument gives
W>=258, |A|>W^W, and canonical signed-index Pell coordinates for each retained
principal pair. This argument precedes the arithmetic bootstrap and does not
use the meanings or signs of B, q, the representatives, or eta.

The relocated anchor proof also gives C!=0 and, for every other principal
nominal exponent k,

    |k| < |C|.

This follows first for the absolute classified indices from the anchor cap,
then for the actual signed nominal indices from the orientation pool. It
applies in particular to t, F+t, x, y+1, the growth index, and the eight other
CRT representatives. The C pair itself is the anchor.

Once the first growth request is interpreted, t>=16 and F is even, positive,
and at least t^t. The stronger growth estimate used for label separation is
retained unchanged. Since C is even, C+F+1 is odd and therefore nonzero. The
literal identity B eta=C+F+1 implies that B and eta are odd and nonzero. Hence
D=2(C+F+1) is congruent to 2 modulo 4 and |D|>=2, with no sign assumption on C.

The signed canonical power lemma at base D now gives

    x>=0,                    q=D^x.

It cannot be replaced with a positive-base-only lemma at this point.

## 2. Bootstrap of x, y, C and the radix

The retained affine beta spacing is y=F(2v+1). Thus y!=0 and |y|>=F.
The retained terminal beta endpoint is

    x=1+[1+(t+1)y] u_t.

If x=0, the nonunit integer 1+(t+1)y would divide -1, impossible. Thus x>=1
and |q|>=2. The retained q-power request at exponent y+1 now forces y+1>=0.
A negative y would satisfy y<=-F<-1. Therefore y>=F>0.

The initial endpoint is

    x=F+1+(y+1)u_0.

If u_0<=-1, then x<=F-y<=0, a contradiction. Thus u_0>=0 and x>=F+1.
The terminal endpoint then forces u_t>=1 and gives the stronger inequality

    x>=2+(t+1)y>=2+(t+1)F.

In particular x>=7 and |q|>=2^x. Therefore |q+1|>=2. The retained q+1
requests force all nine actual CRT representatives, including C, to be
nonnegative. Since C!=0, it is positive. Their requested indices and the
anchor inequality now show

    0<=A_i<C,        0<C,        0<F+t<C.

The new base is positive and satisfies

    D=2(C+F+1)>2C,       q=D^x>(2C)^x>0.

This proves positive q before B has been authenticated as the binomial digit.
No statement about B's sign was needed to establish it.

## 3. One digit bound for the whole arithmetic front

Every binomial upper argument in the retained common remainder system is
between zero and C: the initial argument is F+t, the ordinary column arguments
are A_1,...,A_8, and the index-column argument is C. The old derived-label
request was already removed by the incoming anchor construction and is not
silently reintroduced here.

Every lower digit cutoff k in the system is at most x. The three cutoffs are t,
y+1 and x; the inequalities above give t<x and y+1<x, and x<=x is immediate. Hence for every
coefficient encountered in a low part and for the extracted digit,

    binom(a,j) <= max(1,a)^j <= C^x < q/2^x

whenever 0<=a<=C and 0<=j<=k<=x. (For j>a the coefficient is zero.)
Consequently

    C^x/(q-1) < 2^(1-x) < 1/32.

The true low remainder of (q+1)^a modulo q^k is therefore strictly below
q^k/32. The retained normalized remainder budget gives the encoded remainder
absolute value below q^k/2. Their difference is a multiple of q^k and has
absolute value below q^k, so they agree exactly.

This uniform argument replaces both the special first-binomial estimate and
the old use of the sum-majorant H for the other column binomials. It does not
assume the individual representatives were independently range bounded: their
common upper bound C comes from the already authenticated anchor cap.

## 4. Authentication of B and the modulus needed by the range compiler

The initial digit equations now give

    B = binom(F+t,t) modulo q.

Because B eta=C+F+1 and eta is a nonzero integer,

    |B| <= |C+F+1| = D/2 < q/2.

The true coefficient is below q/2^x<q/32. The congruence therefore implies

    B = binom(F+t,t)>0.

The binomial is at least two. Its retained power request consequently gives
N=B^x>0. In fact the exact identity N=B^x is available before positivity by
the signed power lemma, including its unit-base case; positivity is sufficient
for the ordinary range compiler and is all that is used here.

The CRT-index divisibility is precisely the missing link in replacing the
old factor B in the explicit base expression:

    D=2 B eta,
    q=D^x=B^x(2 eta)^x=N(2 eta)^x.

Thus N divides q. Omitting this fact would break the inference from high
binomial-digit quotients to binomial divisibility by N. The new proof retains
it exactly. Eta is positive once B,C,F are positive and is odd. Therefore
D/B=2 eta is congruent to 2 modulo 4, preserving the former radix parity.

The generalized binomial-CRT theorem, the local polynomial bound below 2^x,
the beta decoding, label-product separation, Horn-flow extraction, and the
logical calibration then apply with the same hypotheses. The changed base
introduces no new guard and removes none of those arithmetic requirements.

## 5. Constructive completeness and order of choices

Start with a finite calibrated refutation. Choose the same cofinal horizon
and growth value F as in the parent. Its binomial B is odd. Choose the beta
spacing and beta code x, so N=B^x and all CRT moduli are fixed. Choose the
eight non-anchor CRT representatives first, and then choose C even and
arbitrarily large in its prescribed residue class modulo N^2. In particular,
choose it larger than every other requested nominal index and representative.
This is possible because N^2 is odd and the progression of permitted even
representatives has step 2N^2.

The retained CRT assignment guarantees B divides C+F+1. Set

    eta=(C+F+1)/B,    D=2(C+F+1),    q=D^x.

Only now choose the shared frame center and canonical Pell pairs. These
choices are acyclic: F,B,x,N and the CRT moduli are independent of C; q is
chosen after C; the Pell frame is chosen after q. The same even C anchor
completion applies. The inequality D>2C gives the uniform digit estimates
above, while N|q supplies every needed range congruence. The resulting true
remainders are small enough for the unchanged common ternary norm budget,
whose slack remains nonnegative and hence has a ternary representation.

The individual and pooled power equivalences provide all exact quotient
witnesses. Every local proof and beta equation is unchanged. This constructs
an integer solution of the new source from every finite calibrated refutation.
Together with soundness it proves the required existence equivalence.

## 6. Measured literal compilation

The builder uses only the supplied incoming package's sparse arithmetic,
common-Hessian projection, and affine-consequence helpers. For the count-first
anchor219 source it emits 218 coordinates and 157 residuals; the five existing
Hessian projections leave 213 coordinates, and one affine projection leaves
212 coordinates and 151 residuals. Degree is exactly four. Before coordinate
or row-height optimization, this 212-coordinate form has 7,291 collected
monomials and the inherited large coefficient height
2,417,851,639,242,452,488,945,685.

For the small-coefficient anchor221 source the same source reduction emits
220 coordinates and 159 residuals, then 215 and 154 after the five radical
projections. The affine projection gives 214 coordinates and 153 residuals, with 7,395
collected monomials and unoptimized coefficient height 13,607,065,661.

These outputs are a semantic reduction plus exact algebraic projections.
Their immediate unoptimized coefficients are not claimed to dominate the
parent's already optimized support. The reduction can be composed with an
independently proved replacement of the growth certificate.


## 7. Extension to an initially signed growth ordinate

The composition with the standalone Pell-ordinate construction only knows
that F is even and |F| is very large at the beginning. This does not break
the radix argument. Because C and F are even, D=2(C+F+1) is still nonzero
and |D|>=2. The same terminal endpoint excludes x=0, so x>=1 and |q|>=2.
The q-power at y+1 then forces y>=|F|>0. If x=1, the initial endpoint
would give (y+1)u_0=-F, impossible because 0<|F|<=y<y+1. Hence x>=2.
The terminal endpoint now gives u_t>=1 and x>=2+(t+1)y. In particular
|q+1|>=2. The q+1 request with nominal index F+t forces F+t>=0. The
standalone growth theorem gives |F|>t, so F cannot be negative. Therefore
F>0, and all of Sections 2--5 applies. This recovers the growth ordinate's
sign from an already retained power request, without an additional guard.
