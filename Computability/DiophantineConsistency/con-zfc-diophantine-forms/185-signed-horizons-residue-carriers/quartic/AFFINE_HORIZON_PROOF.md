# Signed affine horizons: one fewer unrestricted integer in a direct quartic

## Exact contribution and scope

The source is package 173, `crt-index-anchor-215`, at repository commit
`02a78a08603cbae248c19c23a75907c6c6bd6443`. Its completed213-variable
and215-variable quartics are retained byte-for-byte in `p213/equation.json`
and `p215/equation.json`. Source hashes are checked by both included scripts.

The new idea is to let an existing power certificate recover the sign of
the proof horizon. A signed affine progression replaces the old positive
quadratic progression, removing one independent coordinate at degree 4.
This is a change of arithmetic source, followed by an exact polynomial
substitution. It is **not** a bijection between the old and new polynomial
zero sets: the two cofinal sets of permitted horizons differ.

The resulting equation is always the explicit sum of the squares of its
listed quadratic residuals. All coordinates range independently over Z.
The equations contain no variable exponentiation; power notation in this
note describes what retained Pell certificates prove.

The recommended small-coefficient profile is `p214_scaled_square`:

*214 unrestricted integers, 153 quadratic residuals, exact degree 4,
5,875 collected monomials, coefficient height 655,360.*

Its semantic parameters are

    t=8+16z, U=2t^2, K=512U^2=2048t^4, F=t^K.

The smaller-dimensional profile `p212_minimum8` has212 unrestricted
integers, 151 quadratic residuals, exact degree 4, 5,706 monomials, and
coefficient height 316912650058804747029598371840. It uses

    t=8+16z, K=1048576t, F=t^K.

The larger coefficient reflects substitution of K into the squared
Pell frame. The baseline source equations remain included for transparent comparison.

## 1. A parameterized horizon lemma

Let ell=2^20. Fix an integer m>=8 divisible by 4 and impose

    t=m(2z+1), z in Z.

Then t is divisible by 4, never zero, and |t|>=m. Retain the source's signed
Pell anchor, full square frame, orientation certificate, and actual power
requests. Consider either of these two growth choices:

1. K=ell*t, with the existing request F=t^K.
2. U=a*t^2, K=b*U^2, where a,b are fixed positive integers satisfying
   b*a^2*m^3>=ell, with the same request F=t^K.

At every zero of either modified source, t>=m. Once this is proved,
K>=ell*t and F>=t^(ell*t), as required by the existing label-separation
argument. Every finite C222 refutation has a solution of the new source.

### Pell information available before signs

Package173's `C_ANCHOR_THEOREM.md`, Section 2, derives canonical signed
Pell coordinates before the signs or arithmetic meanings of t,F,B,q or
the encoded row index C are known. The square-frame argument uses their
squares, the even parameterization C=2c, and the private comparison
congruences. It does not use the old quadratic horizon equation.

The frame still includes every actual base, index and output, in particular
t and the changed K. It has W>=258: in the affine-index case its K^2 term
already dominates 258 because |K|>=ell*m; in the quartic-index case the
integer identity K=b*a^2*t^4 gives the same conclusion. Consequently the
signed power lemma applies to every retained request with base of absolute
value at least 2. Such a request forces a nonnegative exponent and its exact
integer power. This is the signed version of the same Pell congruence and
large-modulus argument used by the pinned source, not a presumption that
the requested exponent is already positive.

### Affine-index case

Here |t|>=m>=8, so the existing request at base t forces K>=0. Since
K=ell*t and ell>0, t>=0; its nonvanishing gives t>=m. No other arithmetic
sign is needed. The remaining source proof can now proceed in its old order.

### Quartic-index case

Initially t may be negative. Nevertheless K=b*a^2*t^4 is a positive even
integer. The first exact power therefore gives F=t^K>0, and F is even.
The actual encoded row index is C=2c. The retained index congruence is

    B*j=C+F+1.

Its right side is odd. Thus B is an odd nonzero integer. The self-radix
base is BH, where

    H=2+4(C+A1+...+A8).

This is2 modulo 4, even before the actual CRT representatives Ai are
interpreted. Therefore |BH|>=2. Its retained power request gives

    q=(BH)^x, x>=0.

To exclude x=0, use the retained beta endpoint, not a binomial digit:

    y=F(2v+1), g=1+(t+1)y, x=1+g*u_t.

Here |y|>=F and |t+1|>=m-1>=7. Hence

    |g| >= (m-1)F-1 > 1.

If x=0, the last equation would imply g*u_t=-1, impossible for integers.
Thus x>=1 and |q|>=2. The retained power request is **q^t**; its signed
power lemma forces t>=0. Since t is nonzero, t>=m. Some older prose calls
this request q^(t+1); the literal request list uses q^t, which proves the
needed conclusion directly.

This repairs a tempting invalid shortcut. At q=1 the binomial digit row
only yields 2^(F+t)=B+high, where high is an unrestricted quotient. One
cannot conclude B=2^(F+t) or exclude x=0 by parity through that row.

## 2. Why the minimum can be8

The sharper source file `CONSTRUCTOR_DEPTH.md` proves the needed bound
already for t>=8. For nonnegative integers r,s<T,

    E(r,s) <= 8T^2-2T+1 < 8T^2,

and the three other square-shell constructors are no larger. Thus inputs
strictly below t^e produce an output strictly below
8t^(2e)<=t^(2e+1). Starting from strict leaf bounds, constructor depth d
gives exponent2^(d+1)-1. The deepest actual schema has depth19, so every
local label is below t^(ell-1). The sum of the labels need not itself be
below this bound; that derived sum was removed by package 173.

Put L=t^ell. Since K>=ell*t, F>=L^t. The package's boundary-valid
finite-product separation theorem therefore recovers exact Horn label
multiplicities. Its proof admits equality F=L^t.

Two numerical estimates in the more conservative source presentation
used t>=16. They remain true, with the following explicit replacements:

* F>=8^(8ell)>2^64, so the beta endpoint amplification supplies x>2^32
  and the same local-polynomial size bound Local<(2x)^(2^23)<2^x.
* Since K>=ell*t>=2t and t>=8,
  F>=8^(2t)>16^t>lcm(1,...,t)^2. The source's generalized binomial-CRT
  selector therefore has at least its required radius.

The bound x>=2+(t+1)y and y>=F gives 2+t+x+y+F<2x for these values,
so the local-size comparison is unchanged. All digit estimates use this
large actual x; a weaker bare lower bound x>=t+1 is not substituted for it.
The construction is factorial-free; no nearest-factorial rounding lemma
with an independent t>=16 hypothesis is invoked.

Finally v_2(F)=K*v_2(t)>=ell*t exceeds both floor(log2 t) and v_2(t!).
Hence binom(F+t,t) is odd, and F times a suitable positive odd integer
can still supply the beta spacing divisible by t!. The cofinal even-CRT
anchor argument is unchanged.

## 3. Soundness and completeness

After Section 1 recovers the sign of t, Section 2 supplies the same growth,
label, local-value and CRT bounds as the pinned ordinary source proof.
The normalized remainder bounds, binomial range tests, exact local Horn
identities and single-conclusion flow balance then extract a finite C222
refutation from each integer zero. The unchanged numerical-calculus/ZF
and ZF/ZFC refutation equivalences give a finite syntactic ZFC refutation.

Conversely, start with a finite C222 refutation and choose t=m(2z+1)>0
larger than its number of steps and all local free parameters. This set
of t values is cofinal. Define K and F as above, form the finite pending
multiset states, and choose an odd beta multiplier large enough for all
states while supplying the odd part of t!. Its 2-adic part is provided
by F. Choose the beta code x and every-prime CRT residues as in package 173.
Because the binomial modulus is odd, its encoded index C can be selected
even and larger than every other requested index, including the new K.
Only then choose H,q and the shared Pell frame. The source's private
comparison construction fills every remaining certificate. These choices
are in the same noncircular order as the pinned proof.

This gives the desired ordinary ZFC proof:

    ZFC proves: P has no integer zero iff Con(ZFC).

No consistency hypothesis is used. This proves the equivalence, not
either side of it, and does not constitute a new end-to-end Lean or Rocq
certificate. The inherited calibration remains explicitly identified.

## 4. Binding the semantic change to the literal quartics

For the213-variable source the unique `cofinal.horizon` row is
t-16-4z^2. Replace it by t-m-2mz. For the215-variable source it is
t-128-4z^2; perform the same replacement. When the quartic growth index
is rescaled, change only its two defining rows to U-a*t^2 and K-b*U^2.
Every other source row is retained.

Substitute t=m+2mz into every remaining residual and delete the new
linear horizon row and the t coordinate. This is an exact bijection
between zeros of the **modified** source and the emitted residual system:
the inverse simply restores t=m+2mz and the deleted row. Affine
substitution preserves degree at most 2, so the sum of squares remains
quartic. Every final variable is live.

For the recommended214-variable profile, a=2,b=512,m=8. Its two additional
elementary residual operations subtract twice the square-definition row
from the frame row and add that square-definition row to the orientation
row. They remove duplicated t^2 terms and have integral inverse row
operations. They change the sum-of-squares polynomial while preserving
its zero set.

The source replacements also commute with the inherited six coordinate
eliminations and optimization chain. The retained fourteen certificates
show that each radical direction has zero component in t, the horizon
parameter, K and U; the affine projection eliminates a local constructor
coordinate, using only two local constructor rows. Subsequent coordinate
charts never change those protected coordinates, and no elementary row
operation uses or changes the horizon or either growth-definition row.
The independent checker verifies these exclusions while tracking all
coordinate and residual renumberings. Thus editing the protected rows of
the final pinned equation is the same arithmetic change as editing the
unprojected source and transporting it through those certified reductions.

The constructor and independent checker separately authenticate every
source hash, changed row, substituted coefficient, elementary row
operation, final monomial, liveness assertion and degree. The checker
uses a binomial substitution formula and unordered-pair SOS expansion;
it does not import the constructor. All checks also run under python-O.

## 5. Further questions

A finer positive-coefficient majorant for the actual schema trees may
permit horizons smaller than 8, with a different fixed growth exponent.
That is a separate source-bound proof and is not assumed here. Another
direction is to combine signed affine horizons with oriented pooling of
power certificates. The sign argument above is deliberately ordered so
that the first growth base and the self-radix base are known nonzero
before their exact powers are used, making that interface explicit.
