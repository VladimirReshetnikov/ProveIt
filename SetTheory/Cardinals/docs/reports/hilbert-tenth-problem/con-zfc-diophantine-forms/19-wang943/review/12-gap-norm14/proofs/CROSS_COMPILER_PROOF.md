# Five-cell compiler: exact simplification and audit

Pinned source: ProveIt commit `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.
Basis: `con-zfc-diophantine-forms/06-blank67`, with its exact K215 table.
This is an ordinary mathematical proof, not a kernel-checked theorem.

## Result

The 06 compiler uses only the five cells prior/left/center/right/following
of each 3-by-3 window. Its four corners are free. Removing these corners
reduces the selector alphabet from

    1,420,903,358,357,108,792,377
      = 38,256,607,897 * 439^4

to exactly 38,256,607,897 five-cell crosses. Replace nine copy coordinates
by five and twelve families of overlap tests by four. The same four
arithmetic ports (B-1,K,MC,MFsrc) result. No arithmetic unknown, equation,
operation, or degree changes. The coefficient B-1 now has exactly 5^36
binary digits, versus 5^67 in package 06. The reduction factor in that
bit length is exactly 5^31; the coefficients remain too large to materialize.

This change composes with any arithmetic finalizer proved for the native
ports and the inputless marked-tableau semantics. It must replace all four
ports as a unit; mixing old and new ports is invalid.

## 1. Five-cell semantics

Let a=439 and enumerate the same cell alphabet as package 06.
A cross is the tuple (u,l,c,r,d), interpreted as prior, left, center,
right, following. It is valid exactly when the package-06 center predicate
accepts the 3-by-3 window with these entries in positions (1,3,4,5,7)
and ordinary blank 0 in all corners. This is exact because the executable
predicate never reads the corners.

The distinguished crosses are

    S=(438,434,435,436,1)
    E=(438,0,437,438,437).

S is the projection of package 06's Start window. A genuine initialized Q
has this cross: its center becomes ordinary headless 1 after the first
transition. The entering state 93 appears at the neighboring cell and
need not be included in S. E has a horizontal-boundary prior and a
vertical-boundary center, so it is locally valid but violates vertical-bit
propagation at the prior cell in every global extension.

Enumerate S first, E second, and the remaining valid crosses lexicographically.
The exact center-category count of package 06 counts crosses before its
multiplication by the free-corner factor. Replaying its 13 category checks
against the exact machine gives k=38,256,607,897.

For crosses C,R,Y, impose the four equalities

    C.right = R.center, C.center = R.left,
    C.following = Y.center, C.center = Y.prior.

In a cyclic word W_i with right neighbor W_(i-1) and following neighbor
W_(i-h), write c_i=W_i.center. The identities, at i and at its neighboring
indices, imply exactly

    W_i=(c_(i+h),c_(i+1),c_i,c_(i-1),c_(i-h)).

This remains valid when indices coincide. Pullback by
(x,t) -> -x-h*t modulo N therefore gives a globally valid periodic plane.
Conversely every cyclic plane yields these overlap identities.
A Start-containing cyclic cross word exists iff the blank machine halts,
by package 06's rectangle/helical proof. That proof uses only the center
predicate, so removing corners changes none of its steps.

## 2. Exact replacement geometry

Let ell be the least integer >=2 with 2^ell>k+1 and A=2^ell. Set

    p=max(0,ceil((k-2ell-9a-4)/2)),
    jmax=5a+4+p,
    mu=A-2+sum_(j=1)^jmax A^j,
    m=2ell+14a+8+2p,
    n=m+1,
    D=n-k-5a-4,
    e*=k+12a,
    M=k+15a+D.

For the shape coordinates

    Sigma=((0,1),(1,0),(1,1),(1,2),(2,1))

define, with z=0,...,4 the index in this displayed order,

    e(r,c,s)=k+3a+(2-r)*3a+(2-c)*a+s,
    j(z,s)=1+z*a+s.

The five blocks are [k+10a,k+11a), [k+8a,k+9a),
[k+7a,k+8a), [k+6a,k+7a), [k+4a,k+5a).
They are disjoint from selectors 0,...,k-1, from dummy positions
e*,...,e*+D-1, and from anchors M,3M,9M,27M.

Native positions E are precisely these selectors, five payload blocks,
dummy positions, and four anchors. They number n.
Coefficients are

    c_i=1+sum_(z=0)^4 A^(1+za+W_i[z])+sum_(t=1)^4 A^(5a+t),
    c_e(r,c,s)=A^(1+za+s),
    c_(3^(t-1)M)=A^(5a+t),
    c_dummy=0.

Let

    Emax=27M,
    H=51M+3a+1,
    T1=H+2Emax+a+1,
    T2=T1+4Emax+2.

Take L to be the least power of 5 at least T2+2Emax+2.
Put

    U=4(n+2)(28(k+5a+4)+6)+8,
    bmin=max(ell(jmax+1)+3,ell(5a+4)+bits(U)+1,4),

and let b be the least power of 5 at least bmin. Let rho=2^b,
d=bL and B=rho^L=2^d. Every exponent and parameter is explicitly fixed.

The four ports are determined by

    DC=rho^(3a)+rho^(H+a)+rho^(8M)+rho^(24M)
       +sum_(e in E)c_e*(rho^(T1-e)+rho^(T2-e)),
    DR=rho^H,
    MF0=mu*(rho^T1+rho^T2)
       +sum_s(rho^e(0,1,s)+rho^e(1,1,s))
       +sum_s(rho^(H+e(1,0,s))+rho^(H+e(1,1,s)))
       +rho^(9M)+rho^(27M),
    MC=B-1-sum_(e in E, e!=1)rho^e-2rho^e*,
    MF=MF0+4,
    ports=(B-1,DC+B*DR,MC,MF+B-1).

The actual scalar values are in cross_constants.json. In particular,
ell=36, D=1, b=5^17, L=5^19, d=5^36.

## 3. Mask populations and carry bounds

Since pc(A-2)=ell-1 and the powers A^j are in disjoint ell-bit blocks,

    pc(mu)=ell+5a+3+p,
    m=2pc(mu)+4a+2.

The two clause-mask positions contribute 2pc(mu), the four copy-test
families contribute 4a, and the two anchors contribute 2. Thus pc(MF0)=m
and pc(MF)=m+1. The extra bit +4 is disjoint from its other terms.
In MC, the n-1 allowed low bits (all native positions except selector1),
together with the upper bit at the first dummy position, are removed
without borrowing from B-1; exactly n bits are removed. Therefore

    pc(MC)=d-m-1, pc(MC)+pc(MF)=d,
    MC=2 mod4, MF=4 mod8, 0<MC,MF<B-1.

The original conservative estimate remains valid with 9a replaced by 5a:

    sum c_e <= 14(k+5a+4) A^(5a+4).

The definitions of bmin and U imply

    rho >= max(4(n+2)(2 sum c_e+6)+8,2mu+4,16).

Thus the parent's unshifted/rotated no-carry proof is unchanged.
All support is below Emax, and T2+Emax<L, so no unshifted convolution
crosses a cell boundary.

## 4. Exact convolution roles

At T1 or T2, DC times the current native word reads sum c_e*x_e.
No other band or short-shift term reaches that position: the band
separation exceeds twice Emax and short-shift outputs are below T1-Emax.

At vertical test e(0,1,s), the short shift 3a reads the current center
copy e(1,1,s), while the temporal-neighbor identity shift reads its
prior copy e(0,1,s). At e(1,1,s), it reads the current following copy
e(2,1,s) and temporal-neighbor center copy. Thus the two vertical tests
encode exactly the two temporal overlaps.

At horizontal tests H+e(1,0,s) and H+e(1,1,s), shift H+a reads the current
center and right copies; shift H on the spatial neighbor reads its left
and center copies. Thus the two horizontal tests encode exactly the
two spatial overlaps.

At 9M and 27M, DC's shifts 8M and 24M read current anchors M and 3M,
and the temporal-neighbor identity shift reads its anchors 9M and27M.
There are no unintended contributions: the low support lies below M,
the anchors are separated by the listed powers of 3, the high bands
lie above all these tests, and H=51M+3a+1 separates horizontal tests
from the possible sum 24M+27M=51M.

The small sparse audit checks these exact linear maps on every source
basis vector at every test position, rather than testing random words.

## 5. Uncontaminated clauses and whole-cell synchronization

Modulo L, the expanded rotated support is contained in [0,Emax+1].
The distance T2-T1=4Emax+2 and its complementary cyclic distance are
both greater than Emax+1. Thus no translate of that support meets both
clause sites. One clause site is uncontaminated for every bit rotation.

Its low base-A digit permits 0 or1 selectors: the count is <=k<A-1
and AND with A-2 vanishes only for 0 and1. At each payload/anchor base-A
digit, the coefficient is a sum of two Boolean values; its masked bit
forces evenness. Therefore every occupied cell has one selector, its
five matching copy bits, and all four anchors. Every unoccupied cell
has zero payload and anchor bits. The upper dummy bit has zero clause
coefficient and causes no problem.

Write the binary rotation as b*t+epsilon, 0<=epsilon<b. At the marked
origin the two anchor tests force both rotated anchor digits to be odd.
If 1<=epsilon<=b-2, every rotated digit is even. If epsilon=b-1,
the single upper dummy bit supplies at most one odd spill position
per cell; two distinct anchor tests cannot both be odd. Hence epsilon=0.

All low native positions lie in [0,M); the remaining positions are
M,3M,9M,27M. The only pair of native positions at difference18M is
(9M,27M). Since L>54M, a modular difference cannot introduce another
such pair through wraparound. The two anchor tests therefore force
t=0 modulo L. The remaining rotation is a whole-cell rotation.

Anchors propagate occupied status through temporal neighbors. The copy
tests propagate it horizontally because every selected cross has a
one-hot center/left/right payload: if one side were empty, some tested
bit would be1 and fail. Horizontal neighbor index1 generates the entire
cyclic word, so the Start forces every cell occupied. The four decoded
overlaps now give the cross reconstruction of Section1.

## 6. Fixed modulo-five unit and completeness

Because b is a power of5, rho=2 mod5. Since T2-T1=4Emax+2=2 mod4,
the paired high-band terms of DC cancel modulo5 for every c_e.
Since a=439=3 mod4, 8M and24M are0 mod4, and

    2DC-DR
      =2*(2+3rho^H+1+1)-rho^H
      =3 mod5.

No correction monomial is needed. Package06's exact dummy derivative,
Boolean subset lemma and actual-index tuning therefore apply without
change. The one dummy's low bit has c_e=0, and none of the copy or
anchor tests reads it. All allowed Boolean dummy changes preserve
the clauses and no-carry bounds.

The canonical genuine computation supplies one Start at cyclic origin.
The unit rho-digit of the native field comes only from its temporal
neighbor's Start selector; DC and DR have positive minimum exponent.
Consequently the same shifted high-mask correction MF0+4 works, and
the canonical low-bit tests persist after dummy tuning. The parent's
strict mass bound 2C+F<q/3 and the actual-index Pell converse apply.

This proves the same blank-halting equivalence with these smaller
coefficients. The four-port bounds needed by either the old or new
arithmetic finalizers are preserved exactly.

## 7. Verification status

- Exact machine hash checked by the inherited parser.
- All 13 center classes of the cross count replayed by direct local-predicate
  enumeration over every left/right pair and all allowable prior/following
  choices: cross count 38,256,607,897.
- Sparse basis-vector collision, mask-population, carry-bound, and
  all-rotation support audits passed for three toy layouts.
- Cyclic reconstruction checked for all binary center words of length1..8
  and every stride, plus exhaustive binary cross words of length1..3.
- The proof above is parametric; finite audits do not prove its theorem
  and do not materialize the actual giant coefficients.
- No K215 halting tuple and no new Lean/Rocq derivation is claimed.

