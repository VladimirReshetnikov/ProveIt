# Independent review: low-Y positive compact charts (round 19)

## Verdict and scope

**PASS at the explicitly inherited ordinary-mathematics calibration boundary.**
No unresolved mathematical defect was found in `positive/PROOF.md` or the four
literal polynomial DAGs. The low-Y product-weight point is **80 operations /
exact degree 338**. The composed q²-Y point is **79 / 382**; the square-weight
controls are 79 / 456 and 78 / 516. These are ten-strictly-positive-input
polynomials with the *whole* indexed BFS943 coefficient tuple, not a theorem
about arbitrary ports in a numerical box.

This review verifies the new arithmetic implications and the exact compatibility
of the cited ordinary Pell/native interfaces. It does not freshly formalize the
entire machine/refutation calibration, emit a proof-assistant certificate, prove
Con(ZFC), or use finite witness tests to infer an unbounded theorem. The finite
receipt described below has a separate, strictly algebraic purpose.

The author was notified promptly of the independent positive result, the
important low-Y leading-degree tie, the need for an explicit entire-product
bound, and the attribution requirement. No incorrect witness, modulus
cancellation, or blocked action remains to report.

Reviewed proof SHA256: `d1886f6c274a9643429cf4e511563dbf4b6c86c7aad1eabbde7554ae0c0f906c`.
The exact equation hashes are recorded in the independent receipt.

## 1. Literal carrier and native transport

For the new q1 chart, the correct definitions are

    Wbase=qw, X=q Wbase=q²w, Y=qs, D=q⁶,
    B=(K0+Wbase)C-F, sigma=s/q²=Y/q³.

The numerator is

    Z=hD[H(n-LB)+K]-H[DB+h(e-sq⁴)], M=hDH.

Thus, without any divisibility assumptions,

    Z/M=n+K/H+sigma-(1+hL)B/h-e/D.

The shift is exactly `sq⁴`, since `D sigma=sq⁴`. Replacing `Wbase` by the new
input `w` in B would change the calibrated transport relation and is not
permissible. The supplied graph uses Wbase correctly. Its other chart has
`Wbase=w`, `X=qw`, `Y=q²s`, `D=q⁵`, `sigma=s/q`, and the same cleared shift.

## 2. Root extraction and all pre-C sign estimates

The product-square extraction does not need gcd(M,G)=1. Since G divides Q,
each prime dividing G has valuation zero in both Q−1 and QV²−1. The rational
square equation therefore makes G a square. The exact gcd(E,1+a)=1 follows
from a being a multiple of E, so E and 1+a are separate positive squares.

The adjacent-Pell rational descent is valid: writing y=r/m reduced gives
m²|(Q−1); its new first coordinate is integral, nonzero, and strictly smaller
in absolute value when |V|>1. Because 2Q−1 is 1 modulo m, the reduced
second-coordinate denominator is preserved. Descent reaches |V|=y=1.
Thus z and y really are integral before transport or mask decoding.

The all-index folding proof in `provenance/centered/PROOF.md` uses only the
strong/adjacent norms, c²|I, c≤I and V=−c modulo f. It permits either sign of
V and an even strong index. Its reduced main index p is positive and odd.
The first norm gives k=2ψ_(2XY²+1)(n0). Index n0=1 forces c=2Y+1 strictly
between ψ_A(1) and ψ_A(2), so n0≥2 and k≥8XY²+4. In q1, XY³≥q⁵; in q2 it
is at least q⁷. Therefore c>8q⁵, c>X and K>0, all before C>0.

The zero-b exclusion, `a>g`, `Fsq−c>3a`, and y<(3/2)|V| are licensed by
positive inputs alone. In particular gy<V²/2. For the bV weight the extra
small-index exclusion is essential and valid:

* If p=3 and n0≥3, then kY>32X²Y⁵ whereas c=4A²−1<16X²Y², impossible.
* Hence n0=2. Setting u=X+2−2Y gives the exact displayed remainder for eta.
  Its sign forces u∈{0,1}; therefore 2Y−X∈{1,2}, contradicting q|X,Y and
  q≥32. No rank, parity, source premise or C bound enters this argument.
* For auxiliary index j=3, both signs produce multiples of Fsq equal to
  c−c3 or c+c3. The strict interval 0<c−c3<c+c3<2c<Fsq excludes both.
  Thus |V|>8Q² and |b|>4g; hence bV>0 and gy<3bV/8.

For both weights e<b, hence rho<|b|/D, without assuming rho≥0. A negative
integer B would give Wt<−L and then

    n < L/2−L+|b|/D < 0.

The positive sigma and kappa only strengthen this contradiction. Hence B≥0,
then C>0. This is not the invalid arbitrary inverse shear T_old=T−alpha.
Only now are the mask bounds 3q<R<q⁴−2 used. They give c>2R, positive b,V,
and, with c>2p and the unchanged fixed-minus residues, all hypotheses of
the normalized rank and signed auxiliary-index lemmas. Thus p=R.

## 3. Exact first index, with no premature full denominator

Integral z yields D|hH(e−sq⁴). As H=−1 modulo q and h=q−1, D is coprime
to hH, so D|(e−sq⁴), and in particular q⁴|e. The first recurrence is

    k≡2n0 (mod 4XY²).

In q1, XY²=q⁴ws², repairing the old q³-modulus defect. In q2 it is q⁵ws².
The common q⁴ divisor therefore divides 2n0−R−1. The strict inequality
2XY²+1>A and monotonicity show n0<R: otherwise k/2≥ψ_A(R)=c, contradicting
c>k. Consequently

    |2n0−R−1|<R<q⁴,

so 2n0=R+1 and only then 4XY²|e. This last statement alone does **not** yet
prove q⁶|e in q1. The proposal correctly does not make that false inference.

## 4. Early projection and the entire product

Reducing the literal numerator modulo H gives Z≡hDK. Integral z and H|M
imply H|hDK. Since gcd(H,D)=1, **H|hK before rho is integral**. This is the
crucial non-circular reordering.

The authenticated ratio estimate at scale one gives, for R=2r+1 and r≥48,
Y>X^r/3, hence X^(r+1)<3Y(X+1)<H. For clarity, projection can be verified
without cancelling any nonunit. Put t=2^R. The Pell recurrence modulo H,
where 4A=5, gives

    3·2^(R−1)c ≡ t²−1 (mod H),
    2^(R−1)K ≡ −(X−t)(tX+1) (mod H).

Since H is odd, H divides h(X−t)(tX+1), hence also the larger product with
q³h. The complete product, not either factor separately, is small. Indeed,
using q³h<X⁴ and t=2·4^r,

    |q³h(X−t)(tX+1)|
      < 2tX⁶+2t²X⁵
      = 4·4^r X⁶+8·16^r X⁵
      ≤ X^(r+1)[2^(27−3r)+2^(23−r)]
      < X^(r+1) < H.

The penultimate bound uses X≥32 and r≥48; its bracket is at most
2^(−117)+2^(−25)<1. Divisibility and strict height force this whole product
to vanish. Its factors other than X−t are positive, so X=2^R. The same
projection identity now gives H|K, thus integral positive kappa.

Now q|2^R gives q=2^m with m≥5. Induction gives 2^m≥2m, so R>3q≥6m.
Thus q⁶|X, and the *already authenticated* recurrence gives q⁶|e. This
completes rho recovery. It is a property of zeros, not a claim that q⁶
always divides the recurrence modulus.

With z,kappa,rho integral, sigma−WB/h is integral. The coprimality of q and
h gives q²|s for q1, or q|s for q2, and separately h|B because W=1 modulo h.
Thus q³|Y and the nonnegative integral transport quotient are restored.

## 5. Exact native endpoint and positive completeness

The decoded old width coordinate is Wbase, not new w. All necessary source
outer data have now been recovered: X=qWbase=2^R, q³|Y, C>0 and
B=t h with t≥0 integral. Fixed-minus parity uses positive V,y, f>2c,
c|m and m>2R, which are already available; it gives R=3 modulo 4. The
scale-one ratio and half-binomial rounding therefore have their exact
hypotheses. Source reconstruction is fresh at Y(X+1)+2, not at the
auxiliary base Y(X+1)+1.

Conversely the calibrated canonical native family supplies q=2^m,
X=2^R and R>3q. Hence q⁶|X and in particular **q|W_native=X/q**. Therefore
w=X/q² is a positive integer for q1, Wbase=qw=W_native exactly, and
s=Y/q is positive. This is the required additional completeness condition;
it is not true merely because a generic old width is positive. Chart q2
uses w=X/q and s=Y/q².

The canonical ratio theorem gives eta,zeta>0 at the new auxiliary base.
A Pell matrix period modulo c²tau exists because the matrix has determinant
one over a finite ring; a positive period supplies I0 divisible by c²tau.
Thus i=I0/(c²tau) is positive and the stated doubled pair is exact. The
auxiliary reconstruction supplies positive *unshifted* T directly. Finally
sigma=Y/q³ is integral, rho≥0, t≥0, and

    kappa<Xc, sigma<Y<Xc, g≥f0>(A−1)I0>2Xc.

So n=gy+Wt+rho−kappa−sigma is a strictly positive integer. This constructs
all ten independent inputs together and preserves the coherent outer tuple.

## 6. Independent literal count, degree and payload audit

`check_compact_independent.py` imports neither the producer nor its verifier.
It independently checks topology, all-gate/input/port liveness, operation
census, 25 exact polynomial cuts (covering every literal row, including all changed
chart/carrier interfaces), and complete leading homogeneous forms by propagating through
the entire actual DAG. It verifies every raw payload hash and bit length,
and rejects eight deliberate q1 artifact corruptions, including the wrong
native B coefficient. Normal and optimized execution are required to agree.
This is finite algebra, not a proof by testing alleged zeros.

| Chart / weight | Multiplications | Additions | Subtractions | Total | Exact degree |
|---|---:|---:|---:|---:|---:|
| q1 / bV | 48 | 17 | 15 | 80 | 338 |
| q1 / V² | 47 | 17 | 15 | 79 | 456 |
| q2 / bV | 47 | 17 | 15 | 79 | 382 |
| q2 / V² | 46 | 17 | 15 | 78 | 516 |

The q1 degree tie deg(cT)=deg(R)=4 must be retained. Writing q0=beta J,
k0=eta+zeta, C0=q0−F−alpha and B0=k0 sT−q0²(q0−F), its whole top forms are

    [P_bV]_338 = −2^10 q0^162 w^34 s^78 i^14 k0^44 B0²,
    [P_V²]_456 = 2^14 q0^212 w^46 s^104 i^20 k0^60 B0⁴ C0².

The q2 forms are

    [P_bV]_382 = −2^10 q0^206 w^34 s^80 i^14 k0^46 T²,
    [P_V²]_516 = 2^14 q0^272 w^46 s^108 i^20 k0^64 T⁴ C0².

The entire forms have respectively 274,3750,47,390 monomials. The maximal-T
coefficients show nonvanishing for the actual beta>0. No sampled ray was
used to certify exact degree. The raw tuple matches all four graph bindings,
including the indexed K hash beginning `0a86821a70429419` and once-shifted
MF_source; its full hashes are in `compact_independent_receipt.json`.

## 7. Priority and release boundary

The 79/382 point composes an incoming denominator theorem with incoming
Centered arithmetic sharing. It is not a newly discovered denominator.
The genuinely new part reviewed here is the X=q²w repair together with
projection before full q⁶-denominator recovery. The sign-free unshifted-T
argument, both signed third-index exclusions, product-square extraction,
and fresh canonical auxiliary reconstruction remain inherited. The named
`provenance/unshift.md`, `unshift_general.md`, Centered proof, universal Pell
lemmas, ratio proof and indexed-native proof retain their attribution.

Only the review files were written by this reviewer. No publication, source
repository mutation, coefficient substitution, or external release was made.
