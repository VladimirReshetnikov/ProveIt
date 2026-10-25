# Independent mathematical review: second-order Lucas correction

Verdict: PASS for the ordinary mathematical reduction in
`pell_compression/lucas_q1/PROOF.md`, inspected on 25 October 2026.
The reviewed principal is the ten-positive-variable, 87-operation,
degree-304 construction. This verdict concerns the unbounded proof and
dependency order. Circuit identity, exact degree/operation counts, fixed
coefficient bytes and final packaging require their separate finite audit.
The inherited native/refutation calibration is identified but not re-proved.

The review read the new proof, its complete parent proof, the retained
uniform-ratio lemma, and the normalized-rank, signed auxiliary-index and
positive auxiliary-reconstruction lemmas in `universal_pell.tex`.

## 1. Early root and index arguments

The rational root extraction still applies at Y=qs. In particular Q>1,
G>0, M>0 and |V|>1 follow at every positive input. The identities

    Fs=(1+2a)^2, Q=4 Delta^2 U^2 G

justify the coprimality/valuation argument giving G=g^2. The adjacent-Pell
rational-integrality descent is valid: the transformed first coordinate is
a nonzero integer of smaller absolute value, and m^2|(Q-1) ensures that
the second coordinate keeps its reduced denominator m. Thus the argument
does not silently assume integrality of the rational carrier.

The all-index folding hypotheses use A>=3, c<=I, c^2|I and the two
Pell/congruence relations, not q^3|Y. The first norm gives the same
k=2 psi_(2v+1)(n0). After excluding n0=1, the weakened scale still gives

    c>8XY^3>=8q^4,

which is strong enough for the later rank bound c>2R.

The p=3 exclusion remains valid with Y>=q>=32. The exact formula for eta
in terms of u=X+2-2Y has the asserted signs for u<=-1 and u>=2. The two
remaining u values would make q divide 1 or 2. This correctly supports
the large-|b| estimate needed by the bV transport weight.

## 2. Transport for negative ranks

The old inequality `k-R-1<b` does not by itself bound the corrected error
when `(R+1)(R-1)(R+3)<0`. The new proof correctly treats all such integer
ranks: exactly R<=-4 and R=0.

For R=-r<=-4, the exact outer relation forces C<0 and |C|>r/q^3.
The stronger bound

    B<=-1-w|C|,   Wt<-(1+w|C|)L

provides a genuinely cubic negative term in r. The adverse correction is

    delta0 < w s^2 r^3/(6q^3).

Since b>r, b>c, V>(Fs-1)b and Fs-1>s^2, either weight satisfies
`L>(Fs-1)r^2`. Hence `w|C|L>delta0`. This is the necessary extra estimate;
the proof is not relying on a false global inequality ebar<b.

For R=0 the adverse correction is only w s^2/(2q^3), whereas |C|>=1
and L>Fs-1>s^2. The same contradiction follows. For all other ranks the
cubic correction has the favorable sign. Positive kappa and positive
sigma may safely be discarded in an upper bound for n.

Thus B>=0 and C>0 are proved before invoking `3q<R<q^4-2` or any
positive-rank interpretation. The transport order is sound.

## 3. The sixfold Taylor identity and all prime factors of q

The expansion

    2 psi_(1+2v)(m)=2m+8v binom(m+1,3)+32v^2 Z_m

has integral nonnegative Z_m, by the stated finite Lucas polynomial
expansion. After p=R is known, put r0=(R+1)/2 and d=2(n0-r0).
Since

    (R+1)(R-1)(R+3)=48 binom(r0+1,3),

ebar=e6/6 is an integer. The carrier gives the integer divisibility

    6q^6 | 6 hH (ebar-q^4s),

so cancellation of the common integer factor 6 is legitimate. It is not
cancellation of a possibly nonunit residue class modulo q. Coprimality of
q with hH then gives q^6|(ebar-q^4s), and in particular q^4|ebar.

The exact identity was re-derived by factoring the difference of the two
cubic binomial polynomials:

    6(ebar-d)
      =v d[(2n0)^2+(2n0)(R+1)+(R+1)^2-4]+192v^2 Z_(n0).

The first-order reduction gives q^3|d because q^3|v. Therefore the right
side of this identity is divisible by q^6. For a prime ell dividing q,
with a=v_ell(q)>=1, it follows that

    v_ell(ebar-d)>=6a-v_ell(6)>=6a-1>=4a.

This explicitly covers both ell=2 and ell=3, with arbitrary powers of
either in q. Indeed the estimate even gives q^5|(ebar-d), although the
proof needs only q^4. No assumption that q is prime or coprime to six is
being used.

The monotonicity argument gives 1<=n0<R. Hence |d|<R<q^4 and q^4|d
force d=0. Returning to the full Taylor identity only after d=0 gives
ebar=32v^2 Z_(r0), so q^6|ebar and rho is a nonnegative integer. The
full denominator is recovered at the correct stage.

## 4. Delayed scale recovery

The uniform ratio estimate is explicitly valid for X>=32, Y>=1 and
lambda>=1; its lambda=1 specialization does not presuppose q^3|Y.
It supplies the required whole-product height bound after the indices
have been recovered.

The final proof uses a shorter direct recovery: the already established
divisibilities q^6|(ebar-q^4s) and q^6|ebar give q^6|q^4s, hence q^2|s.
Thus sigma is integral and q^3|Y is recovered before projection.
Once z and rho are integral, the carrier therefore gives

    kappa-WB/h in Z,

and clearing h gives H|hK. The retained projection uses the whole product
bound and cancels no arbitrary nonunit factor. After X=2^R, its universal
identity gives kappa integral. The remaining carrier gives h|WB. As W=1
modulo h, h|B, recovering integral nonnegative t before the original native
reconstruction.
The fractional sigma term is doing real work; simply replacing q^3s by
qs while dropping it would not be justified by this proof.

## 5. Positive completeness

The unchanged native source supplies q^3|Y and the required half-binomial
value of Y. Choosing the new independent input s=Y/q makes sigma=Y/q^3
a positive integer. All semantic values A,c,k and their ratio interval
are unchanged, so eta and zeta are positive.

The stronger seed estimate is valid:

    f0>(A-1)I0>2Xc,

because I0 is a positive multiple of c^2 tau and Y,c,tau are positive
with the large bounds already established. Together with kappa<Xc and
sigma<=Y<Xc, this gives g>kappa+sigma. Consequently

    n=gy+(1+hL)t+rho-kappa-sigma

is a positive integer. The retained auxiliary reconstruction applies to
the doubled strong pair and gives positive integral unshifted T. No
inverse positivity of a removed T shift is assumed.

## 6. Review conclusion

No mathematical gap was found in the new unbounded argument. The
second-order correction repairs the particular q-linear-scale obstruction
described in the earlier incoming work, with a complete treatment of
negative transport ranks and the primes dividing six. The result is a
new explicit tradeoff candidate; this review does not assert global
minimality or historical priority.

The final deliverable should retain the inspected proof, actual ten-input
circuits, complete coherent coefficient tuple and fixed-source proof
closure, and the separate exact circuit audit. The degree-410 V^2 control
should remain labeled a dominated comparison, as it is in the proof.
