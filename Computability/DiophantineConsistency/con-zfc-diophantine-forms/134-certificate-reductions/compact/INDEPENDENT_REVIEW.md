# Independent review of the staged Pell-index construction

## Conclusion and scope

I reviewed `PROOF.md` against the retained ordinary proofs
`proof_sources/product_square.md`, `uniform_ratio.md`, `scaled_native.md`,
`saturation.md`, `uncentered.md`, and the specialization statement in
`indexed_native.md`. I found no mathematical defect in the new staged
index argument or in its composition with the stated inherited interfaces.
In particular, removing the artificial scale does not introduce a circular
use of the first-index congruence, a false coprimality assertion involving
`Y`, or a parity restriction on the doubled strong Pell pair.

This is an independent review of the ordinary unbounded arithmetic proof.
It is not a new formal derivation of the transitive native/calibration
theorems, a proof of consistency, or an independent recount of every circuit
operation. The exact finite polynomial and coefficient-byte checks are
separate, documented in `verify.py` and `CHECK.json`. I did not modify any
producer or equation file during this review.

## 1. The replacement ratio bound includes lambda = 1

Write `a0=Y(X+1)`, to distinguish this quantity from the proof's combined
radicand register `a`. The retained lemma takes

    A=lambda*a0+1, P0=2X*lambda^2*Y^2+1,
    xi=(X+1)^(2r)/X^r,

and proves

    xi < psi_A(2r+1)/psi_P0(r+1)
       < xi*(1+1/a0)^(2r)

for every `lambda>=1`. Its proof establishes the lower bound by the exact
identity

    (2A-1)^2 X-(X+1)^2(2P0)
      =4 lambda a0 X+X-2(X+1)^2
      >=2X^2+X-2>0.

The upper bound uses `A<=lambda(a0+1)` and
`2P0-1>4X lambda^2 Y^2`. Both inequalities apply directly at `lambda=1`.
There is no limiting argument, and no old lemma requiring `lambda>1` is
being silently reused. The ordinary Pell growth estimates used to prove
this statement hold for the integral bases that occur here.

The later claims `H>3a0`, `A>q`, and `P0>A` also survive directly:

    H=4a0-1>3a0,
    A=Y(X+1)+1>q,
    P0-A=Y(2XY-X-1)>0.

These use `X>=q>=32` and `Y>=q^3`, already true from the positive inputs.

## 2. Root extraction is independent of all index divisibility

The identities

    Fsq=(1+2a)^2,
    Q=4 Delta^2 U^2 G,
    gcd(E,1+Delta U^2 E)=1

are literal polynomial identities. Therefore, at any zero,
`gcd(G,Q-1)=gcd(G,QV^2-1)=1`. Applying valuations to the rational equality

    (Q-1) z^2=G(QV^2-1)

forces every prime valuation in `G` to be even. No coprimality of the
carrier denominator `M` is needed. The positive coprime factors of `G`
then give `E=tau^2`, `F0=f0^2`, and `g=tau*f0`.

The adjacent-coefficient descent correctly proves integrality of the
rational `y=|z|/g`. If `y=u/m` is in lowest terms, `m^2|Q-1`; the stated
linear transformation has an integral first coordinate, strictly lowers
its nonzero absolute value when that value exceeds one, and preserves the
reduced denominator `m` of the second coordinate. At first coordinate
one, the norm gives `y=1`. Thus `z` is an integer before any use of the
mask rank, `B>=0`, or the rational number `rho=e/Y^2`.

The doubled pair satisfies

    f=1+2a, I=2Ug,
    f^2-Delta I^2=1, Q=(Delta I)^2, c^2|I.

These are precisely the strong-pair hypotheses used later. They do not
require the strong index to be odd.

## 3. Transport and the rank are recovered before rho is integral

The inherited all-index folding interface is uniform in the actual base
`A>=3`; the present pair and auxiliary norm supply its hypotheses. It
gives `c=psi_A(p)` with positive odd `p`. The first norm independently
gives `k=2psi_P0(n0)`. Excluding `n0=1` proves

    k>=8XY^2+4, c>kY>k>8XY^2>=8q^7.

This bound and the unconditional mask inequality
`R<q^4+(alpha+2)q^2` prove `b>c` without knowing the sign of `B`.
The one-sided estimate `rho<b/Y^2` is valid even when `e` is negative;
it follows from `b-e=c(T+alpha)-k+1>0`.

For `L=V^2`, the proof's exact identity gives `g<a`, then `V>3g` and
`gy<L/2`. For `L=bV`, the odd auxiliary index is at least five, because
`V>4Q` excludes its first and third values. Its fifth value gives
`b>4g`, and again `gy<L/2`. These arguments only use positive integral
roots already recovered in Section 2.

If `B<=-1`, the exact rational carrier implies

    n < L/2-L+b/Y^2 < 0,

contradicting the positive input `n`. The last inequality holds for both
weights since `V>b>1` and `Y^2>2`. Thus `B>=0`, so `C>0` and the mask
gives `3q<R<q^4-2`.

At this point `c>8q^7>2R` and the positive Pell growth gives `c>2p`.
The rank/divisor lemma supplies the strong index `m` with `pc|m` and
`m>2p`. The signed auxiliary-index lemma then uses

    S=Delta I, S^2=Delta(f^2-1), c|S,
    V=-c modulo f, V=-R modulo c,
    0<p,R<c/2

to conclude `p=R`. The second residue follows from `c^2|I`, hence
`f^2=1 modulo c`. None of these premises involves `rho` or the
first-index congruence. This is the essential chronology check.

## 4. A known divisor suffices to recover the whole denominator

With `z` integral, clearing only `hH` in the carrier shows

    Y^2 | hH e.

Because `Y=q^3s`, one has `q^6|Y^2`. Also `h=q-1` and
`H=4Y(X+1)-1=-1 modulo q`, so `gcd(q^6,hH)=1`. Consequently `q^6|e`.
There is no need for `gcd(Y,h)=1`, which in general is false.

The base-one recurrence gives

    k=2n0 modulo 4XY^2.

Therefore `q^6|(2n0-R-1)`. To bound this small index error, suppose
`n0>=R`. Since `P0>A` and `p=R` is already proved, monotonicity would give

    k/2=psi_P0(n0)>=psi_A(R)=c>k,

an impossibility. Thus `1<=n0<R`, and

    |2n0-R-1|<R<q^4<q^6.

The divisible error is zero. Only after obtaining `2n0=R+1` does the
proof return to the full base-one congruence to deduce `4XY^2|e`, hence
`Y^2|e`. This establishes `rho` integral in the required order.

## 5. Projection needs no cancellation modulo a composite number

The ratio bound gives `Y>X^r/3`, where `R=2r+1` and `r>=48`, so
`H>X^(r+1)`. Since `rho` and `z` are now integral, the carrier gives
`H|h*Kpos`. The identity

    Kpos=H*X*c-2Kquad

only cancels the unit two modulo the odd number `H`. Universal Pell
projection then gives divisibility of the entire product

    h(X-2^R)(2^R X+1).

For an explicit independent height check, put `T0=2^R`. Since
`X,T0>=2` and `h<X`,

    |h(X-T0)(T0 X+1)| < 4 T0^2 X^3.

Also `X^(r-2)>=32^(r-2)>2^(4r+4)=4T0^2` for `r>=48`. Thus the product's
absolute value is less than `X^(r+1)<H`. The product must vanish, and
its second and first prefactors are positive, giving `X=2^R`.

The projection then gives `H|Kpos`, so `kappa` is an integer. The carrier
and `W=1 modulo h` give `h|B`. The prescribed `q^3|Y` was present from
the outset. The fixed-minus parity and half-binomial rounding interfaces
therefore have all their original hypotheses. The proof correctly
constructs a fresh native source at `Y(X+1)+2`, without identifying that
base with the new base `Y(X+1)+1`.

## 6. Positive completeness after doubling the seed pair

The calibrated source supplies the canonical outer data with `X=2^R`,
`R=3 modulo 4`, `q^3|Y`, and `Y` equal to the prescribed half-binomial.
At `lambda=1`, the uniform ratio lemma supplies the fresh values

    c=psi_A(R), k=2psi_P0((R+1)/2),
    eta=c-kY, zeta=k-eta.

Both are positive. One may check the margin directly: the half-binomial
identity gives `xi=2Y+theta`, `0<theta<1/4`; the ratio's upper error is
bounded by the retained weaker `3/a0` estimate, whose total error is
less than `1/4` in the canonical range. Thus the ratio `c/k` lies strictly
between `Y` and `Y+1`. Furthermore `e` is a strictly positive multiple
of `4XY^2`, so `rho>=1`.

The finite-order matrix construction is valid over every modulus, not
only prime moduli: the Pell matrix has determinant one and belongs to
the finite group `SL_2(Z/(c^2 tau))`. A positive multiple of its order
gives a positive seed ordinate `I0` divisible by `c^2 tau`. Consequently
`i=I0/(c^2 tau)>0`, and doubling gives exactly the strong pair in the
polynomial definitions.

The retained auxiliary-completeness theorem requires the strong norm
and `c|I`; it has no odd-index hypothesis for this strong pair. Its
explicit witness is

    S=Delta I, V=chi_S(R)/S,
    T'=(V+c+R f^2)/(c f^2).

Its integrality is the retained odd-index polynomial identity at the
already canonical `R=3 modulo 4`. The positivity of the actual input
`T=T'-alpha` does not need the removed scale. Indeed, with `r>=48`,

    V=Q_r(S^2)>=(4S^2-3)^r>9S^4,
    c<I<S, f^2<=S^2, alpha<q<S.

Hence `T'>V/(c f^2)>9S>alpha`. The quantity `f0` also satisfies

    f0>(A-1)I0>Xc>kappa.

Thus `g=tau*f0>kappa`. The chosen final positive coordinate

    n=gy+Wt+rho-kappa

is integral and strictly positive because `y>=1`, `Wt>=0`, and
`rho>=1`. Its exact carrier is `z=gy`, so the released polynomial
vanishes. No positive inverse shear is presumed.

## Review boundary

The new local theorem and its positive witness construction pass this
review relative to the explicitly retained universal Pell and calibrated
native-source theorems. The coherent fixed tuple and the distinction
between the new and reconstructed native bases are preserved. Historical
priority, global minimality, and the truth of `Con(ZFC)` are not conclusions
of this review.
