## Final evaluator update

The delivered evaluators use 93 gates for P13, 104 for the P12 product,
and 103 for the P12 sum of squares. The following review also discusses
the preceding 95/105/104-gate evaluators. Exact symbolic checks prove
equality of their polynomials; the original packets are retained in
reference/. See CIRCUIT_OPTIMIZATION.md for the three local identities.

# Independent mathematical review of the thirteen-positive construction

Review target: `short_opt/PROOF13.md` and the precise source interface in
`short_opt/PROOF14.md`, against ProveIt commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

**Outcome:** the newly proposed local reduction is mathematically valid on
the stated strictly positive domain, conditional on the explicitly inherited
native compiler/canonical-witness and signed Pell-index theorems. I found no
additional semantic gap in the new carrier, recovery order, or completeness
arguments. This is a separately conducted AI-assisted mathematical review,
not external peer review, a kernel build, or an object-language ZFC proof.

## 1. First carrier and the logical order

From `A0=0`, the rational number `Z/M` has integer square, hence is an
integer `tau` even when `Z` is negative. The separate reductions modulo
`q^3` and `q-1` are legitimate because these factors are coprime. They give
`q^3|Y` and `(q-1)|Bt`, using `W=1 mod(q-1)`. Thus

```
s=Y/q^3>0, t=Bt/(q-1), tau=ell+k+r+s-Wt.
```

The first norm has `|tau|<ell+k`, since
`(ell+k)^2-[ell(ell+k)+1]=ell*k+k^2-1>0`. Therefore
`Wt>r+s>0`, and `t>0`. Positivity of `Bt` proves `C>0`, since the alternative
`C<=0` makes `(qK0+X)C-qF` strictly negative. This derivation uses neither
`q|X` nor any conclusion from the auxiliary-index theorem. It removes the
main circularity risk in a quotient-absorption argument.

## 2. Second carrier and the preliminary index bounds

Since `Y` is a positive multiple of `q^3`, the congruence restriction
`q=2 mod3` makes `gcd(q,H)=1`. The prescribed compact tuple has
`beta=1 mod3`; `J=3j+1` therefore supplies this restriction on every input.

The displayed positivity estimate for `Dstar` is valid before `q|X`:
`r0<k`, `c>kY`, and `UaY>H` give
`Dstar>Uac-Hk>0`. The last inequality follows already from `q>=16`,
`Y>=q^3`, `a>=2Y`, and `H=4a+3<6a`. Rational-root integrality in `A1`
then gives the integer positive main root and
`q^5|(q^4X-r0)`.

The first Pell equation has discriminant `v(v+1)` with `v=XY^2` and
fundamental unit `(2v+1,2)`. Coefficient 1 cannot occur because
`v^2+v+1` lies strictly between `v^2` and `(v+1)^2`; coefficient 2 occurs.
Thus the classification with `k=2 psi_(2XY^2+1)(n)` is correct.

The case `n=1` forces `eta=zeta=1` and `c=2Y+1`, contradicting the main
Pell inequality `c>=2(a+2)>=4Y+4`. Hence `n>=2`. Consequently
`c>kY>8XY^3>=8q^9>2R`, with the last inequality using only the already
established outer bound `R<q^4`. Parameter monotonicity and `c>k` give
`n<p`; standard Pell growth gives `c>2p`.

## 3. Normalized strong equation avoids a hidden hypothesis

The normalized equation `f^2-Delta(ic^2)^2=1` gives
`f=chi_A(m)` and `I=psi_A(m)` directly. Strong divisibility gives `p|m`
from `c^2|I`. If `m=pv`, composition gives `I=c psi_D(v)` and
`psi_D(v)=vD^(v-1) modc`. Since `D` is invertible modulo `c`, this gives
`c|v`, and hence `c|m` and `m>=pc>2p`.

This is stronger than merely appealing to the earlier ordinary-strong
rank lemma: that lemma needs a large-`c` hypothesis which would not yet be
available in the new recovery order. The new proof correctly avoids it.

With `Maux=Delta I`, `Kaux=Maux^2`. The auxiliary residual is exactly
`Maux^2 V^2-(Maux^2-1)(V+u)^2-1`. Neither `y=|V+u|` nor `V` can vanish;
the `V=+/-1` possibilities are excluded by `V=-c modf` and `f>2c>4`.
The congruences `V=-c modf` and `V=-R modc` are valid. All hypotheses of
the signed auxiliary-index interface quoted in package57's Section5 are
therefore present before it is used to conclude `p=R`.

## 4. Modulus recovery and transport

The main congruence first gives `q^4|r0`. The first Pell congruence gives
`k=2n mod(4XY^2)`, whose modulus is a multiple of `q^4`. Thus
`q^4|(2n-R-1)`. The strict interval `1<=n<R<q^4` forces equality, not merely
a congruence: `2n=R+1`. Now `r0=k-2n` is divisible by `4XY^2`, which is a
multiple of `q^5` because `Y^2` contains `q^6`. The stronger main
congruence then yields `q|X`. No earlier step assumed this divisibility.

Both `h=r0/(XY)` and `gamma_old=gamma+X/q-r0/q^5` are integers. The first
is positive by strict Pell growth. For the second,
`D>(a+1)c` and `c>X` imply `D-ac-X>0`.

Finally `Bt=q[(K0+w)C-F]>0` and `(q-1)|Bt` give the strictly positive
integer `z_new=((K0+w)C-F)/(q-1)`. Setting `z_old=z_new+1` restores the
old transport equation with right side exactly 1. This explicit shift is
necessary and has the correct sign.

## 5. Completeness and positivity of every new coordinate

The canonical compact tuples have odd tableau area and `B=2^590069=2 mod3`,
so `J=1 mod3` and `J>1`; the new `j` is positive. Their `R=3 mod4` supports
the squared-modulus Chebyshev quotient construction. These are properties
of the complete coherent tuple, not arbitrary independent port values.

Canonical `X=2^R`, `R>3q`, imply `w=X/q>q`. The old transport equality
then gives `z_old>=2`, so `t=q(z_old-1)>=q`. With `tau>ell` and `k>s`,

```
r=Wt+tau-ell-k-s > qW-k-s > qW-2k >0.
```

This verifies the nontrivial positivity of the new carrier gap. The main
gap is positive because the inherited canonical bound `gamma_old>w`
holds and `r0/q^5>0`. The quoted package58 proof proves this margin by
explicit Pell growth; positivity of `gamma_old` alone would not suffice.

The fresh auxiliary values `V*=chi_(Delta I)(R)/(Delta I)` and
`y*=psi_(Delta I)(R)` satisfy the squared-modulus congruences. Coprimality
`gcd(c,f^2)=1` makes the constructed `T` an integer; its numerator is
positive. Since `R>=3` and `Delta I>1`, one has `y*>V*>1`, so `u=y*-V*>0`.
Changing these two auxiliary coordinates does not alter either carrier.

## Scope of this review

The new algebraic and existential argument passes at ordinary proof level.
The inherited native decoder, canonical completeness, K215-to-refutation
calibration, and signed abscissa step-down theorem remain named dependencies.
The complete object-language consistency iff and the new thirteen-variable
polynomial were not checked by a proof-assistant kernel in this review.
The separate exact degree/gate checker is implementation evidence, not a
replacement for these unbounded mathematical arguments.
