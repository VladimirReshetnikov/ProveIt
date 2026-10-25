# Independent arithmetic review of the strict horizon merger

Reviewed against ProveIt commit
`7a8da414376a80b90ecf799f37ceb26fb9ac674e`, the incoming Factorial Free
Binomial CRT `direct/factorial_free_affine/raw_source.json`, and the
transformation now released as `code/build_strict_source.py`, 25 October 2026.

## Conclusion

The proposed strict horizon change is mathematically compatible with
the smaller growth majorant, linear CRT radius, and affine radix class.
The full existence equivalence survives, subject to the inherited
arithmetic and C222/refutation calibration cited in the retained source.
The constructive converse must choose an **even** cofinal parameter `h`
for `t=16+h^2` when the growth majorant is `F=t^t`. The odd choice in an earlier exploratory variant applied instead
to its different growth majorant `F=(t+1)^t`.

This review checks the new arithmetic and the literal location of the
source changes; it does not replace the independent complete expansion
and transformation-certificate checker.

## 1. Exact meaning of the range merger

The old source has two denominator outputs:

* coordinate 181, `pow4.output`, for `q^t`;
* coordinate 189, `pow6.output`, for `q^(t+1)`.

The first denominator already serves the row-index range. The second
serves exactly the ranges of the four schema coordinates `a,b,c,d` and
the derived polynomial label sum `J(a,b,c,d)`. Changing those five
binomial lower indices from `t+1` to `t` strengthens their decoded bounds
from `<=t` to `<t`. The existing prime-power range proof works verbatim
with this smaller lower index: the factorial valuation loss is smaller,
and the target digit is still below the chosen prime-power precision.

Rows 239 through 246 supply the private Pell addition and power-residue
certificate for the obsolete `q^(t+1)` request. Coordinates 333 through
340 occur nowhere outside these rows. The only remaining uses of the
old output are an additive semantic majorant, its square in the frame,
and its denominator-ratio row. Consequently substituting 189 by 181,
substituting ratio coordinate 539 by 538, and deleting ratio row 376
has precisely the stated arithmetic effect. It does not alter the
evaluated semantic Pell anchor `J`.

Removing `(t+1)^2` and `(q^(t+1))^2` from the square frame removes
obsolete atoms only. With first power base `d=t`, removing the duplicate
`d^2` is valid because the atom `t^2` remains in that same frame. Any
duplicate surviving occurrence in an additive majorant merely increases
that majorant and causes no logical problem.

## 2. `F=t^t` suffices for exact label multiplicities

All nonzero decoded labels now belong to `[1,t-1]`. Delete unit factors
coming from zero labels from the two flow products. If the two nonunit
factor counts differ and the smaller is `r`, then `r<=t`. The larger
product is at least `(F+1)^(r+1)`, whereas the smaller is at most

    [1+(t-1)F]^r <= (t-1)^r(F+1)^r.

The strict inequality `F+1>(t-1)^t` excludes equality. Thus both products
have the same factor count `r<=t`.

On replacing `F` by an indeterminate `Z`, each product has nonnegative
integer coefficients and coefficient sum at most `t^r<=t^t=F`.
Every individual coefficient is strictly below `F`: for `r=0` this is
immediate, and otherwise the constant coefficient one and another
positive coefficient prevent any single coefficient from attaining the
whole sum. Thus every coefficient of the difference has absolute value
strictly below `F`. A least nonzero coefficient cannot vanish modulo
`F` after dividing the value at `F` by its corresponding power of `F`.
The difference polynomial is therefore zero. Unique factorization of
the linear polynomials `1+jZ` recovers the exact label multiplicities.

This argument needs individual coefficient bounds, not a falsely strict
bound on the total coefficient sum.

## 3. The linear radius and signed radix proof remain valid

The elementary bound `lcm(1,...,t)<=4^(t-1)` gives, for `t>=16`,

    lcm(1,...,t)^2 <= 16^(t-1) < 16^t <= t^t=F.

Hence the full factorial-free prime-power selector and covering lemmas
still apply to `B=binom(F+t,t)`. Both the soundness selector and the
completeness assignment for all prime factors are retained.

The first power base is positive and at least 16. Thus `F=t^t>2^32`,
and all original coarse growth budgets remain ample. The binomial upper
index `F+t` is smaller than the former `F^2+t`. The signed-radix bootstrap
with `q=4z+1` consequently applies with the new `F`: it forces the
actual CRT representatives nonnegative, gives `|BH|>=2`, excludes
amplification index zero using the last endpoint, and obtains

    x >= (t+1)F+2,  |q| >= 2^x,  |B| < |q|/2.

Signed low-remainder recovery for the first binomial digit then gives
`B=binom(F+t,t)>0`, followed by `q=(BH)^x>0`. No sign assumption on the
new affine radix has been smuggled into this argument.

## 4. Constructive completeness and its parity correction

Start with a finite C222 derivation. The retained derived-label proof
explicitly chooses the horizon beyond the proof length, every finite
schema parameter, and every finite derived label sum before defining
the carrier. Include the fixed truth-padding row in this finite list.
An arbitrarily large **even** `h` gives `t=16+h^2` exceeding this entire
list strictly. Consequently all five stronger ranges hold after padding.
There is no dependence of these finite local constructor values on the
later carrier or on the CRT representatives.

Now `t` is even and

    v_2(F)=t v_2(t) >= t > v_2(t!).

Let `O` be the odd part of `t!`. Choosing a sufficiently large odd
multiple `w` of `O` and setting `y=Fw^2` supplies the same even multiple
of `t!`, arbitrarily large positive accumulator margin, and odd pairwise
coprime beta moduli as in the incoming construction.

Since `v_2(F)>floor(log_2 t)`, every `1<=j<=t` satisfies
`v_2(F+j)=v_2(j)`. Hence `B=binom(F+t,t)` is odd. The retained CRT choices
therefore still permit even amplification code `x`, the required nine
representative parities, odd `H`, and the designated semantic anchor
parity. The inequality `F+t<=B` remains true. It follows that the
canonical radix `(BH)^x` is an odd square and so satisfies `q=4z+1`.

The removed `t+1` request needs no replacement private Pell witnesses.
Its five consumers use the already constructed `q^t` request. Every
remaining simultaneous Pell-frame, exact-power, normalized-remainder,
and slack witness is supplied by the original construction with these
strict finite bounds and the new positive first base `d=t`.

Thus a finite refutation produces a zero of the changed source, and a
zero produces a finite refutation. Exact monic elimination and sum of
squares then transfer the existence equivalence to each emitted ordinary
quartic. The inherited syntactic calibration gives the required
ZFC-provable equivalence between its nonsolvability and `Con(ZFC)`.

## Scope

No claim of global optimality, first historical discovery, proof of
consistency, or new proof-assistant formalization is made here. All
unmodified power, CRT, C222, and ZF/ZFC calibration lemmas remain explicit
dependencies of this review.
