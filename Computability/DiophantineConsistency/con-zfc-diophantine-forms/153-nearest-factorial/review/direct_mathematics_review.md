# Independent review of the nearest-factorial source transformation

Prepared with AI assistance on 25 October 2026. This review was performed
separately from the producer of `common_nearest246`. It is an ordinary
mathematical review, not outside human refereeing or a new proof-assistant
certificate.

## Accepted scope

I checked the replacement of the three initial scalar sign guards and the
two factorial ceiling rows by an odd-square radix and one additional term
in the common normalized remainder bound. Subject to the retained signed
Pell orientation and direct C222 calibration theorems, the replacement is
sound and complete. The argument below makes explicit two power-congruence
extensions needed before any factorial sign has been recovered.

The separate JSON audit `audit_direct_source.py` reads only data and imports
no producing program. It verifies that all 381 retained raw residuals are
unchanged, exactly the two declared ceiling rows are removed, exactly the
three declared rows are added, precisely the three original scalar guards
are removed, the signed anchor cap is unchanged after renaming its private
witnesses, and the common remainder guard changes only by adding `-4 S^2`.
Three deliberate corruptions are rejected. The receipt is
`DIRECT_SOURCE_CHECK.json`. Final coordinate eliminations, row operations,
and full quartic expansion require their own separate finite audit.

## 1. Exact new hypotheses

Write `F` for the proposed factorial, `B` for the proposed binomial,
`V=(F^2+1)^t`, `M=q^x`, and `H=1+sum(a_i)` for the nine actual CRT
representatives. At the beginning these interpretations, except
`t=16+h0^2`, are conclusions still to be proved. The retained frame and
anchor give canonical signed-index Pell coordinates independently of the
removed sign guards.

The new equations are

    q=(2z+1)^2,
    B vB=M,
    vB V+S=M F,
    M^2=1+4(sum_{i=1}^{11} R_i^2+S^2)+G(a,b,c),

where `G(a,b,c)=a^2+b^2+c(c+1)`. All variables are integers. In particular
`G>=0` for every integer triple. The old three positive divisor ratios
`q^t v_t=M`, `q^(t+1) v_(t+1)=M`, and `q^(y+1) v_y=M` remain. The
displayed powers name existing ordinary-polynomial power-output wires;
they are not exponentiation primitives in the emitted equation.

## 2. Two needed power-congruence extensions

Let the retained frame give `|A|>W^W`, `W>=258`, and absolute values below
`W` for each requested base, exponent, and output. Canonical signed Pell
coordinates certify the usual congruence with modulus

    T=2An-n^2-1.

For any nonzero integer base `n` and nonnegative requested exponent `k`,
the ordinary recurrence gives the power congruence for `n^k` even when
`n<0`. Also

    |T| >= 2|A||n|-n^2-1 > W^W+W,
    |m-n^k| < W+W^(W-1) < |T|.

Thus the congruence gives exact equality `m=n^k`. This extension is used
for the possibly negative self-radix base `BH` only after `B!=0`, `H>=1`,
and `x>=0` have been proved. It must not be invoked at base zero.

At base one, the output is one for every signed exponent. To see this
without assuming the exponent's sign, put

    L_k=X_k(A)+(1-A)Y_k(A).

Then `L_0=L_1=1`, and the recurrence
`L_(k+2)=2A L_(k+1)-L_k` extends in both directions. Modulo `2(A-1)` it
gives `L_k=1` for every integer `k`. The frame's output bound and
`|2(A-1)|>W+1` give `m=1`. This is the precise base-one fact needed for
the exceptional `q=1` branch; the parent's statement for a known
nonnegative exponent alone would not suffice there.

The parent's negative-index exclusion at a positive base at least two is
unchanged. It uses the inverse-unit congruence to derive `m n^j=1` for a
negative index `-j`, which is impossible for integers `m`, `n>=2`, `j>=1`.

## 3. Exclude q=1 before claiming x is nonnegative

The odd-square equation gives `q>=1`. If `q=1`, the preceding signed
base-one result gives `M=1`, without any sign premise on `x`. The common
norm equation then forces `S=0`. The ratio `B vB=1` forces
`B=vB=1` or `B=vB=-1`. The scaled ceiling gives `F=vB V`, hence
`|F|=V`. Independently, the nonnegative horizon and the `F^2+1` power
request give `V=(F^2+1)^t>|F|`. Contradiction.

Consequently `q>=9`, since it is an odd square. The base-`q` request now
forces `x>=0` and `M=q^x>0`. The retained divisor equation
`q^(t+1) v_(t+1)=q^x` gives `x>=t+1>=17`. These facts precede every
use of the endpoint equations or of a factorial/binomial interpretation.

Every actual representative is an exponent at base `q+1>=10`, so the
parent's signed-index argument gives `a_i>=0` and hence `H>=1`.

## 4. A centered ceiling error gives the missing signs

Since `B vB=M>0`, both `B` and `vB` are nonzero. Put `b=|B|`. Subtracting
`vB V+S=M F` from `vB B F=M F` shows exactly

    S=vB(BF-V).

The norm gives `|S|<M/2`, so the integer `s=BF-V` satisfies

    |s|<b/2.                                      (1)

This deduction is valid for either sign of `B`; no rational witness is
introduced. The nonzero signed-base extension gives

    q=(BH)^x=|BH|^x>=b^x                          (2)

because `q>0`. If `BH<0`, equality itself forces `x` even.

If `F=0`, then `V=1`, so (1) gives `b>=3`. Each low coefficient of
`(q+1)^t` is at most `2^t`. For `t>=16`,

    2^t/(q-1)<=2^t/(3^(t+1)-1)<1/32.

The ordinary low remainder modulo `q^t` is therefore below `q^t/32`.
The normalized centered-remainder argument identifies it exactly, so
the factorial digit yields `B=1 mod q`. But `|B-1|<=b+1<q` by (2) and
`x>=17`, hence `B=1`, contrary to `b>=3`. Thus `F!=0`.

Now put `f=|F|>=1`. If `BF<0`, then `BF<=-b`, and (1) would give
`V=BF-s<-b/2<0`. Therefore `BF>0` and

    V<b(f+1/2).

For `f>=1`, `(f^2+1)^2>(f+1)(f+1/2)`. Since `t>=16`, this forces
`b>=f+2`, and consequently

    V<b^2-b.                                      (3)

These inequalities are available before any binomial meaning is used.

## 5. The exact factorial digit is recovered without a sign guard

For `m>=1`, `t>=1`, and `0<=j<=t`, the elementary Pascal/product bound is

    binom(m+t,j)<=(m+1)^t.

Apply it with `m=F^2`. Every low factorial coefficient is at most `V`.
Equations (2)--(3), `b>=3`, and `x>=17` give

    V/(q-1)<b^2/(b^x-1)<1/32.

Thus the ordinary low remainder modulo `q^t` is below `q^t/32`. Scaling
by the positive ratio `M/q^t`, the existing norm bound identifies the
new remainder with that ordinary remainder exactly. Dividing the digit
equation and reducing modulo `q` gives

    B=C mod q,       C=binom(F^2+t,t),       0<C<=V.

If `B=-b`, then `0<C+b<=V+b<b^2<=q`, contradicting `q|(C+b)`. Hence
`B>0`, and `BF>0` gives `F>0`. Since both `B` and `C` lie in `[0,q)`,
the congruence gives the equality `B=C`.

This sequence does not use a binomial interpretation to obtain the
coefficient estimate required to prove that interpretation.

## 6. Nearest-factorial lemma

**Lemma.** For integers `t>=16` and `F>=1`, define

    R_t(F)=(F^2+1)^t/binom(F^2+t,t).

Then `|F-R_t(F)|<1/2` implies `F=t!`.

**Proof.** Set `H0=t!`. The exact product is

    R_t(F)=H0 product_(j=1)^t (F^2+1)/(F^2+j).

All factors are at most one, so `R_t(F)<=H0`. Thus
`F<R_t(F)+1/2<=H0+1/2`, and integrality gives `F<=H0`.
Each factor is nondecreasing in `F^2`; hence

    R_t(F)>=2^t/(t+1)>t^2+1/2.

The last inequality holds at 16 and is preserved by induction; the
stronger `2^t>2t^2(t+1)` also holds at 16 and is preserved for `t>=16`.
It follows that `F>t^2`, so `F>=t^2+1`.

Put `a_j=(j-1)/(F^2+j)`. Then

    sum_j a_j<t(t-1)/(2F^2)<1/[2(F+1)],

because `F^2>t^2(F+1)>t(t-1)(F+1)`. The finite product inequality gives

    R_t(F)>H0(1-1/[2(F+1)]).

If `H0>=F+1`, the right side is at least `F+1/2`, contradicting the
nearest-integer premise. Therefore `F=H0`. This proves the lemma.

In the new source, divide (1) by the now-positive `B=C`: the premise is
exactly `|F-V/B|<1/2`. Therefore `F=t!`.

## 7. Rejoin the retained decoding only after the bootstrap

At this point all of `F=t!`, `B>F`, `q>=9`, and the ordinary factorial
digit have been recovered. The positive `F` gives
`y=V(V-1)>F+2`. The unchanged endpoint equations now imply
`x>=2+(t+1)y` in the same order as the parent. The encoded index becomes
positive by its existing congruence and `B>F^2+1`, so `H>=2`.

The parent's coefficient bounds for all ten range digits, its repaired
zero-representative estimates, the strict beta quotient ranges, the
amplification bound, and the finite Horn-flow interpretation can then be
used without any changed premise. Each low ordinary range remainder is
below its denominator divided by 32 and is recovered by the same common
centered norm. The inherited C222/refutation calibration is unchanged.

## 8. Completeness and the odd-square restriction

For `F=t!`, each `j<=t` divides `F`. Thus `F^2/j=F(F/j)` is even and
each reciprocal factor `1+F^2/j` is odd. Hence `B` is odd. The canonical
beta base `y=V(V-1)` is even, so all beta moduli `1+(j+1)y` are odd.
The beta CRT progression can consequently be chosen with an even and
arbitrarily large `x`.

After this choice, the CRT precision modulus `N^2=B^(2x)` is odd.
Representatives can be chosen in their required residue classes with
either parity by adding this modulus. Keep the parent's parity condition
on its dominant `a` and `b`, which makes the semantic anchor even. Choose
the independent `d` representative's parity so that
`H=1+sum(a_i)` is odd. The documented identity for anchor parity depends
only on `a,b`, so this does not disturb that condition. Its representative
size bounds remain available using the two consecutive positive lifts.
Then `q=(BH)^x` is an odd square, represented by
`z=((BH)^(x/2)-1)/2`.

For the nearest factorial remainder,

    0<=F-R_t(F)<t(t-1)/(2t!)<1/32.

The bound is immediate at `t=16` and decreases thereafter. Since `B|M`,
choose `vB=M/B` and `S=vB(BF-V)`. Thus `|S|/M<1/32`.
The eleven old normalized remainders are also below `M/32`. Therefore

    4(sum R_i^2+S^2)<48 M^2/1024<M^2.

The integer `M^2-1-4(sum R_i^2+S^2)` is nonnegative and has a ternary
`G` representation. The new norm is therefore compatible with every
canonical witness after the stated cofinal and parity choices. The
remaining parent witnesses are constructed in the same dependency order.

## 9. Conclusion and limits

No circular sign premise was found after the base-one and signed-base
extensions were stated explicitly. The nearest-factorial lemma gives
exactly the stronger tolerance required by the centered ceiling error.
The literal source/guard audit agrees with the declared mathematics.

This accepts the new ordinary semantic reduction, relative to its
identified inherited Pell and logical calibration. It does not by itself
authenticate a final claimed variable count, prove all coefficient
collection steps, supply an object-language ZFC proof, establish
Con(ZFC), or certify a global simplicity optimum.
