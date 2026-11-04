# Independent review: symbolic-beta scalar obstruction

The reviewed note and checker have SHA-256 values
`ec1a6a401ca62eb9930ec252ad14f3ecb54f6b5c12c98a4d1180267c4e01a631`
and `496e1871d4614ed57ef07fc8accbeaa941a30d08327095931c84a602ac221393`,
respectively. The primary modular-gcd program has SHA-256
`7afbe833e37be4702dc71761abf8e128ca328b0ccfc3463a702fd0587a211cc4`.
The ordinary-integer argument is correct under its explicit definitions,
subject to the stated external finite gcd computation. In particular, the
two Pell ordinates fit the **full** interval `kY<c<k(Y+1)`.

Independent derivation: `s=1770208`, `d=1768160`, `r=3056651345`, and
`n=3054883185` satisfy `rd=s(2n−r)`, `r≥590069`, odd `r`, and
`n<r<2n`. With `t=2^s` and `X=2^r`, this proves
`(tX)^(r−1)=t(Xt²)^(n−1)`. The recurrence bounds
`(z−2)^(j−1)≤y_j(z)≤z^(j−1)` for `z≥3` and positive `j` suffice.
Since `t²>2` and `r−1>n−1`, the lower main-ordinate estimate exceeds
`t(Xt²+2)^(n−1)`, which is at least `kY`. For the upper estimate,
`4(r−1)Y<X` gives `(1+2/X)^(r−1)≤1+4(r−1)/X<1+1/Y`;
the common leading term is at most `kY`, yielding `c<k(Y+1)`.
Consequently `eta=c−kY` and `zeta=k−eta` are both positive.

The recurrence modulo `q⁴` gives `k≡2n` because `q⁴ | Xt²`. The gcd
`gcd(c,q²−1)=1` was independently recomputed by the distinct
[companion-matrix implementation](../trace74-symbolic-pell-gcd-matrix/README.md);
both algorithms are external computations using GMP on the same host. The
main recurrence has even coefficient and odd index, so `c` is odd and
coprime to `q⁴`; moreover `q⁴` and `q²−1` are coprime. The three stated
rank congruences therefore have a simultaneous CRT solution. Subtracting
whole multiples of the product makes `R<0` and gives `G<0`; then
`F=1`, `C=q(q−1)−G` make `F,C>0`, `F+C≥q`, and the graph's displayed
signed-rank formula equals `R`. The carrier input is consistently
`w=X/q≥1`. Because `R≡r (mod c)` and `R<0`,
`(|R|+r)%c=0`, the negative `SignMod` alternative. The projection is zero
because `X=2^r`; this is not a full graph evaluation.

The checker was rerun independently with `python3 -I -S -B` and exited 0.
It verifies the huge symbolic case's finite exponent arithmetic without
evaluating its Pell numbers, and exactly evaluates the analogous
`B=7,n=63,r=77` case, including the positive split and simultaneous rank
congruences. It does not prove the universal recurrence estimates or
check the huge tuple by evaluation. The note makes no claim that the
tuple is a full graph zero or binds all external fixed ports. It is not a
Lean model proof or iPRA endpoint.
