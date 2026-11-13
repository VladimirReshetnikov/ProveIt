# A limitation of the Pell-gap and projection constraints

There are infinitely many ordinary-integer scalar assignments satisfying
the strict Pell gap, the index window, the `q` divisibilities, and the
weighted projection, even at the symbolic first beta. They can additionally
satisfy the signed-rank and first-index congruences and violate the reverse
guard. **They are not positive 74-graph tuples.** In fact, the family
necessarily violates the required positive split of the first ordinate;
this failure is proved below. The example therefore does not refute the
reverse guard at the fixed ports or the desired equation equivalence.

For any integers `B≥1` and `n≥5` with `2n−1≥B`, let

```text
q=2^B, beta=q−1, J=1, h=q−1,
Y=q³, t=2Y, r=2n−1, X=2^r, K=2^r,
k=2*y_n(X*t²+2),  c=y_r(t*(X+1)+2),
```

where `y_0(z)=0`, `y_1(z)=1`, and
`y_(j+1)(z)=z*y_j(z)−y_(j−1)(z)`. Then `q=beta*J+1`,
`q | X`, `q³ | Y`, `n<r<2n`, and `r` is odd. The weighted projection

```text
4Y(X+1)−1 | h X (X−K) (KX+1)
```

holds because `X−K=0`. The first and main ordinate *numbers* above are
positive, but `c` has not yet been represented by positive graph
coordinates.

For positive indices, elementary induction gives
`y_j(z)≤z^(j−1)` for `z≥2` and `y_j(u+2)≥u^(j−1)` for `u≥1`. Hence

```text
t*y_n(X*t²+2) ≤ t(2Xt²)^(n−1),
y_r(t(X+1)+2) ≥ (tX)^(2n−2).
```

The ratio of the lower bound in the second line to the upper bound in the
first is `(X/2)^(n−1)/t`. The exponent inequality

```text
2(n−1)² > 3B+2
```

holds because `B≤2n−1` and `n≥5`: the difference from `6n−1` is
`2n²−10n+3>0`. Thus the main ordinate exceeds *twice* the left side of
the strict Pell gap. The gap and projection constraints therefore hold.

For the retained symbolic first beta, take `B=67*8807=590069` and any
`n≥295035`. Then `q=beta+1` and all the preceding scalar claims apply.
This observation uses the symbolic parameter, not an identification with
an external coefficient payload.

## Rank and residue can be imposed independently

Let `MC,MF,K0` be any natural numbers, put `RJ=MC+q*MF`, `a=2n−1`,
and define the least nonnegative residue and an integer shift by

```text
G0 = [−(1+q²)(a−RJ)] mod q⁴,    G=G0−q⁴,
F=1,    C=q(q−1)−G,
R=(q²−1)G+RJ.
```

Here `G<0`, `C>0`, `F+C≥q`, and `q(q−F)−C=G`, so `R` is exactly the
guard-free signed rank expression for `J=1`. Since
`(q²−1)(−1−q²)=1−q⁴`, `R≡2n−1 (mod q⁴)`. The first recurrence
parameter satisfies `X*t²+2≡2 (mod q⁴)`, so induction on `n` gives
`y_n(X*t²+2)≡n (mod q⁴)` and hence `k≡2n (mod q⁴)`. Consequently

```text
q⁴ | R+1−2n,   q⁴ | k−R−1,
q² | C+MC+q(F+MF)+1−2n.
```

The last congruence is a direct reduction of the displayed rank formula.
Also `(K0+1)C−F≥0`. These are simultaneous *scalar* constraints; no full
graph equation or signed-rank/main-index congruence is asserted.

## Why the positive-ordinate split fails

The actual graph coordinates require positive `eta,zeta` with

```text
k=eta+zeta,    c=kY+eta.
```

Those equations imply `c<k(Y+1)`. The scalar family violates this:
the strengthened growth bound above gives `c>2t*y_n`, while
`k(Y+1)=2*y_n(Y+1)≤2t*y_n` because `Y≥1`. Thus the only possible
`eta=c−kY` is **greater than `k`**, forcing `zeta=k−eta<0`.

Accordingly, this family demonstrates that the *strict gap*, projection,
rank residue, size, and index-window constraints listed above cannot alone
force the guard. It does **not** satisfy both ordinate equations as a
positive graph tuple; the upper bound `c<k(Y+1)` and the other actual graph
factors remain available to rule it out. No Lean model theorem or iPRA
endpoint follows from this ordinary-integer construction.

The companion checker evaluates one small exact instance (`B=30,n=16`)
and separately checks the symbolic-exponent inequalities without evaluating
its enormous Pell ordinates. It is a finite diagnostic, not a proof of the
universal recurrence estimates or of any full graph claim. Run from the
repository root:

```text
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-gap-projection-scalar-obstacle/check.py
```
