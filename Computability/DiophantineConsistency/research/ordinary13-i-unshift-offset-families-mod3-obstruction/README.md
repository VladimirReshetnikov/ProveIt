# Infinite families of excluded power-match offsets

At the exact compact ports, if \(q=1+\beta J\) is a power of 2, the actual
rank \(R\) is 0 modulo 3; the [pinned source-level certificate](../ordinary13-i-unshift-offset-lminus2-mod3-obstruction/README.md)
replays the compact digit and graph evidence. Consider only exact power matches
with \(m=n+d\), \(d=L-h\), and \(R=2n-1\). The equality of the leading
powers requires

\[
n=\frac{(L-h)(2L-h+1)}{h+1}.
\]
For every nonnegative integer \(h\equiv0,2,3,5,6\pmod9\), this is
incompatible with the actual rank. Here \(L\) and n must be integers and the
usual construction also requires suitable nonnegative indices and offset.

If \(h\equiv0\pmod3\), the denominator is 1 modulo 3, giving
\(n\equiv L(2L+1)\). Thus \(2n-1\) is 2, 2, or 1 modulo 3 as
\(L\equiv0,1,2\); it is never 0.

If \(h\equiv2\) or 5 modulo 9, write \(h=3k+2\) with \(3\nmid k+1\).
Integrality of n implies the numerator is divisible by 3, forcing
\(L=3t+2\) because both numerator factors then vanish simultaneously.
Substitution yields

\[
n=\frac{3(t-k)(2t-k+1)}{k+1}.
\]
As \(3\nmid k+1\), the integer n is divisible by 3, and \(2n-1\equiv2\).
This contradicts \(R\equiv0\).

This excludes these **particular matched-index formulas**, not other values of
h, shifted rank formulas, different witness maps, or graph zeros. No Lean,
iPRA, or all-model conclusion follows. The bounded control below checks
examples, while the displayed symbolic argument proves the infinite claims:

```sh
python3 -I -S -B research/ordinary13-i-unshift-offset-families-mod3-obstruction/check.py | cmp - research/ordinary13-i-unshift-offset-families-mod3-obstruction/receipt.json
```
