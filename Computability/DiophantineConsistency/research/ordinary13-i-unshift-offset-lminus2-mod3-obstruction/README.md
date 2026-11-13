# Fixed-port obstruction for the d = L − 2 power match

At the actual compact ports, suppose \(J\) is a natural graph coordinate and
\(q=1+\beta J\) is a power of 2. Then the matching construction with
\(m=n+d\), \(d=L-2\), and \(R=2n-1\) is impossible. This rules out only
that exact index and rank matching, not the existence of graph zeros or other
ways to arrange witnesses.

The [pinned preceding certificate](../ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/README.md)
checks the actual rank row and compact digit recipes. It proves
\(R\equiv0\pmod3\) whenever q is a power of 2: namely,
\(\beta\equiv MC\equiv MF\equiv1\pmod3\), \(J\equiv q-1\), and
\(R=G(q^2-1)+J(MC+qMF)\equiv q^2-1\equiv0\).

The exact leading-power identity for this offset requires

\[
n=\frac{(L-2)(2L-1)}3.
\]
Since n is an integer, the numerator must be 0 modulo 3. Both factors have
the same unique root 2 modulo 3, so \(L=3t+2\) for an integer t. Then
\(n=3t(2t+1)\), and the proposed rank \(2n-1\equiv2\pmod3\), a
contradiction. Equivalently its numerator after multiplying by 3 has residues
\(4L^2-10L+1\equiv1,4,6,7,7,6,4,1,6\pmod9\), none 0.

From `Computability/DiophantineConsistency`, reproduce the finite checks and
the pinned source-level predecessor with:

```sh
python3 -I -S -B research/ordinary13-i-unshift-offset-lminus2-mod3-obstruction/check.py | cmp - research/ordinary13-i-unshift-offset-lminus2-mod3-obstruction/receipt.json
```

The proof applies in standard integers. The checker does not run Lean, expand
the large fixed ports, or prove an iPRA/all-model theorem.
