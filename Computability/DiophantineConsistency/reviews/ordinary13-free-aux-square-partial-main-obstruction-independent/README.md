# Independent review: main-norm obstruction for the chosen free-square family

The [reviewed packet](../../research/ordinary13-free-aux-square-partial-main-obstruction/README.md)
correctly rules out a complete output zero for the **chosen family
\(c=\Delta+2\)** with positive U. It does not exclude other choices of c,
other zeros of the free auxiliary-square graph, or an existential zero map.

For the literal graph \(\Delta=a^2+4a+3=(a+2)^2-1\). Set \(A=a+2\).
When \(A\ge2\) and \(c=\Delta+2=A^2+1\), direct expansion gives

\[
1+\Delta c^2=A^2(A^4+A^2-1).
\]
If the left side were an integer square, divisibility by \(A^2\) would
make \(A^4+A^2-1\) a square. But it lies strictly between the squares
\(A^4\) and \((A^2+1)^2\). The graph main residual
\(D_*^2-U^2(1+\Delta c^2)\) therefore cannot vanish when U>0: a zero
would first force \(U\mid D_*\), making the radicand a square.

The full-output extraction also checks. At output zero the four integer
factors multiply to 1, hence each is ±1. Since
\(\Delta\equiv0\) or 3 modulo 4, the value
\(1+\Delta c^2\) is 0 or 1 modulo 4. Consequently the actual main factor
\(1+D_*^2-U^2(1+\Delta c^2)\) is never 3 modulo 4, so it cannot be
−1. It must be +1 and its residual must vanish, which contradicts the
nonsquare argument. This extraction does not assume a positive sign or a
prior divisibility for the signed root.

The independent checker pins the relevant graph and author packet, verifies
the main and product rows, checks the polynomial identity by coefficient
arithmetic, exhausts the 256 mod-4 combinations, and runs bounded nonsquare
controls. The author's receipt also reproduces. The general argument above,
not the bounded tests, justifies the conclusion. No Lean, build, staging, or
model-provider validation was performed.

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-partial-main-obstruction-independent/check.py | cmp - reviews/ordinary13-free-aux-square-partial-main-obstruction-independent/receipt.json
```
