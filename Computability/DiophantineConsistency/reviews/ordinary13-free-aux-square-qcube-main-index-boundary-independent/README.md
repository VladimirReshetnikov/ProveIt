# Independent review: q³ main-index boundary

The [reviewed packet](../../research/ordinary13-free-aux-square-qcube-main-index-boundary/README.md)
correctly strengthens the compact free-square graph's main-index restriction
to \(m>q^3\) for ordinary natural full zeros in its exact
\(J=1,w=s=1\) slice. It neither excludes other slices and larger indices
nor establishes a Lean/model theorem or zero map.

The [independently reviewed two-norm transfer](../ordinary13-free-aux-square-two-norm-positive-k-transfer-independent/README.md)
uses the literal natural graph's \(k=\eta+\zeta\) and proves
\(k>0\) at an ordinary compact-port full zero. Thus \(c=\eta+q^3k>0\).
The actual main norm and standard Pell classification supply an index m for
this c; as its zero index has ordinate 0, m>0. This explicitly handles the
m=0 case left outside the earlier positive-index result.

The [independently reviewed first/main boundary](../ordinary13-free-aux-square-first-main-index-boundary-independent/README.md)
supplies a first index n≥1, the exact actual-rank congruence and growth bounds

\[
2n\equiv R+1\pmod{q^5},\quad
2q^{7(n-1)+3}\le c\le q^{5(m-1)},\quad
(2q-1)(q^2-1)+1\le R+1<q^5.
\]

Since q>1, the two growth bounds require
\(7(n-1)+3<5(m-1)\), exactly \(7n+1<5m\). In particular,
\(14n<10m\). If \(m\le q^3\), then \(14n<10q^3\). The
explicit lower rank bound gives

\[
7(R+1)-10q^3\ge4q^3-7q^2-14q+14>0\quad(q\ge8).
\]

For example the final polynomial is \(1502+642t+89t^2+4t^3\) at
\(q=8+t\), so it is strictly positive for t≥0. Thus
\(14n<7(R+1)\), or \(2n<R+1<q^5\). Two distinct nonnegative
integers in this interval cannot satisfy their required congruence modulo
\(q^5\), a contradiction.

The independent checker pins the reviewed predecessors and exact graph,
checks the no-extra-one k/c wiring and both Pell classification source
signatures, independently expands the shifted rank polynomial, and verifies
bounded exponent and rank controls. Those finite controls do not prove the
uniform result; the argument above does. The author receipt reproduces. No
Lean, build, staging, provider validation, or internal arithmetic proof was
performed.

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-qcube-main-index-boundary-independent/check.py | cmp - reviews/ordinary13-free-aux-square-qcube-main-index-boundary-independent/receipt.json
```
