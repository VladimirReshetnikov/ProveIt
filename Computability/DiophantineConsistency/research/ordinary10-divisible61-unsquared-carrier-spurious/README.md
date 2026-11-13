# A signed carrier cannot replace its square directly

A tempting local way to shorten the final three-residual expression is to
replace the literal sum of squares

\[
B_{res}^2+F_{res}^2+A_1^2
\]

by \(B_{res}+F_{res}^2+A_1^2\). The latter is an **invalid probe**,
not a proved reduction: it has an exact natural zero at a point where the
original 61-operation graph is strictly positive. This remains true even if
one assumes several inequalities already known at legitimate positive-port
zeros. It does not establish that the original and probe have different
existential zero status or rule out other residual encodings.

At the natural ports

\[
(\beta,K_0,MC,MF)=(2,1,1,0),
\]

take the ten graph inputs

\[
(1,0,0,1,0,20295322575756392005638,8750,0,3,0).
\]

The actual literal fields are

\[
\begin{gathered}
q=3,\ C=1,\ X=3,\ Y=27,\ k=4,\ R=41,\\
\ell=8748,\quad \tau=8750,\quad B=3,\quad
F_{res}=3,\quad A_1=-201471201792.
\end{gathered}
\]

In particular beta>0, K0>0, MC<beta, MF<2beta, C>0, X>0,
\(k>q\), and the earlier necessary root interval
\(2\le\tau-\ell\le k-2\) all hold. Since \(\beta J=2\), the
chosen natural h equals

\[
h=\frac{B+F_{res}^2+A_1^2}{2}.
\]

Consequently \(B_{res}=B-2h=-(F_{res}^2+A_1^2)\): the probe output
is exactly zero, while the original sum of squares is positive. The point
is not claimed to satisfy either actual norm equation or to use the fixed
compact ports.

`probe.json` is a literal 60-row counterexample probe: it removes only
`Bsq=Bres*Bres` and redirects the existing `sum1` to `Bres`. Its name and
metadata mark it invalid; the row count is **not** a saved gate in a valid
zero-preserving equation. The checker pins the 61 graph, verifies the exact
edit and all 60 live rows, computes the point from the original graph, and
evaluates both outputs exactly. The cancellation is specific to this proposed
encoding and is not a lower bound on other circuits. No Lean, build, staging,
model/provider or iPRA result is involved.

```sh
python3 -I -S -B research/ordinary10-divisible61-unsquared-carrier-spurious/check.py | cmp - research/ordinary10-divisible61-unsquared-carrier-spurious/receipt.json
```
