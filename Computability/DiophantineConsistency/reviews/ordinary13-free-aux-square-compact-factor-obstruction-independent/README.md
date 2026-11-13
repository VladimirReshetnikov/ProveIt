# Independent review: compact free auxiliary-square partial construction

Reviewed the pinned [candidate packet](../../research/ordinary13-free-aux-square-compact-factor-obstruction/README.md).
The structural map and the displayed standard-integer partial construction
check out. No full compact-port zero, zero-existence separation, model result,
or Lean proof follows from this construction.

The independent checker compares all 84 retained rows with the 85-row parent:
it removes exactly `y2=n_y*n_y`, replaces its consumers with the new natural
input `n_y2`, and preserves all other rows, outputs, ports and input order.
Consequently the graph values agree under the explicit forward substitution
`n_y2=n_y²`, for arbitrary integer ports and valuations. The reverse is open.

For the compact partial assignment, write \(Y=q^3\),
\(a=Y(q+1)\), \(c=(a+2)^2+1\), and \(C=q^2-1\). With q even,
\(q-1,q+1\) are coprime, \(c\equiv17\pmod{q-1}\), and
\(c\equiv5\pmod{q+1}\). The pinned fixed exponent gives
\(q\equiv15\pmod{17}\), \(q\equiv2\pmod5\), whence
\(\gcd(C,c)=1\). Therefore the literal rank
\((\alpha+\beta^2)C+MC+qMF\) can be made 2 modulo c by a positive
natural alpha. Its value is positive and \(T=(R+\Delta)/c\ge1\), since
\(\Delta=c-2\).

The graph coordinates for c are also natural: \(c\equiv5\pmod Y\),
\(Y>5\), so \(\eta=5\), \(k=(c-5)/Y=Y(q+1)^2+4(q+1)>5\),
and \(\zeta=k-5>0\). The modular Pell matrix has determinant 1, so it is
a permutation of the finite ring module modulo \(c^2\); an identity power
exists, with order at most \((c^2)^4=c^8\). Its positive iterate has v>0
and \(c^2\mid v\), making \(i=\Delta v/c^2>0\) a valid shifted input.
The actual strong equation then holds:
\(I^2=\Delta(f^2-1)\), where \(I=c^2i=\Delta v\).

With the selected T, the literal graph has
\(V=f^2\Delta-c=I^2-2\). The free input
\(y_2=I^4-3I^2+1\) satisfies
\(y_2-I^2(y_2-V^2)=1\). It lies strictly between
\((I^2-2)^2\) and \((I^2-1)^2\), because the two gaps are
\(I^2-3\) and \(I^2\); these are positive for I≥2. Thus it is a natural
nonsquare and the strong and auxiliary factors have the claimed values.

The checker additionally reconstructs a complete finite noncompact q=2 toy
using an independently computed modular Pell period and evaluates every child
row. Its first and main residuals are both nonzero, confirming the critical
scope boundary. This finite toy and residue controls are not a proof that the
actual compact partial assignment satisfies the first or main norms; the
symbolic arithmetic above supports only the stated partial assignment.
The author receipt also reproduces. No Lean, build, staging, or model-provider
validation was performed.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-free-aux-square-compact-factor-obstruction-independent/check.py | cmp - reviews/ordinary13-free-aux-square-compact-factor-obstruction-independent/receipt.json
```
