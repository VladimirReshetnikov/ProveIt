# The smallest kernel-gcd complement is still auxiliary-obstructed

Order fact-level pairs lexicographically by integer \(A\ge2\), then by
positive even main index m. The smallest pair outside the
[kernel-gcd criterion](../ordinary13-parent-even-index-kernel-gcd-obstruction/README.md)
is

\[
A=3,\quad m=2,\quad \Delta=A^2-1=8=2\cdot2^2,\quad c=y_2(A)=6.
\]

Indeed A=2 has squarefree \(\Delta=3\), so the criterion holds for
every c; at A=3, m=2 already gives
\(\gcd(c^2,dt)=\gcd(36,4)=4\nmid6\). The natural main Pell root
exists: \(17^2-8\cdot6^2=1\). There are natural strong witnesses, the
smallest positive one being

\[
f=19601,\quad I=55440,\quad i=1540,
\qquad I=c^2i,\quad I^2=8(f^2-1).
\]

Nevertheless **no** natural strong witness at these fact-level A,c can
satisfy the parent's auxiliary factor-one equation, for either signed
auxiliary root and any integer R,T. This example is not a full two-norm graph
zero, does not show that the kernel criterion can be removed generally, and
does not prove parent/child existential inequivalence or an iPRA theorem.

## All strong witnesses reduce to the same Pell subgroup

Let \(I=c^2i>0\) and \(I^2=8(f^2-1)\). The divisibility of squares
forces \(4\mid I\). With \(u=I/4>0\),

\[
f^2-2u^2=1.
\]

The least positive integer-coordinate norm-one Pell unit is
\(3+2\sqrt2\), so every such positive solution has
\(f=x_h(3)\), \(u=2y_h(3)\) for some h>0. Thus
\(I=8y_h(3)\), and \(36\mid I\) is equivalent to
\(9\mid y_h(3)\). The first six ordinates modulo 9 are
\(1,6,8,6,1,0\); since the positive Pell x-coordinates increase, h=6
produces the smallest f above. The checker also independently scans smaller
f as a bounded control.

All \(x_h(3)\) are odd. Choose an odd prime p dividing f. Its Pell
transition \(Q^h\) modulo p is invertible and anti-diagonal. If any odd
ordinate index j had \(y_j(3)\equiv0\pmod p\), then
\(Q^j=\pm\mathrm{Id}\); raising that scalar matrix to h would be
diagonal, whereas the odd power \((Q^h)^j\) is anti-diagonal. This is
impossible. The Pell addition identity then gives, for every odd \(\ell\),

\[
y_\ell(3)^2-y_2(3)^2=y_{\ell-2}(3)y_{\ell+2}(3)\not\equiv0\pmod p.
\]

If the actual auxiliary factor were 1, standard Pell classification would
produce an odd auxiliary index \(\ell=2j+1\) and a sign \(\epsilon\)
with \(V=\epsilon x_\ell(I)/I\). Its graph formula requires
\(V\equiv-c\pmod{f^2}\), while
\(I^2\equiv1-A^2\pmod{f^2}\) and the earlier odd-quotient identity
would force \(y_\ell(3)\equiv\pm c\pmod p\), a contradiction.
The argument covers every h, not just the displayed strong witness.

For the displayed f one can also see a four-step finite obstruction: 17
is a prime divisor of 19601, and all odd auxiliary quotients modulo 17 lie in
\(\{1,-1\}\), whereas \(\pm c=\pm6\) are neither value. This
finite control does not replace the universal subgroup proof.

## Why this is only a Pell-level example

The actual shifted two-norm graph has \(A=Y(X+1)+2\), with q≥1,
\(Y=q^3s\), and shifted \(s\ge1\). A=3 would force
\(Y=1,X=0,q=s=1\); then its actual scaled main root and norm are
incompatible (the norm makes \(d-c\) a unit modulo H=7, while the root
formula forces 7 to divide it). Thus the displayed main Pell ordinate is
not itself a solution of that graph's signed main equation. Changing
first/main witnesses or leaving the strong subgroup in other discriminants
remains open.

The checker pins and reproduces the general kernel and anti-diagonal packets,
checks the exact Pell and strong values, the mod-9 minimality, a bounded
small-f control, and the four-step mod-17 quotient cycle. No Lean, build,
staging, model provider, or large coordinate expansion is used.

```sh
python3 -I -S -B research/ordinary13-even-index-kernel-complement-minimal-pell/check.py | cmp - research/ordinary13-even-index-kernel-complement-minimal-pell/receipt.json
```
