# Necessary strong subgroup and correlated auxiliary congruences

Suppose standard natural first/main data satisfy the actual two norms of the
shifted two-norm graph, with main multiplier \(A\ge2\) and positive main
ordinate \(c=y_m(A)\) at **any index \(m\ge2\)**. In any same-data
parent completion, its actual strong witness must have

\[
f=x_{mz}(A)\quad\text{for some }z\ge1,\qquad
c\mid y_{mz}(A),\qquad f^2\equiv1\pmod c. \tag{1}
\]

Moreover, its actual auxiliary witness must have an odd Pell index
\(\ell=2j+1\) and a **single correlated sign** \(\sigma\in\{-1,1\}\)
satisfying

\[
y_\ell(A)\equiv-\sigma c\pmod{f^2},\qquad
\ell\equiv-\sigma R\pmod c. \tag{2}
\]

Here R is the literal graph rank, not an independent variable and not
assumed equal to m. These are necessary restrictions, not a proof that
\(c\mid R\pm m\) or that every two-norm zero lifts. They apply to
ordinary integers; no Lean/model, iPRA or existential-equivalence result is
claimed. In the shifted compact two-norm setting, beta>0 and the first norm
exclude J=0, so q≥2, shifted k≥1 and \(c\ge Y\ge8\); its main Pell
index is consequently at least 2.

## Strong witness lies in the m-subgroup

The [reviewed even-index theorem](../ordinary13-parent-even-index-unconditional-same-data-obstruction/README.md)
starts from the parent factor-one equation
\(I^2=\Delta(f^2-1)\), with \(I=c^2i>0\),
\(\Delta=A^2-1\), and uses only \(c\mid I\). Write
\(\Delta=d t^2\) with d>1 squarefree. Valuations give \(I=dt\,u\)
and \(f^2-du^2=1\). For the least positive **integer-coordinate norm-one**
Pell unit \(\varepsilon=a+b\sqrt d\), with coordinates \((X_j,U_j)\),
ordinary Pell classification gives positive r,h such that

\[
A+t\sqrt d=\varepsilon^r,\qquad
f+u\sqrt d=\varepsilon^h.
\]

Put \(D_0=\gcd(c,dt)=\gcd(m,dt)\le m\); the equality follows from
\(y_m(A)\equiv mA^{m-1}\pmod\Delta\) and \(dt\mid\Delta\).
Because \(c\mid dtU_h\), the integer \(c/D_0\) divides \(U_h\).
It also divides \(U_{rm}=tc\). Pell strong divisibility gives
\(c/D_0\mid U_g\), where \(g=\gcd(h,rm)\). If g were proper,
\(g\le\lfloor rm/2\rfloor\).

The required strict growth holds for **all** m≥2:

\[
U_{rm}>m t\,U_{\lfloor rm/2\rfloor}. \tag{3}
\]

For even m this is the doubling proof in the predecessor. For odd
\(m=2v+1\ge3\), set \(k=\lfloor rm/2\rfloor\). If rm is even,
r is even and \(k\ge rv+1\), so
\(2X_k\ge4X_{rv}=4x_v(A)\ge4vA>mt\). If rm is odd,
\(U_{2k+1}>aU_{2k}=2aX_kU_k\), while \(a\ge2\) and
\(X_k\ge X_{rv}=x_v(A)\ge vA\); this again exceeds \(mtU_k\).
Here \(4v\ge2v+1=m\) and A>t. Thus (3) holds in both cases.

Since \(U_{rm}=tc\) and \(D_0\le m\), (3) makes
\(c/D_0>U_{\lfloor rm/2\rfloor}\), contradicting the alleged proper
g. Hence \(rm\mid h\). Writing \(z=h/(rm)\) gives
\(f=x_{mz}(A)\), and Pell strong divisibility gives
\(c=y_m(A)\mid y_{mz}(A)\). The norm
\(f^2-1=\Delta y_{mz}(A)^2\) then proves \(f^2\equiv1\pmod c\).
This uses no squarefreeness or gcd hypothesis on the original \(\Delta\)
and requires only \(c\mid I\), although the parent supplies \(c^2\mid I\).

## Exact auxiliary condition for a fixed strong witness

At a parent completion, the strong and auxiliary factors must both be 1.
Let \((x_j(I),y_j(I))\) be the Pell sequence with multiplier I. Standard
integer classification of
\((IV)^2-(I^2-1)y^2=1\) gives an odd \(\ell=2j+1\) and
\(\epsilon\in\{-1,1\}\) with
\(V=\epsilon x_\ell(I)/I\). Put \(\sigma=\epsilon(-1)^j\).
The actual graph formula \(V=f^2(Tc-R)-c\) implies
\(V\equiv-c\pmod{f^2}\) and, using (1), \(V\equiv-R\pmod c\).

The exact odd-quotient identities used in the [general CRT lift](../ordinary13-shifted-two-norm-parent-crt-sufficient-condition/README.md),
together with \(I^2\equiv1-A^2\pmod{f^2}\) and
\(I\equiv0\pmod c\), give

\[
V\equiv\sigma y_\ell(A)\pmod{f^2},\qquad
V\equiv\sigma\ell\pmod c.
\]

This proves the correlated congruences (2). Their same sign is essential.
They alone do not force \(\ell\equiv\pm m\pmod c\), nor do they
prove or refute the earlier scalar sufficient conditions.

Conversely, for a **fixed valid strong witness** f,I, the congruences (2)
plus the explicit positivity inequality

\[
\sigma(-1)^j\frac{x_\ell(I)}I+c+f^2R>0 \tag{4}
\]

are sufficient for an auxiliary completion: the two coprime moduli f² and c
divide the numerator, so its quotient by \(f^2c\) is a natural T≥1;
choose \(y=y_\ell(I)\) and the corresponding signed V. Equation (4) is
a real additional requirement when that sign is negative. This exact
fixed-strong criterion does not establish that any such \(\ell,\sigma\)
exist.

## Reproduction and limits

The checker pins the exact graph and reviewed even-index and odd-lift source
packets, reproduces the former, checks bounded Pell-growth and subgroup
controls, and gives a fact-level odd-index example with h odd and R≠m.
That toy is not a graph zero. The ordinary Pell classification, strong
divisibility and symbolic growth argument above establish the uniform claim;
finite controls do not. No Lean, build, staging, provider validation or
giant Pell expansion is used.

```sh
python3 -I -S -B research/ordinary13-parent-strong-subgroup-rank-congruence/check.py | cmp - research/ordinary13-parent-strong-subgroup-rank-congruence/receipt.json
```
