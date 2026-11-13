# Conditional odd-index parent lift for either multiplier parity

The [previous \(m\equiv1\pmod4\) construction](../ordinary13-shifted-two-norm-parent-odd-index-lift/README.md)
assumed its main Pell multiplier A was even. That assumption is unnecessary.
For any integer \(A\ge2\), the same construction works because its
chosen strong index h is even and the doubled Pell x-coordinate is odd.
The earlier packet is preserved unchanged.

Consequently, for a standard natural zero of the shifted nine-variable
two-norm graph with nonnegative ports and beta>0, let R be the actual rank,
\(A=a+2\), and \(c=y_m(A)>0\) its main Pell ordinate. If m is odd and

\[
c\mid R+(-1)^{(m-1)/2}m, \tag{†}
\]

then the original shifted 85-row parent has a natural zero preserving the
first/main coordinates. The construction supplies actual strong and square
auxiliary witnesses. It does **not** assume \(m=R\). This is a conditional
standard-integer statement: (†) and oddness of m have not been proved for
arbitrary two-norm zeros, and neither a full graph zero, an unconditional
reverse bridge, model/Lean theorem, nor an iPRA/Con(ZFC) equivalence follows.

## Parity-free strong witness

Use \(\Delta=A^2-1\), let \((x_j,v_j)\) be the main Pell sequence,
and set \(h=2mc\). As in the [explicit-index lift](../ordinary13-shifted-two-norm-parent-explicit-index-lift/README.md),
\(c^2\mid v_h\). Set

\[
f=x_h,\quad i=\Delta v_h/c^2,\quad I=c^2i=\Delta v_h.
\]

The witnesses are positive natural integers,
\(I^2=\Delta(f^2-1)\), and \(f^2\equiv1\pmod c\).
Since h is even, the Pell norm and doubling formula give

\[
f=x_{2mc}=x_{mc}^2+\Delta v_{mc}^2=2x_{mc}^2-1,
\]

which is odd for **either** parity of A. The matrix identity of the general
lift therefore yields \(Q^{2hf}\equiv-\mathrm{Id}\pmod{f^2}\):
\(Q^{2h}\equiv-\mathrm{Id}+2fB\), and raising to odd f makes the
linear binomial term divisible by \(f^2\).

## Uniform odd-index auxiliary choice

Set \(\delta=(-1)^{(m-1)/2}\) and choose

\[
L=\begin{cases}
m,&m\equiv3\pmod4,\\
2hf-m,&m\equiv1\pmod4.
\end{cases}
\]

In both cases L≥m, \(L\equiv3\pmod4\), and
\(L\equiv-\delta m\pmod c\), because h is a multiple of c. Also
\(y_L(A)\equiv y_m(A)=c\pmod{f^2}\): this is immediate in the first
case; in the second it follows from
\(Q^L\equiv-Q^{-m}\pmod{f^2}\), whose lower-left entry is c.

Let \((z_j,y_j)\) be the Pell sequence of multiplier I and put
\(V=z_L/I>0\). The quotient is an integer since L is odd. The exact
odd-quotient identities from the general CRT lift give

\[
V\equiv-y_L(A)\equiv-c\pmod{f^2},\qquad
V\equiv-L\equiv\delta m\pmod c.
\]

As f² is a unit modulo c, (†) gives
\(f^2c\mid V+c+f^2R\). The actual graph rank R is positive under the
two-norm, nonnegative-port and beta-positive hypotheses, as proved in the
general lift. Thus

\[
T=(V+c+f^2R)/(f^2c)\ge1.
\]

With parent auxiliary input \(y=y_L(I)\), the literal graph ordinate is
\(V=f^2(Tc-R)-c\), and its Pell norm makes the auxiliary factor 1.
The strong factor is 1, the first/main residuals remain zero, and the shifted
inputs \(i-1,T-1\) are natural. This supplies the claimed parent zero
conditional on the original two-norm solution and (†).

Even m, the rank congruence (†), and the formal interpretation of this
constructive arithmetic inside a specified iPRA encoding remain open.

## Reproduction

The checker pins and reproduces both earlier branch certificates, checks the
Pell doubling identity for bounded even and odd A, and independently
constructs exact fact-level controls at **odd** multiplier A=3 for m=1 and
m=3. Both controls use R≠m; neither is asserted to be a graph zero. The
symbolic doubling and matrix proof above establishes the general corollary;
the finite checks do not. The predecessor's guarded nontrivial modular test
runs under its 20 s limit. No Lean, build, staging or model provider is used.

```sh
timeout 20s python3 -I -S -B research/ordinary13-shifted-two-norm-parent-odd-index-general-A/check.py | cmp - research/ordinary13-shifted-two-norm-parent-odd-index-general-A/receipt.json
```
