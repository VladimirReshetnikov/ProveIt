# An explicit parent lift for main index 1 modulo 4

Let a standard natural solution of the [shifted nine-variable two-norm graph](../ordinary9-shifted-free-aux-two-norm64/README.md)
have nonnegative ports with \(\beta>0\), actual rank R, even main Pell
multiplier \(A=a+2\), and main ordinate \(c=y_m(A)>0\). Suppose

\[
m\equiv1\pmod4,\qquad c\mid(R+m). \tag{†}
\]

Then the original shifted 85-row parent has a natural zero preserving the
first/main coordinates. The construction gives actual strong and square
auxiliary witnesses. It is a **conditional** standard-integer lift, not a
proof that (†) follows from arbitrary two-norm zeros, not a constructed graph
zero, and not a Lean, model, iPRA or Con(ZFC) result. In particular it does
not assume \(m=R\). The fixed compact \(J=1\) slice has q even, hence
Y and a even and the stated even-A hypothesis.

Together with the [explicit 3-mod-4 lift](../ordinary13-shifted-two-norm-parent-explicit-index-lift/README.md),
this gives a single sufficient scalar condition for **odd** m and even A:

\[
c\mid R+(-1)^{(m-1)/2}m.
\]

The previous branch handles \(m\equiv3\) and \(c\mid R-m\); the
present branch handles \(m\equiv1\) and \(c\mid R+m\). Even m,
other multiplier parities, and derivation of these congruences from the two
norms remain open.

## Explicit strong witness and a negative half-period

Use the previous lift's construction. For the Pell transition Q with
multiplier A and discriminant \(\Delta=A^2-1\), put \(h=2mc\).
Its explicit matrix identity proves \(Q^h\equiv\mathrm{Id}\pmod{c^2}\).
Let \((f,v)=(x_h(A),y_h(A))\), and define

\[
i=\Delta v/c^2,\qquad I=c^2i=\Delta v.
\]

These are positive natural integers, and the actual strong equation is
\(I^2=\Delta(f^2-1)\). Also \(f^2\equiv1\pmod c\), so f and c
are coprime. Because A is even and h is even, the Pell recurrence modulo 2
shows f is **odd**.

The matrix identity from the general lift gives
\(Q^{2h}\equiv-\mathrm{Id}+2fB\pmod{f^2}\) for an integer matrix B.
Raising to the odd power f and using the binomial formula yields

\[
Q^{2hf}\equiv-\mathrm{Id}\pmod{f^2}.
\]

Set the auxiliary index

\[
L=2hf-m.
\]

It is positive and at least m, because h=2mc and f≥2. Since h is even and
\(m\equiv1\pmod4\), \(L\equiv3\pmod4\). Moreover, h is divisible
by c, so \(L\equiv-m\pmod c\). The inverse Pell matrix is integral;
using the negative half-period above,

\[
Q^L=Q^{2hf}Q^{-m}\equiv-Q^{-m}\pmod{f^2}.
\]

Its lower-left entry therefore gives \(y_L(A)\equiv c\pmod{f^2}\).

## Positive auxiliary witness

Let \((z_j,y_j)\) be the Pell sequence of multiplier I and set
\(V=z_L/I>0\). L is odd, so this quotient is an integer. The same
odd-quotient polynomial identities used in the general lift, with
\(L\equiv3\pmod4\), imply

\[
V\equiv-y_L(A)\equiv-c\pmod{f^2},\qquad
V\equiv-L\equiv m\pmod c.
\]

As \(f^2\equiv1\pmod c\) and (†) gives \(R+m\equiv0\pmod c\),
the coprime moduli f² and c imply

\[
f^2c\mid V+c+f^2R,\qquad
T=\frac{V+c+f^2R}{f^2c}.
\]

R>0 follows from the actual first norm, shifted positive F/alpha/k,
nonnegative ports and beta>0, as established in the general lift. Hence T≥1.
Set the actual parent auxiliary input to \(y=y_L(I)\). Then
\(V=f^2(Tc-R)-c\), and its Pell norm makes the actual auxiliary factor
one. With \(n_i=i-1\) and \(n_T=T-1\), both strong and auxiliary
witnesses are natural; the untouched first/main residuals remain zero.

The scalar congruence and the odd-index assumption remain open for arbitrary
actual two-norm zeros. In the compact J=1 slice, the separately derived
[parity restriction](../ordinary13-shifted-two-norm-lift-obligation-obstructions/README.md)
shows that the previously proposed \(c\mid R-m\) cannot hold for even m;
it does not exclude all other constructions. Formalizing this finite matrix,
Pell and divisibility argument in a specified iPRA encoding is separate work.

## Reproduction

The checker pins and reproduces the preceding explicit lift, verifies an exact
fact-level example with \(A=2,m=1,c=1,L=27,R=2\), and performs a
nontrivial \(m=5,c=209\) control of the quotient and matrix congruences by
modular powering without expanding the enormous auxiliary coordinate. Neither
control is asserted to be a graph zero. The symbolic negative-half-period and
polynomial congruences above provide the general proof. The checker has
256 MiB address-space, 15 s CPU and zero core-file limits; the command adds a
20 s wall-clock guard. No Lean, build, staging, or giant auxiliary Pell
expansion is used.

```sh
timeout 20s python3 -I -S -B research/ordinary13-shifted-two-norm-parent-odd-index-lift/check.py | cmp - research/ordinary13-shifted-two-norm-parent-odd-index-lift/receipt.json
```
