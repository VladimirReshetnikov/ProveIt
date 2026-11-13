# An exact obstruction to universal same-witness auxiliary completion

At the exact fixed compact ports there is a symbolic **partial** assignment
for the shifted-zeta free-square graph with a natural main Pell ordinate and
a valid even-index strong witness, but no original-parent auxiliary
completion preserving that witness and the other data. The first necessary
auxiliary congruence already fails modulo 31, for both signs and every odd
auxiliary Pell index.

This is **not** a two-norm child zero or a counterexample to the requested
existential reverse bridge. In fact, the selected main index is 2 and the
actual signed main graph root cannot satisfy its norm. It also does not rule
out choosing a different strong witness. It shows only that the two abstract
facts “c is a main Pell ordinate” and “f is an even-period strong witness”
do not by themselves make a same-data odd-index/CRT completion automatic.

## Exact compact partial data

Let \(N=67\cdot8807\), \(q=2^N\), and take the actual graph inputs
\(J=1\), \(w=1\), and \(s=31\). Define

\[
Y=31q^3,\quad a=Y(q+1),\quad A=a+2,\quad
\Delta=A^2-1,\quad c=2A.
\]

The graph represents this c with \(\eta=4\),
\(k=2(q+1)\), and shifted \(\zeta=2q-2\ge1\), because
\(Yk+\eta=2A\). Thus the actual input is
\(n_\zeta=2q-3\ge0\). Also c is precisely the main Pell ordinate at
index 2. F, alpha, the computed rank R, r, gamma, and the unused child
auxiliary-square input may be assigned any natural values compatible with
their graph shifts; no norm or full-zero claim is made about them.

For the Pell sequence \((x_j,v_j)\) of multiplier A, take the **even**
index \(h=4A\), and set

\[
f=x_h,\qquad i=\frac{\Delta v_h}{c^2},\qquad I=c^2i=\Delta v_h.
\]

Here i is a positive natural. To see \(c^2=4A^2\mid v_h\), put
\(z_j=v_{2j}\). The even subsequence has recurrence
\(z_{j+2}=2(2A^2-1)z_{j+1}-z_j\), with \(z_0=0,z_1=2A\).
Modulo \(4A^2\) induction gives
\(z_j\equiv(-1)^{j-1}2Aj\); at \(j=2A\) this vanishes. The norm
\(f^2-\Delta v_h^2=1\) now gives the **actual** strong equality
\(\Delta(f^2-1)=I^2\). The graph input \(n_i=i-1\) is natural.

## The first auxiliary congruence fails for all odd indices

Because \(31\mid s\), \(A\equiv2\pmod{31}\), so \(c\equiv4\)
and \(\Delta\equiv3\pmod{31}\). Also \(A\equiv2\pmod8\), hence
\(h=4A\equiv8\pmod{32}\). At multiplier 2 the Pell pair at index 8
is \((0,14)\pmod{31}\), and the transition has period dividing 32.
Therefore \(31\mid f=x_h\).

Suppose a parent completion with these same data existed. Its auxiliary Pell
classification from the [exact reverse criterion](../ordinary13-shifted85-free-aux-square-criterion/README.md)
would give an odd \(\ell=2j+1\), a sign \(\epsilon\), and in
particular

\[
\epsilon\frac{x_\ell(I)}I+c\equiv0\pmod{f^2}.
\]

Strong equality and \(31\mid f\) give \(I^2\equiv-3\equiv28\pmod{31}\),
so I is invertible modulo 31. For the Pell sequence of multiplier I, define
\(v_j=x_{2j+1}(I)/I\), an integer. The odd subsequence satisfies

\[
v_{j+2}=(4I^2-2)v_{j+1}-v_j,\quad v_0=1,\quad v_1=4I^2-3.
\]

Modulo 31 its initial values are 1, 16 and its multiplier is 17. It has
period dividing 16 with values
\(\{\pm1,\pm3,\pm8,\pm15\}\). Neither \(4\) nor \(-4\) occurs.
Hence the displayed congruence is impossible even modulo 31, independently
of R and of the separate positivity and rank congruence needed for T.

## Why this does not refute the reverse bridge

For these same partial data the actual main residual **cannot** be zero. Its
root is \(D_*=U(q+ac)+H(U\gamma+R+1-k)\), with
\(U=q^5\cdot31\), \(H=4a+3\), and \(\gcd(H,U)=1\). If its norm
vanished, \(U\mid D_*\) and hence \(d=D_*/U=\pm x_2(A)\) would
satisfy \(d-ac\equiv q\pmod H\). The Pell identities
\(x_2-ac\equiv4\) and \((x_2-ac)(x_2+ac)\equiv1\pmod H\)
would require either \(H\mid q-4\) or \(H\mid4q+1\). Both positive
integers are strictly less than H for the fixed q≥8. Thus this is a
main-Pell **ordinate**, not a solution of the actual signed main-root
constraint, and it cannot be a two-norm child zero.

The parent-completion condition may still follow from the two actual norm
constraints, from other graph factors, or after changing the chosen strong or
other witnesses. No Lean, model proof, global zero exclusion, or iPRA result
is claimed.

## Reproduction

The checker pins the shifted graph, exact reverse criterion, compact beta and
Pell source; it verifies the literal field wiring, the two finite mod-31
cycles, and bounded controls of the even-index divisibility. A q=8 control
uses modular exponentiation only; neither the fixed compact q nor any
astronomical Pell iterate is expanded. The displayed general induction and
congruence argument supply the proof.

```sh
python3 -I -S -B research/ordinary13-shifted-free-aux-odd-index-31-obstruction/check.py | cmp - research/ordinary13-shifted-free-aux-odd-index-31-obstruction/receipt.json
```
