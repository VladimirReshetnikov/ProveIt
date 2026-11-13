# Actual two-norm restrictions on the parent-lift conditions

At the exact fixed compact tuple, restrict the shifted two-norm graph to
\(J=1\), so \(q=2^{67\cdot8807}\). Suppose its actual **main** norm is
zero, and write

\[
X=qw,\quad Y=q^3s,\quad U=q^5s,\quad a=Y(X+1),\quad
H=4a+3,\quad g=\gcd(s,3),
\]

where the shifted graph has \(s\ge1\). Then necessarily

\[
\gcd\!\left(w,\frac Hg\right)=1. \tag{1}
\]

In particular, the slice \(w\equiv0\pmod5\), \(s\equiv1\pmod5\)
cannot satisfy even the main norm. This is an actual compact-port subcase
exclusion, not a full graph no-zero result.

If both actual norms are zero, standard Pell descent supplies a main index m
and first index n. Then R is odd and \(c\equiv m\pmod2\). Consequently

\[
c\mid(R-m)\quad\Longrightarrow\quad m\text{ is odd}. \tag{2}
\]

Finally, if \(w=1\) and \(s\equiv2\pmod5\), the main norm forces
\(m\equiv1\pmod4\) for **either** sign of its actual root. Thus the
[m≡3 conditional parent lift](../ordinary13-shifted-two-norm-parent-explicit-index-lift/README.md)
cannot apply directly in that conditional slice. This does not prove that a
two-norm zero exists in the slice, or that no other lift can handle it.
Changing only the auxiliary f, i, T, y inputs leaves m and R fixed; it cannot
change either scalar hypothesis. Changing first/main witnesses remains open.

## Why the unit forces (1)

The main norm and \(U>0\) give an integer \(d=D_*/U\) with
\(d^2-\Delta c^2=1\), where \(\Delta=a^2+H\). The literal root
formula is

\[
D_*=U(X+ac)+H(U\gamma+R+1-k).
\]

As H is odd and \(H\equiv3\pmod s\),
\(\gcd(H,U)=\gcd(H,s)=g\). Hence the root equation yields
\(d-ac\equiv X\pmod{H/g}\). But
\((d-ac)(d+ac)=1+Hc^2\), so d−ac is a unit modulo H/g. Therefore X,
and hence w (q is coprime to H), is a unit modulo H/g, proving (1).
In particular w>0 because H/g>1.

The pinned fixed exponent gives \(q\equiv2\pmod5\). If
\(5\mid w\) and \(s\equiv1\pmod5\), the actual H satisfies
\(H\equiv4q^3s+3\equiv0\pmod5\). As g is 1 or 3,
\(5\mid H/g\), contradicting (1). This exclusion uses no first norm,
rank equality, auxiliary witness, or assumed main index.

## Parity of m and the rank

Once w>0, \(M=XY^2>0\). The actual first norm and standard
first-Pell descent give even k. Also \(q^5\mid U\), H is odd, and the
actual main-root equation above gives
\(q^5\mid R+1-k\). Hence R is odd. For the main Pell multiplier
\(A=a+2\), A is even; its recurrence modulo 2 gives
\(y_m(A)\equiv m\pmod2\), so \(c\equiv m\pmod2\). If m were even,
c would be even while R−m is odd, making \(c\mid R-m\) impossible.
This proves (2), but it neither proves \(c\mid R-m\) nor determines m
modulo 4.

## An actual main-root consequence at w=1

For w=1, \(X=q\), \(a=q^3s(q+1)\). Since \(q\equiv2\pmod5\),
\(H\equiv s+3\pmod5\). Thus \(s\equiv2\pmod5\) makes
\(5\mid H/g\). Let \((x_m,c)\) be the main Pell pair and let the
signed root d be \(+x_m\) or \(-x_m\). The recurrence and norm give

\[
x_m-ac\equiv2^m,\qquad x_m+ac\equiv2^{-m}\pmod{H/g}.
\]

The actual root congruence \(d-ac\equiv q\) modulo 5 therefore gives
\(2^m\equiv2\) for the positive sign, and
\(-2^{-m}\equiv2\) for the negative sign. Both imply
\(m\equiv1\pmod4\). No equality between m and R is used. If such a
zero exists, its m cannot satisfy the stated m≡3 sufficient condition; the
existence of that zero and other parent-completion strategies are unresolved.

## Reproduction and scope

The checker pins the literal nine-variable graph, fixed beta and prior
conditional lifts, verifies the necessary field rows and source signatures,
exhausts the relevant small residues, and runs bounded gcd/Pell controls. The
general unit, parity and signed-root arguments above justify the conclusions;
finite controls alone do not. No large compact numeral, Lean process, build,
staging, provider validation, model theorem or iPRA result is produced.

```sh
python3 -I -S -B research/ordinary13-shifted-two-norm-lift-obligation-obstructions/check.py | cmp - research/ordinary13-shifted-two-norm-lift-obligation-obstructions/receipt.json
```
