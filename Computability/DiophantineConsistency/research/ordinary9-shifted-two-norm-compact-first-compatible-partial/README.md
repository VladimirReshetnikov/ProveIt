# A compact first-norm witness compatible with main-root divisibility

For the exact fixed compact tuple, the nine-variable shifted two-norm graph
has a fully symbolic family of natural inputs for which its **first** norm
residual is zero and its actual signed main root is divisible by its main
scale U. The natural eta coordinate may be any \(0\le\eta<k\). The remaining
main norm is not established: this packet does **not** construct a zero of
the two-norm graph, its free-square child, or the original parent, and does
not assume a relationship between the main Pell index and the graph rank.

## Fixed compact choices

Let

\[
\rho=2^{67},\quad q=2^{67\cdot8807},\quad \beta=q-1,\quad
K_0=\beta\rho^{42}+K'.
\]

The pinned compact kernel has \(0<K'<\rho^{5496}\), and
\(67\cdot5496<67\cdot8807-1\). Hence with

\[
t=(\beta-1)/2,\quad w=t-K',
\]
we have \(t,w\) positive natural integers. Set

\[
J=1,\ F=1,\ \alpha=2,\ s=1,\quad
X=qw,\quad Y=q^3,\quad U=q^5,\quad M=XY^2=q^7w.
\]

The actual graph coefficient is \(C=q-F-\alpha=\beta-2\), and its
actual first carrier is \(B=C(X+K_0)-1=\beta h\), where the explicitly
natural positive quotient is

\[
h=(\beta-2)(w+\rho^{42})+t-1.
\]

This equality is exact: \(X+K_0=\beta(w+\rho^{42})+t\) and
\(2t+1=\beta\). It uses the source-defined compact K0, not an
independently chosen carrier.

## Actual rank and first norm

The literal rank for F=1 and alpha=2 is

\[
R=(\beta^2+2)(q^2-1)+MC+qMF.
\]

It is a positive odd integer. Indeed beta is odd, q is even, the compact
low mask MC is even (its least base-\(\rho\) digit is \(\rho-2\)),
and the other fixed masks are natural. Put \(n=(R+1)/2\ge1\).

Use the first-Pell recurrence with \(D=M(M+1)\) and starting pair
\((\tau_0,k_0)=(1,0)\):

\[
\begin{aligned}
\tau_{j+1}&=(2M+1)\tau_j+2Dk_j,\\
k_{j+1}&=2\tau_j+(2M+1)k_j.
\end{aligned}
\]

At index n, write \(\tau=\tau_n\), \(k=k_n\). Its norm gives
\(\tau^2=1+M(M+1)k^2\). Moreover \(\tau_j\equiv1\pmod{2M}\),
all \(k_j\) are even, and each step adds 2 modulo \(4M\). Since
\(k_j\ge2j\), there is a natural \(\sigma\) such that

\[
k=2n+4M\sigma=R+1+4M\sigma.
\]

Let \(\ell=Mk\) and choose
\(r=\tau-\ell-k+(k\beta+1)h\). It is natural because \(h\ge1\)
and \(\tau>\ell\). Substituting into the *literal* first root yields
\(Z=\beta\tau\), so the actual \(A_0\) is zero. No enormous Pell
coordinate need be expanded to specify this witness.

For every natural \(\eta<k\), set the shifted input
\(n_\zeta=k-\eta-1\). Then the graph's k is exactly the chosen k and
\(c=Yk+\eta\). The other selected nine inputs are
\(n_J=1,n_F=0,n_\alpha=1,n_w=w,n_s=0,n_r=r\), and any
natural \(n_\gamma=\gamma\).

## The unresolved actual main norm

Because \(M/U=q^2w\), the chosen index gives
\(R+1-k=-4M\sigma\), a multiple of U. With the graph definitions
\(a=Y(X+1)\), \(H=4a+3\), and \(\Delta=a^2+H\), its actual
signed root satisfies

\[
D_*/U=d=X+ac+H(\gamma-4q^2w\sigma).
\]

Thus the main-root scale divisibility is satisfied for every natural gamma,
with the actual fixed rank and without an index assumption. What remains is
to find \(0\le\eta<k\) and \(\gamma\ge0\) such that

\[
d^2=1+\Delta(Yk+\eta)^2.
\]

Equivalently, the particular ordinate must lie on the corresponding Pell
conic and one of its signed roots must lie in the displayed arithmetic
progression with a nonnegative gamma. Neither existence nor nonexistence is
proved here. Completion of that step would still need to be assessed against
the distinct free-square and original-parent proof boundaries.

## Reproduction

The checker pins the literal nine-variable graph, compact kernel recipe and
independent first-norm sources. It reproduces the earlier fixed-kernel bound,
checks the exact field wiring and bounded carrier/root controls, and tests a
noncompact q=8 example using **modular** Pell powering only. The symbolic
algebra above gives the compact construction; the controls do not solve the
main norm. The predecessor reconstructs beta and K′ in memory, with beta
590,069 bits (about 74 kB); no large numerals are printed or written, and
no giant Pell coordinate is expanded. No Lean, build, model provider, iPRA
proof, or full zero is claimed.

```sh
python3 -I -S -B research/ordinary9-shifted-two-norm-compact-first-compatible-partial/check.py | cmp - research/ordinary9-shifted-two-norm-compact-first-compatible-partial/receipt.json
```
