# Exact frozen ternary boundary audit

This note verifies the frozen transfer and supplies coercive forms. It does **not** prove a moving-weight Airy approximation or a limiting-amplitude theorem.

## 1. The one-step transfer

On functions on the nonnegative integers, set

\[
(Tf)(j)=2f(j-1)+f(j+2),\qquad f(-1)=0.
\]

The transpose with respect to counting measure is

\[
(T^*g)(j)=2g(j+1)+g(j-2),\qquad g(-1)=g(-2)=0.
\]

Then the positive edge profiles, normalized to have slope one, are exactly

\[
h(j)=j+1,\qquad
\ell(j)=j+\frac43+\frac16\left(-\frac12\right)^j,
\]

and satisfy \(Th=3h\), \(T^*\ell=3\ell\).

The boundary values are not merely asymptotic identities:

\[
h(-1)=0,\quad
\ell(-1)=\frac13-\frac13=0,\quad
\ell(-2)=-\frac23+\frac23=0.
\]

For the right bulk equation the characteristic polynomial is
\((z-1)^2(z+2)\); thus a bulk solution has the form
\(a+bj+c(-2)^j\). Nonnegativity on the whole half-line forces \(c=0\), and the boundary gives \(a=b\). Hence every nonzero nonnegative right edge harmonic is a positive multiple of \(h\).

For the left bulk equation the polynomial is \((z-1)^2(2z+1)\). The two boundary equations, for \(a+bj+c(-1/2)^j\), give \(a=4b/3\), \(c=b/6\). Thus the left edge solution is unique up to scalar even without a positivity restriction.

Useful elementary inequalities are

\[
\frac14\leq \ell(j)-h(j)\leq\frac12,
\qquad 1\leq\frac{\ell(j)}{h(j)}\leq\frac32.
\]

These are formal positive harmonic profiles, not square-summable eigenvectors. The counting-measure operator has spectral radius 3: its norm is at most 3, and almost-constant vectors supported far from the boundary give an approximate eigenvalue 3.

## 2. Residue decomposition and all three blocks

Write \(f_r(k)=f(3k+r)\), \(r=0,1,2\). Let the lower unilateral shift be
\((Sf)(k)=f(k-1)\), with \(f(-1)=0\), and \((S^*f)(k)=f(k+1)\). Set

\[
A=2I+S^*,\qquad C=I+2S.
\]

The residue components obey

\[
(Tf)_0=Cf_2,\qquad (Tf)_1=Af_0,\qquad (Tf)_2=Af_1.
\]

Consequently

\[
B_0=CA^2,\qquad B_1=ACA,\qquad B_2=A^2C.
\]

Let \(E_{ij}=|i\rangle\langle j|\), and put

\[
L=12I+6S^*+(S^*)^2+8S.
\]

Since \(SS^*=I-E_{00}\), \(S^*S=I\), and
\(S(S^*)^2=S^*-E_{01}\), the exact block identities are

\[
\boxed{B_0=L-8E_{00}-2E_{01}},\qquad
\boxed{B_1=L-4E_{00}},\qquad
\boxed{B_2=L}.
\]

For every block and every \(k\geq1\),

\[
(B_rf)(k)=8f(k-1)+12f(k)+6f(k+1)+f(k+2).
\]

The three zeroth rows are

\[
\begin{aligned}
(B_0f)(0)&=4f(0)+4f(1)+f(2),\\
(B_1f)(0)&=8f(0)+6f(1)+f(2),\\
(B_2f)(0)&=12f(0)+6f(1)+f(2).
\end{aligned}
\]

The adjoint bulk equation, for \(k\geq2\), is

\[
(B_r^*g)(k)=g(k-2)+6g(k-1)+12g(k)+8g(k+1).
\]

There are **two** adjoint boundary rows:

| Block | \((B_r^*g)(0)\) | \((B_r^*g)(1)\) |
|---|---|---|
| \(r=0\) | \(4g(0)+8g(1)\) | \(4g(0)+12g(1)+8g(2)\) |
| \(r=1\) | \(8g(0)+8g(1)\) | \(6g(0)+12g(1)+8g(2)\) |
| \(r=2\) | \(12g(0)+8g(1)\) | \(6g(0)+12g(1)+8g(2)\) |

## 3. Period-three compatible profiles

Define

\[
h_r(k)=3k+r+1,
\qquad
\ell_r(k)=3k+r+\frac43+
\frac16\left(-\frac12\right)^r\left(-\frac18\right)^k.
\]

They satisfy the one-step intertwining relations

\[
Ah_0=3h_1,\quad Ah_1=3h_2,\quad Ch_2=3h_0,
\]

\[
A^*\ell_1=3\ell_0,\quad
A^*\ell_2=3\ell_1,\quad
C^*\ell_0=3\ell_2.
\]

Therefore

\[
\boxed{B_rh_r=27h_r,\qquad B_r^*\ell_r=27\ell_r}
\]

with the exact boundary rows above. At the boundary,

\[
(h_0(0),h_1(0),h_2(0))=(1,2,3),\qquad
(\ell_0(0),\ell_1(0),\ell_2(0))=
\left(\frac32,\frac94,\frac{27}{8}\right).
\]

The block right characteristic polynomial is
\((z-1)^2(z+8)\). Nonnegative right edge profiles cannot contain the alternating growing mode \((-8)^k\), and each zeroth-row condition selects the stated linear profile. The left characteristic polynomial is
\((z-1)^2(8z+1)\); the two adjoint boundary rows select the stated linear-plus-\((-1/8)^k\) solution.

For each block, \(27\) is the counting-measure spectral radius, by the same norm bound and bulk approximate-eigenvector argument as for \(T\).

## 4. The residue-zero Doob transform

For the rest of the note abbreviate

\[
B=B_0,\quad h_k=3k+1,\quad
\ell_k=3k+\frac43+\frac16\left(-\frac18\right)^k,
\quad \rho_k=\ell_k/h_k.
\]

Define the Markov kernel and invariant measure

\[
P_{ij}=\frac{B_{ij}h_j}{27h_i},\qquad
\pi_i=h_i\ell_i.
\]

The row-sum identity follows from \(Bh=27h\), and stationarity from

\[
\sum_i\pi_iP_{ij}
=\frac{h_j}{27}\sum_i\ell_iB_{ij}
=h_j\ell_j=\pi_j.
\]

This is an infinite invariant measure, with \(\pi_k\asymp(k+1)^2\); it is not a probability distribution. The kernel is nonreversible because there are jumps of size +2 but none of size -2.

The exact boundary transition probabilities are

\[
P_{00}=\frac4{27},\qquad
P_{01}=\frac{16}{27},\qquad
P_{02}=\frac7{27}.
\]

For \(k\geq1\),

\[
\begin{aligned}
P_{k,k-1}&=\frac{8(3k-2)}{27(3k+1)},&
P_{kk}&=\frac49,\\
P_{k,k+1}&=\frac{6(3k+4)}{27(3k+1)},&
P_{k,k+2}&=\frac{3k+7}{27(3k+1)}.
\end{aligned}
\]

All residue blocks admit the analogous Doob transform with invariant measure \(h_r\ell_r\). The normalized one-step residue maps transport these measures cyclically, since the displayed intertwining relations hold on both sides.

## 5. Exact Dirichlet form and nearest-neighbor coercivity

Use the Hilbert norm \(\|f\|_\pi^2=\sum_k\pi_k|f_k|^2\). For a finitely supported real or complex sequence, set

\[
\mathcal E(f)=\operatorname{Re}\langle f,(I-P)f\rangle_\pi.
\]

Stationarity, not reversibility, gives

\[
\mathcal E(f)=\frac12\sum_{i,j}\pi_iP_{ij}|f_i-f_j|^2.
\]

Put \(b_0=4\), \(b_k=6\) for \(k\geq1\). Grouping unordered edges gives the exact identity

\[
\boxed{\mathcal E(f)=\sum_{k\geq0}c_k|f_{k+1}-f_k|^2
+\sum_{k\geq0}d_k|f_{k+2}-f_k|^2},
\]

where

\[
c_k=\frac{b_k\ell_kh_{k+1}+8\ell_{k+1}h_k}{54},
\qquad d_k=\frac{\ell_kh_{k+2}}{54}.
\]

In particular, \(c_0=13/12\) and \(d_0=7/36\). Let

\[
w_k=h_kh_{k+1}=(3k+1)(3k+4),\qquad
\mathcal Q(f)=\sum_{k\geq0}w_k|f_{k+1}-f_k|^2.
\]

For \(k\geq1\),
\(c_k/w_k=(6\rho_k+8\rho_{k+1})/54\geq7/27\).
At \(k=0\), \(c_0/w_0=13/48>7/27\). Therefore

\[
\boxed{\mathcal E(f)\geq\frac7{27}\mathcal Q(f)
\geq\frac7{27}\sum_k\pi_k|f_{k+1}-f_k|^2}.
\]

The last inequality uses \(\ell_k\leq h_{k+1}\). The constant \(7/27\) is sharp for the individual nearest-neighbor conductance comparison because \(c_k/w_k\to7/27\). This statement is not a claim of sharpness for a global comparison that also uses the length-two edges.

A convenient explicit reverse comparison is

\[
\boxed{\mathcal E(f)\leq\frac{53}{144}\mathcal Q(f)}.
\]

Indeed, \(|f_{k+2}-f_k|^2\leq2|\Delta f_k|^2+2|\Delta f_{k+1}|^2\). The resulting coefficient divided by \(w_k\) is
\(R_k=(c_k+2d_k+2d_{k-1})/w_k\), where \(d_{-1}=0\). Here
\(R_0=53/144\). For \(k\geq1\), writing \(h=3k+1\) and \(t=(-1/8)^k\), direct simplification gives

\[
R_k=\frac13+
\frac{(h-1)-(h+2)t/4}{9h(h+3)}.
\]

Since \(h\geq4\), \(|t|\leq1/8\), the second term is at most
\(1/[8(h+3)]\leq1/56\), so \(R_k<53/144\).

Thus this nonreversible transfer has a Dirichlet form uniformly equivalent to an explicit nearest-neighbor form of three-dimensional radial type.

## 6. Stronger coercivity for actual norm loss

Controlling \(\mathcal E\) alone should not be silently identified with a bound on \(\|Pf\|_\pi\). Here actual norm loss has its own exact positive form:

\[
\begin{aligned}
\mathcal V(f)&=\|f\|_\pi^2-\|Pf\|_\pi^2\\
&=\frac12\sum_i\pi_i\sum_{j,k}P_{ij}P_{ik}|f_j-f_k|^2\\
&=\sum_{k\geq0}\sum_{m=1}^3D_{k,m}|f_{k+m}-f_k|^2.
\end{aligned}
\]

These are the conductances of the reversible kernel \(P^*P\), where \(P^*\) now means the adjoint in \(\ell^2(\pi)\). Their exact values are

\[
D_{k,1}=\frac{h_kh_{k+1}}{729}
\begin{cases}
16\rho_0+96\rho_1,&k=0,\\
4\rho_0+72\rho_1+96\rho_2,&k=1,\\
6\rho_{k-1}+72\rho_k+96\rho_{k+1},&k\geq2,
\end{cases}
\]

\[
D_{k,2}=\frac{h_kh_{k+2}}{729}
\bigl(a_k\rho_k+48\rho_{k+1}\bigr),
\quad a_0=4,\ a_k=12\ (k\geq1),
\]

\[
D_{k,3}=\frac{8h_kh_{k+3}}{729}\rho_{k+1}.
\]

Since \(\rho_0=3/2\), \(\rho_1=69/64\),

\[
\frac{D_{0,1}}{w_0}
=\frac{16(3/2)+96(69/64)}{729}=\frac{85}{486}.
\]

For \(k=1\) the bracket is at least 172, and for \(k\geq2\) it is at least 174, both exceeding \(729(85/486)=255/2\). Hence

\[
\boxed{\|f\|_\pi^2-\|Pf\|_\pi^2
\geq\frac{85}{486}\mathcal Q(f)
\geq\frac{85}{486}\sum_k\pi_k|\Delta f_k|^2}.
\]

The coefficient is sharp for the nearest-neighbor conductance comparison for \(P^*P\), with equality of those coefficients at the zeroth edge. No global optimality is asserted.

A shorter but weaker route uses global laziness: \(P_{kk}\geq\alpha=4/27\), so \(P=\alpha I+(1-\alpha)Q\) with a stationary Markov contraction \(Q\). It yields

\[
\mathcal V(f)\geq2\alpha\mathcal E(f)
\geq\frac{56}{729}\mathcal Q(f).
\]

## 7. Exact resistance and a finite-interval estimate

The comparison weight has the telescoping identity

\[
\boxed{\sum_{j=k}^N\frac1{w_j}
=\frac13\left(\frac1{h_k}-\frac1{h_{N+1}}\right)}.
\]

In particular the resistance of the comparison chain from \(k\) to infinity is \(1/(3h_k)\).

If \(f\) is supported on \(\{0,\ldots,N\}\), then Cauchy–Schwarz and \(f_{N+1}=0\) give

\[
\|f\|_\pi^2\leq C_N\mathcal Q(f),\qquad
C_N=\frac13\sum_{k=0}^N\ell_k
\left(1-\frac{h_k}{h_{N+1}}\right).
\]

This is an explicit finite positive sum; \(C_N\sim N^2/6\). Also
\(\ell_k\leq3k+3/2\) gives the simple bound
\(C_N\leq(N+1)^2/2\).

For the killed restriction \(P_N\) to these sites, zero extension and the full-line norm-loss estimate imply

\[
\|P_Nf\|_\pi^2\leq
\left(1-\frac{85}{486C_N}\right)\|f\|_\pi^2
\leq
\boxed{\left(1-\frac{85}{243(N+1)^2}\right)\|f\|_\pi^2}.
\]

Thus an explicit, boundary-uniform diffusive contraction estimate is available without treating the original transfer as self-adjoint.

## 8. Verification and limits of the result

The accompanying `verify_frozen_ternary.py` uses Python's exact `Fraction` arithmetic, with no external dependencies. It checks all three edge-profile equations and boundary rows, the residue intertwinings, Markov row sums, the Dirichlet and norm-loss identities on finitely supported test vectors, all stated conductance comparisons, and the telescoping resistance formula.

The formulas above are exact frozen-operator facts. To apply them to moving Airy weights one still needs, separately, control of the changing multiplication weights, the associated weighted norms or conjugations, localization, and the accumulated nonautonomous errors. Frozen coercivity alone does not establish positivity or convergence of a claimed limiting amplitude.
