# Independent audit: power-increment kernel and endpoint-polynomial Gram matrices

The proposed integral identity, its beta evaluation, and the Gram consequences are correct. The only necessary wording qualification is that shift independence of the determinant applies to the initial matrix with indices `0,...,N`, not to every arbitrary principal submatrix.

## Integral and holomorphic domain

Put `u=s+t` and

\[
I(s,t)=\int_0^\infty
\bigl((x+1)^{-s}-x^{-s}\bigr)
\bigl((x+1)^{-t}-x^{-t}\bigr)\,dx.
\]

For `|s|,|t|<1/4`, this integral is jointly holomorphic. On a compact smaller bidisk, the integrand near zero is bounded by a constant times `1+x^(-2*rho)` with `rho<1/4`. For `x>=1`, the fundamental theorem of calculus gives

\[
(x+1)^{-s}-x^{-s}=-s\int_x^{x+1}v^{-s-1}\,dv,
\]

so the product is bounded by a constant times `x^(-2+2*rho)`. The same compact-domain domination, or the standard holomorphic-parameter integral theorem, justifies all order differentiations.

## A fully justified beta evaluation

The substitution `y=x/(1+x)` gives

\[
I(s,t)=\int_0^1(1-y)^{u-2}
\bigl(1-y^{-s}-y^{-t}+y^{-u}\bigr)\,dy.
\]

The four individual Euler beta integrals do **not** share a common domain of ordinary convergence. The following twice-subtracted formula makes their use rigorous. For `Re(a)>0`, `Re(b)>-2`, away from the displayed removable or meromorphic exceptions,

\[
B(a,b)=\int_0^1(1-y)^{b-1}
\bigl[y^{a-1}-1+(a-1)(1-y)\bigr],dy
+\frac1b-\frac{a-1}{b+1}.
\]

This is first obtained for `Re(b)>0` and then continued using the integral on the right, whose bracket vanishes to second order at `y=1`.

Apply it to `b=u-1` and to `a=1,1-s,1-t,1-u`, with respective coefficients `1,-1,-1,1`. Both the constant and the linear subtraction terms cancel since `u=s+t`. Therefore

\[
\begin{aligned}
I(s,t)
&=B(1,u-1)-B(1-s,u-1)-B(1-t,u-1)+B(1-u,u-1)\\
&=-\frac1{1-u}
-\Gamma(u-1)\left[
\frac{\Gamma(1-s)}{\Gamma(t)}+
\frac{\Gamma(1-t)}{\Gamma(s)}\right].
\end{aligned}
\]

Here `B(1-u,u-1)=0` by the meromorphic beta formula, initially away from exceptional `u` and then by removal. At `u=0`, all relevant expressions are interpreted by their joint holomorphic continuation.

The reciprocal-gamma reflection formula gives

\[
\frac{\Gamma(1-s)}{\Gamma(t)}+
\frac{\Gamma(1-t)}{\Gamma(s)}
=\frac{2\Gamma(1-s)\Gamma(1-t)}\pi
\sin\frac{\pi u}{2}\cos\frac{\pi(s-t)}2.
\]

Together with

\[
\Gamma(u-1)\Gamma(2-u)=-\frac\pi{\sin\pi u},
\]

this proves exactly

\[
\boxed{\quad\mathcal R(s,t)=\frac1{1-s-t}+I(s,t).\quad}
\]

## Polynomial Gram representation

For real `ell`, differentiating `exp((s+t)*ell)` times this identity gives

\[
\begin{aligned}
P_{r,q}(\ell)={}&\int_0^1(\ell-\log x)^{r+q}\,dx\\
&+\int_0^\infty
\bigl[(\ell-\log(x+1))^r-(\ell-\log x)^r\bigr]
\bigl[(\ell-\log(x+1))^q-(\ell-\log x)^q\bigr],dx.
\end{aligned}
\]

At zero, the logarithmic powers are integrable. At infinity, a difference of degree `r>=1` is bounded by `C*(1+log(x))^(r-1)/x`; the degree-zero difference vanishes identically. Thus every displayed Gram integral converges ordinarily.

Every finite principal matrix is positive definite: its first integral already represents the squared norm of a nonzero polynomial in `ell-log(x)` under a positive measure with interval support.

For the initial block

\[
P_N(\ell)=\bigl(P_{r,q}(\ell)\bigr)_{0\le r,q\le N},
\]

let `T_N(ell)` be the lower triangular binomial-shift matrix

\[
(T_N(\ell))_{r,k}=\binom rk\ell^{r-k}\quad(k\le r).
\]

Both Gram vector families transform by this same matrix, hence

\[
P_N(\ell)=T_N(\ell)P_N(0)T_N(\ell)^{\mathsf T},
\qquad\det T_N(\ell)=1.
\]

Consequently `det P_N(ell)` is independent of `ell`.

The first Gram matrix at zero is `G_N=((r+q)!)`. The identity

\[
\binom{r+q}{r}=\sum_k\binom rk\binom qk
\]

factors it as `G_N=D_N L_N L_N^T D_N`, where `D_N` has diagonal entries `r!` and `L_N` is the unit lower triangular Pascal matrix. Thus

\[
\det G_N=\prod_{r=0}^N(r!)^2.
\]

Since `P_N(0)=G_N+B_N` with `B_N` positive semidefinite,

\[
\boxed{\quad\det P_N(\ell)\ge\prod_{r=0}^N(r!)^2.\quad}
\]

For `N>=1`, the second Gram matrix is nonzero: its `(1,1)` entry is the positive integral of `log((x+1)/x)^2`. Therefore `G_N^(-1/2) B_N G_N^(-1/2)` is nonzero and positive semidefinite, so its determinant factor `det(I+G_N^(-1/2) B_N G_N^(-1/2))` is strictly greater than one. The inequality is strict for every `N>=1`; for `N=0` there is equality.

The initial-block qualification is material: the one-entry principal matrix consisting only of `P_11(ell)=ell^2+2*ell+2+pi^2/3` has a determinant that depends on `ell`.

This note audits the identities and proofs, without making a global priority claim.
