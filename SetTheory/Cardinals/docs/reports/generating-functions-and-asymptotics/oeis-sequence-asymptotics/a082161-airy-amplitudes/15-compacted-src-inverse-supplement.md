# A254789 inverse expansion and exact discrete interpretation

Prepared 2 October 2026. Conditional on the candidate forward theorem until that theorem is independently approved. The inversion algebra is generic and is specialized here to the compacted coefficients. `inverse_check.py` verifies the symbolic cancellations and tests the truncated smooth model; its fitted amplitude is not a certified number.

## 1. Logarithmic forward model

Let z be the largest Airy zero and gamma_c the proposed positive limiting amplitude. The first three proposed logarithmic corrections are

\[
B=53z^2/90,\qquad D=271z/216,\qquad
L_3=393/1120-1304z^3/42525.
\]

With A=3z, p=5/4, C=log(gamma_c sqrt(2pi)), and

\[
E=L_3+1/12=1459/3360-1304z^3/42525,
\]

define the explicit smooth model

\[
h(t)=t\log(4t/e)+At^{1/3}+p\log t+C+Bt^{-1/3}+Dt^{-2/3}+Et^{-1}.
\tag{1}
\]

Then the forward theorem gives log c_n=h(n)+O(n^(-4/3)). The factorial contributes both +1/2 log n and +1/(12n); omitting either changes the inverse. As t grows, h'(t)~log(4t)>0 and h''(t)~1/t.

## 2. Lambert anchor and explicit inverse

For T=log Y, put

\[
x=\frac{T}{W_0(4T/e)},\qquad s=\log(4x),\qquad q=p\log x+C.
\]

Then x log(4x/e)=T. Define

\[
\begin{split}
u&=-A/s,\qquad v=-q/s,\\
w&=-B/s+A^2/(3s^2)-A^2/(2s^3),\\
r&=-D/s+A(p+q/3)/s^2-Aq/s^3,\\
k&=-E/s+pq/s^2-(AB+q^2/2)/s^3+A^3/(3s^4)-A^3/(2s^5).
\end{split}
\]

The inverse of the explicit smooth model satisfies

\[
h^{-1}(T)=x+ux^{1/3}+v+wx^{-1/3}+rx^{-2/3}+kx^{-1}
+O(x^{-4/3}/s).
\tag{2}
\]

In particular,

\[
h^{-1}(T)=x-\frac{3z}{s}x^{1/3}-\frac54+
\frac{(5/4)\log4-C}{s}+O(x^{-1/3}/s).
\tag{3}
\]

The Airy displacement is positive because z<0; the factorial/prefactor shift is -5/4; the unknown amplitude first appears at order 1/log x.

To verify (2), let t=x^(-1/3), delta=u/t+v+wt+rt^2+kt^3 and expand h(x+delta)-T. Its successive coefficients from t^(-1) to t^3 are

\[
\begin{split}
su+A,&\quad sv+q,\\
sw+u^2/2+Au/3+B,&\\
sr+uv+Av/3+pu+D,&\\
sk+v^2/2+(u+A/3)w-u^3/6-Au^2/9+pv-Bu/3+E.&
\end{split}
\]

Each vanishes identically with the displayed coefficients. The remaining residual is O(x^(-4/3)), since q=O(s), u=O(1/s), v=O(1), and w,r,k=O(1/s). Division by the local derivative ~s gives (2).

## 3. Practical Newton inversion and all finite orders

Starting at x_0=x, use

\[
x_{j+1}=x_j-\frac{h(x_j)-T}{h'(x_j)}.
\]

Two steps give x_2-h^(-1)(T)=O(x^(-5/3)s^(-7)), smaller than the forward uncertainty O(x^(-4/3)/s). Indeed a Newton step squares the error and multiplies it by O(1/(xs)); the initial error is O(x^(1/3)/s). More generally the j-step error is O(x^(1-2^(j+1)/3)s^(1-2^(j+1))).

One can retain log Gamma(t+1) instead of truncating Stirling, replacing p log t+Et^(-1) in the corresponding way. Higher forward orders yield higher explicit smooth models. If the log-forward error is O(n^(-rho)), the model inverse uncertainty is O(x^(-rho)/log x). An arbitrary number of Newton steps therefore makes numerical inversion error smaller than any fixed finite forward order.

These are inverse statements about an explicit model. They do not differentiate an unknown remainder of the integer sequence, and they do not impose a canonical real interpolation on combinatorial counts.

## 4. Exact discrete threshold

Define N(Y)=min{n:c_n>=Y}. The forward expansion implies eventual strict monotonicity, since log c_(n+1)-log c_n=log(4n)+O(n^(-2/3))>0.

If |log c_n-h(n)|<=K n^(-4/3) for n>=n_0, let r_*=h^(-1)(log Y). For all sufficiently large Y, a conservative radius

\[
\eta=\frac{8\max(K,1)r_*^{-4/3}}{\log(4r_*)}
\]

gives

\[
\lceil r_*-\eta\rceil\le N(Y)\le\lceil r_*+\eta\rceil.\tag{4}
\]

To prove this, evaluate the integer immediately below the lower ceiling and the integer at the upper ceiling. Near r_* the model derivative is at least half log(4r_*), while the forward error is at most twice K r_*^(-4/3). The stated displacement provides a strict margin in both directions, and monotonicity finishes the argument. The same reasoning applies to every higher finite order.

For 2eta<1, at most two adjacent integers remain possible. If dist(r_*,Z)>eta, the ceilings agree and give the exact threshold. A bare ceiling of a truncated asymptotic is not uniformly valid arbitrarily close to integer boundaries. Replacing r_* by (2) or the Newton result requires enlarging eta by its model-inversion error.

The existence of an unspecified asymptotic K proves an eventual statement, not a certified finite-Y algorithm. A numerical certificate also requires effective forward constants, a certified amplitude, and controlled evaluation errors. The fitted gamma_c=173.12670485 does not supply them.

## 5. Provenance of coarse versus fine conclusions

Even the published theta theorem already implies

\[
N(Y)\in\left[
\left\lceil x-\frac{3z}{s}x^{1/3}-\frac54-\frac{K'}{\log x}\right\rceil,
\left\lceil x-\frac{3z}{s}x^{1/3}-\frac54+\frac{K'}{\log x}\right\rceil
\right]
\]

for some constant K' and sufficiently large Y. The logarithm of its unknown multiplicative constants is O(1), which becomes O(1/log x) after inversion. Therefore that coarse localization is not new to the amplitude theorem. The new candidate forward theorem identifies the fixed amplitude term and permits the algebraic refinements in (2), together with arbitrarily narrow asymptotic discrete brackets.

Changing gamma_c to an approximation gamma_tilde changes the smooth inverse to first order by -log(gamma_tilde/gamma_c)/log(4n). A fixed bounded amplitude error tends to zero in the inverse, but still exceeds the algebraic precision claimed in (2) and can change a threshold near an integer.
