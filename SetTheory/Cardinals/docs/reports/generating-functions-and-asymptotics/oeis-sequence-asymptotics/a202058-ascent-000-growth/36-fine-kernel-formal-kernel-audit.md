# Exact frozen kernel and audit of the proposed lognormal mechanism

2 October 2026. These calculations clarify a possible sharper route. They do **not** prove a lognormal equivalent or its leading coefficient.

## 1. Exact circle kernel

Use the characteristic quantities and frozen transition ratios from the audited report. Put r=h(k)/D, r′=h(y)/D and

\[
\kappa_q(v)=\frac{q e^{-qv}}{1-e^{-q}},\quad 0\le v<1.
\]

Changing variables separately on y<s and y>s gives the exact identity

\[
\frac{g(y)\,dy}{\lambda}
 =\kappa_q((r'-r)\bmod1)\,dr'.
\]

Thus the frozen continuum Doob kernel K_q is convolution on the circle, independent of the composition z=s/D. Lebesgue measure is exactly stationary at every q, not merely asymptotically stationary. On the Fourier mode exp(2πiℓr),

\[
K_q=\frac{q}{q-2\pi i\ell}.
\]

On zero-mean periodic functions, wherever the operators are defined,

\[
(K_q-I)^{-1}=q\,\partial_r^{-1}-I.
\]

For example this identity holds in L² with the mean-zero periodic antiderivative. It also yields a bounded measurable Poisson solution for a bounded mean-zero forcing. Since λ/b=D/R, the inverse of the frozen q-time generator (D/R)(K_q−I) is

\[
\frac RD(q\partial_r^{-1}-I).
\]

A forcing of order q therefore has a rank corrector of order q²/D. Notice that the real spectral gap is of order D/q², whereas the directed rotation contributes an imaginary eigenvalue of order D/q. Using only the real gap would miss the sharper explicit Poisson inverse.

## 2. Independent residual expansion

Write V=Tψ/ψ−∂_tψ/ψ. Take D→∞ at fixed q, with 0<z=s/D<1 and r away from coincident breakpoints. Integer states approximating fixed (r,z) give the same limiting first-order residual. The statements in this section concern this continuum first-order limit, not an already-uniform joint q,D limit.

Euler–Maclaurin at the integer breakpoints gives

\[
\frac{S-\lambda}{b}
 \longrightarrow \frac q{2R}\mathbf1_{r<z}
 +\frac q2\mathbf1_{r>z}
 +\frac{R-1}{2R}\{\kappa_q((z-r)\bmod1)-\kappa_q((-r)\bmod1)\}.
\]

The final two terms are rank-boundary layers and cannot be discarded pointwise near r=z or r=1.

For r′=h(i)/D, let a be the leading D times the shifted-rank difference. The four exact child formulas give

- duplicate descent, r′<r and r′<z: a=r′
- duplicate ascent, r′≥r and r′<z: a=−(R−1)r′
- new ascent, r′≥r and r′>z: a=1−r′
- new descent, r′<r and r′>z: a=1+(R−1)r′

Consequently the shifted-rank contribution tends to

\[
-\frac qR\int_0^1\kappa_q((r'-r)\bmod1)a(r,r')\,dr'.
\]

The remaining time-derivative contribution is

\[
B=r-\frac{q e^{-q}}R
 \begin{cases}r(1-z),&r<z,\\z(1-r),&r>z.\end{cases}
\]

Away from the rank boundary layers, letting q→∞ gives the proposed leading formula

\[
V/b\sim q f(r,z),\qquad
f(r,z)=\begin{cases}1/4+r/2,&r<z,\\r/2,&r>z.\end{cases}
\]

This verifies the bulk calculation independently: the duplicate-ascent Euler–Maclaurin term is q/4 and its rank shift contributes qr/2; the new-ascent Euler–Maclaurin term q/2 combines with −q(1−r)/2.

## 3. Exact rank average of the continuum first-order limit

The rank-boundary kernels in Section 2 integrate to zero. Conditional on r′=x under stationary rank measure, the probability that r≤r′ is

\[
P_q(x)=\frac{1-e^{-qx}}{1-e^{-q}}.
\]

Set

\[
I(q)=\int_0^1xP_q(x)\,dx
=\frac{1/2-[1-(1+q)e^{-q}]/q^2}{1-e^{-q}}.
\]

Integrating the four a formulas gives

\[
\langle a\rangle=1-z+\frac{R-1}{2}
 +\frac{2-R}{2}z^2-RI(q).
\]

Also

\[
\langle B\rangle=\frac12-\frac{qe^{-q}}{2R}z(1-z).
\]

Combining all terms and using 2−R=e^(−q) gives the particularly simple exact answer

\[
\boxed{\langle V/b\rangle
 =q I(q)+\frac{q(z-1)}{2R}+\frac12.}
\]

Therefore the rank average is

\[
\frac q4(1+z)+\frac12-\frac1q+O(qe^{-q}),
\]

uniformly in z∈[0,1]. This validates the leading average q(1+z)/4 without overlooking the rank boundary layers. The exact formula still refers to the first-order D→∞ continuum limit.

## 4. Composition and the candidate scalar exponent

At R=2, every ascent increases D by one and every descent decreases D by one. In the large-q non-wrapping regime, the pointwise composition drift in q-time is

\[
Lz/b\simeq\begin{cases}-(1+z)/2,&r<z,\\(1-z)/2,&r>z.\end{cases}
\]

Its rank average is (1−3z)/2. Thus this drift formula is an **averaged** formula; it is not valid pointwise.

A trial multiplier H=exp(q²/6+qz/6) gives the leading pointwise forcing

\[
f(r,z)+\frac16\,\frac{Lz}{b}
 =\frac r2+\frac{1-z}{12}+\frac1{12}\mathbf1_{r<z}.
\]

Its rank average is exactly 1/3, independently of z. The mean-zero forcing to remove is

\[
g(r,z)=\frac r2-\frac14+\frac{\mathbf1_{r<z}-z}{12}.
\]

The Poisson identity in Section 1 supplies its frozen correction explicitly:

\[
\eta(r,z)=-\frac RD\{q^2\partial_r^{-1}g-qg\},
\]

so that (D/R)(K_q−I)η+qg=0. Its size is O(q²/D). This is a concrete reason to study a scalar exponent q²/6 rather than a numerical fit alone. Since q∼2log n at the coefficient scale, it suggests a coefficient logarithm (2/3)(log n)². That suggestion remains conditional.

## 5. A definite obstruction to a naive boundary argument

The uncorrected ψ-Doob chain started at x0=(1,1,1) does not typically grow out of the finite-state region rapidly at large q. As q→∞, x0 has r→1/3. Its new-ascent child is (2,1,2), with child rank→1/2, so

\[
\frac{\psi(2,1,2)}{\psi(1,1,1)}
 =\exp(q/3+O(1)).
\]

After dividing by b=exp(q/2+O(log q)), this jump rate in q-time is only

\[
O(qe^{-q/6}).
\]

The duplicate-descent child has an even smaller rate O(qe^(−2q/3)). Thus an ordinary typical-trajectory claim that the root chain reaches D≫q² in O(log q) q-time is false. The Feynman–Kac expectation could still be dominated by rare early growth paths rewarded by later potential, but this requires a weighted boundary argument, a different conjugation, or a carefully controlled seeding construction.

## 6. Missing estimates before a theorem

A valid proof of the candidate would need all of the following, or substitutes:

1. A uniform discrete residual expansion after rank/composition correction, including r=0, r=z, the wrap layer, and the moving q parameter
2. Uniform control of the exponentiated Poisson correction, including its finite-difference errors and transitions changing z and D
3. A weighted finite-state-to-bulk estimate whose logarithmic cost is o(Q²), for both upper and lower bounds; unweighted typical growth does not provide it
4. Control of repeated returns to the finite-state region, rather than only an initial entrance estimate
5. A coefficientwise transfer theorem or regularity result; even logF∼q²/6 would not by itself establish the same asymptotic at every single coefficient

The new audited O(log² n) coefficient upper bound and the improved coarse lower bound do not supply these missing steps. No asymptotic equivalent is established by this note.
