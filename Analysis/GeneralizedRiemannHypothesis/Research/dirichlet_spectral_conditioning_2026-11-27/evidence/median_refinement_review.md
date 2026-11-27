# Review of the Riemann / real Dirichlet half-contribution height refinement

## Verdict

The proposed refinement is correct for a **fixed** real Dirichlet character (with `q` its conductor) or for zeta (`q=1`), a fixed shape `theta>0`, and the positive nontrivial zero ordinates counted with multiplicity. Central zeros must be omitted from the gamma series and deflated in any entire-function product representation. The exact implicit centering `c_ell` must be retained in the central limit theorem. A two-block local limit theorem proves the needed moving-cutoff result directly, without requiring a functional central limit theorem or tightness of a process.

An additional valid expansion is

\[
\sigma^2=\frac{\theta}{8u^3}(\ell-1)
 +O_{\chi,\theta}\!\left(\frac{\log u}{u^4}\right).
\]

## 1. Setup and normalization

Let `gamma>0` range over the positive ordinates with multiplicity, and let independent `G_gamma` have gamma distribution with shape `theta` and rate `1`. Put

\[
 X=\sum_{\gamma>0}\frac{G_\gamma}{\gamma^2},\qquad
 S_c=\sum_{0<\gamma\le cu}\frac{G_\gamma}{\gamma^2}.
\]

The stipulated count is

\[
 N(T)=\#\{0<\gamma\le T\}
 =\frac{T}{2\pi}\left(\log\frac{qT}{2\pi}-1\right)
 +E(T),\qquad E(T)=O_\chi(\log(T+2)).\tag{1}
\]

The formula can be extended to all `T>=0` by enlarging the constant: the main term tends to zero at zero, positive zero ordinates are locally finite and bounded away from zero after central zeros are removed, and `N(0)=0`. Thus `E(0)=0`.

The series `sum gamma^-2` converges, so `X` is finite and positive almost surely. For every `0<x<E X`, there is a unique `u>0` solving

\[
 x=\theta\sum_\gamma(\gamma^2+u^2)^{-1}.
\]

Indeed the right side is continuous and strictly decreasing from `E X` to zero. Let

\[
 \sigma^2=\theta\sum_\gamma(\gamma^2+u^2)^{-2},\qquad
 \ell=\log\frac{qu}{2\pi}.
\]

All limits below mean `x` decreases to zero, equivalently `u` increases to infinity. Define the conditional law `P_x=P( . | X<=x)`. The event has positive probability for every `x>0`: choose a finite initial block whose omitted tail has small expectation, and use independence and the positive probability that the initial gamma variables are all small.

**Conductor and symmetry:** Bennett--Martin--O'Bryant--Rechnitzer define their `N(T,chi)` using **both** positive and negative ordinates, including multiplicity, in the open critical strip. For a real character conjugation symmetry gives

\[
 N_{\rm both}(T,\chi)=2N(T)+m_0,
\]

where `m_0` is the multiplicity at ordinate zero. Halving their formula and subtracting this finite term gives (1). For imprimitive real characters, the nontrivial zeros in the open strip are those of the inducing primitive character, so `q` must be the **conductor**, not the presentation modulus. For zeta the positive-ordinate Riemann--von Mangoldt formula gives (1) directly with `q=1`.

## 2. Mean estimate, including uniformity

For `f_u(T)=(T^2+u^2)^-1`, Stieltjes integration by parts gives

\[
\begin{aligned}
 m_u(c)&=\theta\int_0^{cu}f_u(T)\,dN(T)\\
 &=\frac{\theta}{2\pi u}
 \left\{\ell\arctan c+J(c)\right\}
 +\theta f_u(cu)E(cu)-\theta\int_0^{cu}f_u'(T)E(T)\,dT,\\
 J(c)&=\int_0^c\frac{\log r}{1+r^2}\,dr.
\end{aligned}\tag{2}
\]

The main integral is valid despite the logarithmic derivative at zero because `log T` is integrable there. For `c` in any fixed compact subset of `(0,infinity)`, the error in (2) is uniformly

\[
 O_{\chi,\theta}\!\left(\frac{\log u}{u^2}\right).
\]

For the integral error, substitute `T=ur` in

\[
2\int_0^{cu}\frac{T\log(T+2)}{(T^2+u^2)^2}\,dT.
\]

The same estimate is valid at `c=infinity`: the endpoint term tends to zero and both `r/(1+r^2)^2` and that weight times `log(r+2)` are integrable. The inversion `r -> 1/r` shows `J(infinity)=0`, whence

\[
 x=\frac{\theta\ell}{4u}
 +O_{\chi,\theta}\!\left(\frac{\log u}{u^2}\right).\tag{3}
\]

For the variance the identical argument with `(T^2+u^2)^-2` gives

\[
\sigma^2=\frac{\theta}{2\pi u^3}
 \left\{\ell\int_0^\infty\frac{dr}{(1+r^2)^2}
 +\int_0^\infty\frac{\log r}{(1+r^2)^2}\,dr\right\}
 +O_{\chi,\theta}\!\left(\frac{\log u}{u^4}\right).
\]

The two integrals are `pi/4` and `-pi/4`. The second identity follows by differentiating the beta integral, or by writing

\[
 (1+r^2)^{-2}=\tfrac12\frac{d}{dr}\frac{r}{1+r^2}
 +\tfrac12(1+r^2)^{-1}
\]

and integrating by parts, using `J(infinity)=0`. Hence

\[
\sigma^2=\frac{\theta(\ell-1)}{8u^3}
 +O_{\chi,\theta}\!\left(\frac{\log u}{u^4}\right)
 \sim\frac{\theta\ell}{8u^3}.\tag{4}
\]

In particular the error in (2)--(3), divided by `sigma`, is `O(sqrt(log u/u))=o(1)`, and

\[
 a_u:=u^2\sigma\longrightarrow\infty,
 \qquad \frac{\pi\sigma}{x}\sim
 \pi\sqrt{\frac{2}{\theta u\ell}}\longrightarrow0.\tag{5}
\]

The variance fraction at a cutoff is, uniformly when `c` stays in a fixed compact subset of `(0,infinity)`,

\[
\frac{\theta\sum_{\gamma\le cu}(\gamma^2+u^2)^{-2}}{\sigma^2}
 \longrightarrow V(c):=
 \frac{2}{\pi}\left(\arctan c+\frac{c}{1+c^2}\right).\tag{6}
\]

Consequently (6) also holds along **any** sequence `c_u -> c>0`.

## 3. The deterministic median correction

Let `G` denote Catalan's constant. Expanding `(1+r^2)^-1` on `(0,1)` and integrating, or using its standard integral representation, gives `J(1)=-G`.

For every `ell>0`, the equation

\[
 \ell\arctan c_\ell+J(c_\ell)=\frac{\pi\ell}{4}\tag{7}
\]

has a unique solution `c_ell>1`: the left side minus the right side is `-G` at `1`, tends to `pi ell/4>0` at infinity, and has derivative

\[
 \frac{\ell+\log c}{1+c^2}>0\qquad(c\ge1).
\]

It is also the only positive solution: on `(0,exp(-ell))` the function decreases from the negative value `-pi ell/4`, and thereafter it increases. The implicit-function theorem, or direct Taylor expansion at `1`, yields

\[
 c_\ell=1+\frac{2G}{\ell}+\frac{2G^2}{\ell^2}
 +O(\ell^{-3}).\tag{8}
\]

Thus the proposed first-order expansion is correct. Equation (7), (2), and (3) imply

\[
 m_u(c_\ell)-x/2=o(\sigma).\tag{9}
\]

**Important centering warning.** One may display (8) to explain the drift, but replacing the exact `c_ell` by `1+2G/ell` in the CLT is false. The missing term is asymptotic to `2G^2/ell^2`. After multiplication by `x/(pi sigma)`, it grows like a positive constant times `sqrt(u)/ell^(3/2)`, which tends to infinity. Centering at `1` is still less accurate. The implicit root (7) is explicit enough for the theorem and is computable by a one-dimensional monotone solve.

## 4. Moving-cutoff conditional normal limit

Here is a complete proof of the limited moving-cutoff statement needed for the median; it does not assume a process limit.

Define the Esscher law

\[
 \frac{dQ_u}{dP}=
 \frac{e^{-u^2X}}{E[e^{-u^2X}]}.
\]

Under `Q_u` the summands `Y_gamma=G_gamma/gamma^2` remain independent, and `Y_gamma` is gamma with shape `theta` and rate `lambda_gamma=gamma^2+u^2`. Thus `E_Q X=x` and `Var_Q X=sigma^2`.

Let `c_u -> 1` be any deterministic sequence and write

\[
 A_u=\frac{S_{c_u}-m_u(c_u)}{\sigma},\qquad
 C_u=\frac{X-S_{c_u}-(x-m_u(c_u))}{\sigma},\qquad
 Z_u=A_u+C_u=\frac{X-x}{\sigma}.
\]

Under `Q_u`, `A_u` and `C_u` are independent and have variance limits

\[
 v=V(1)=\frac12+\frac1\pi,\qquad 1-v.
\]

### Local limit argument

For either block the centered characteristic function is a product whose modulus is

\[
 \prod_{\gamma\text{ in block}}
 \left(1+\frac{s^2}{\sigma^2\lambda_\gamma^2}\right)^{-\theta/2}.
\]

Its logarithm has the Gaussian expansion at every fixed `s`, since

\[
 \max_\gamma(\sigma\lambda_\gamma)^{-1}
 \le (u^2\sigma)^{-1}\longrightarrow0,
\]

and the cubic Taylor remainder is bounded by a constant times this maximum times the block's normalized variance. Formula (6) therefore gives pointwise convergence to the characteristic functions of `N(0,v)` and `N(0,1-v)`.

To upgrade to a local limit theorem, use the shell `[u/4,u/2]` for the first block and `[2u,3u]` for the second. Each contains at least `kappa n_u` ordinates, counted with multiplicity, for `n_u=u ell` and some `kappa>0`, by (1). On either shell, `(sigma lambda_gamma)^-2 >= kappa'/n_u`. Hence, for constants `b,d>0` independent of `u` and of the moving cutoff sequence once it is close to `1`,

\[
 |\widehat f_u(s)|\le
 (1+b s^2/n_u)^{-d n_u}.\tag{10}
\]

For sufficiently large fixed `n_0`, the right side of (10), for `n_u>=n_0`, is bounded above by `(1+b s^2/n_0)^(-d n_0)`, an integrable function. This follows because `n log(1+b s^2/n)` increases in `n`. Dominated convergence proves convergence of characteristic functions in `L^1`. Fourier inversion gives uniformly convergent densities

\[
 f_u\longrightarrow\phi_v,\qquad
 g_u\longrightarrow\phi_{1-v},
\]

where `phi_r` is the `N(0,r)` density. Their convergence also holds in `L^1` by Scheffe's lemma. In particular these densities are uniformly bounded. No simplicity or spacing assumption on zeros is used.

### Transfer to the small-sum conditioning

The `P_x` law is the `Q_u` law weighted by `exp(a_u Z_u) 1_{Z_u<=0}` and normalized. Under `Q_u`, `(A_u,Z_u)` has density `f_u(w)g_u(z-w)`. Set `r=-a_u z>=0`. Its weighted normalization is

\[
 \frac1{a_u}\int_0^\infty e^{-r}
 \int_\mathbb R f_u(w)g_u(-r/a_u-w)\,dw\,dr
 \sim\frac1{a_u\sqrt{2\pi}}.
\]

For bounded continuous test functions the same integral calculation, using the uniform and `L^1` density convergence, proves

\[
 \left(A_u,u^2(x-X)\right)
 \ \xrightarrow[P_x]{d}\ (W,E),\tag{11}
\]

where `E` is rate-one exponential, `W` is normal with variance `v(1-v)`, and the two limits are independent. Indeed the limiting joint density is

\[
 \sqrt{2\pi}\,\phi_v(w)\phi_{1-v}(-w)e^{-r}
 =\phi_{v(1-v)}(w)e^{-r},\qquad r\ge0.
\]

The domination needed in this step is immediate from the uniform boundedness of `g_u` and the unit integral of `f_u`; the `r` tail has the integrable factor `e^-r`. Equation (11) also yields `Z_u -> 0` in `P_x` probability, since `a_u -> infinity`.

## 5. Quantile inversion and the claimed CLT

Let

\[
 H=\min\left\{\gamma>0:
 \sum_{0<\gamma'\le\gamma}Y_{\gamma'}\ge X/2\right\}.
\]

This is finite almost surely, because the increasing partial sums tend to `X>0`. Repeated ordinates cause no difficulty: all contributions at that height are included. We write `H_x` for this variable viewed under `P_x`.

Fix `h` real and define

\[
 c_u(h)=c_\ell+h\frac{\pi\sigma}{x}.
\]

By (5) this tends to `1`. With `M_u(c)=theta(ell atan(c)+J(c))/(2pi u)`,

\[
 M'_u(c_\ell)=\frac{\theta}{2\pi u}
 \frac{\ell+\log c_\ell}{1+c_\ell^2}
 \sim\frac{x}{\pi}.
\]

Taylor's theorem on a fixed neighborhood of `1`, (2), (3), and (9) give

\[
 \frac{m_u(c_u(h))-x/2}{\sigma}\longrightarrow h.\tag{12}
\]

The quadratic Taylor error is `O(x (sigma/x)^2)=o(sigma)`; the counting error is also `o(sigma)`.

The following event identity is exact, including cutoffs equal to a positive zero ordinate:

\[
 \{H_x\le u c_u(h)\}=\{S_{c_u(h)}-X/2\ge0\}.
\]

Moreover,

\[
 \frac{S_{c_u(h)}-X/2}{\sigma}
 =A_u-\tfrac12Z_u+
 \frac{m_u(c_u(h))-x/2}{\sigma}
 \ \xrightarrow[P_x]{d}\ W+h.
\]

Since the limiting normal has no atom at zero, (11)--(12) prove

\[
 \boxed{\quad
 \frac{x}{\pi\sigma}\left(\frac{H_x}{u}-c_\ell\right)
 \xrightarrow{d}
 N\!\left(0,\frac14-\frac1{\pi^2}\right).
 \quad}\tag{13}
\]

Equivalently, writing `B` for a standard Brownian bridge, the limit of the cumulative probability at `h` is `P(B(v)+h>=0)`, because `Var B(v)=v(1-v)`. The sign causes no discrepancy: the limiting variable is `-B(v)`, which has the same centered normal law as `B(v)`.

The dimensional fluctuation scale is

\[
 \frac{u\pi\sigma}{x}
 \sim\pi\sqrt{\frac{2u}{\theta\ell}}.
\]

## 6. Central zeros and the role of GRH

No term with `gamma=0` can be admitted into `X`: division by `gamma^2` is undefined, and inserting such a term would destroy the finite random-series model. For real primitive characters a central zero is not ruled out by GRH alone. Its finite multiplicity affects the zero-count remainder only by `O(1)` and hence does not change any estimate above.

If the report connects the Laplace product to a completed L-function, first remove the central factor from the completed function. For a real, even completed function of the centered variable, remove its zero at the origin, divide by the resulting nonzero value at the origin, and then pair the positive and negative zeros. The resulting product is

\[
 \prod_{\gamma>0}(1+s/\gamma^2),
\]

at imaginary displacement `sqrt(s)` in the usual real-zero coordinate, and the gamma-series Laplace transform is its `-theta` power. The probabilistic proof of (13) itself needs only the counting asymptotic (1); GRH supplies the interpretation of the completed-function zeros as this positive real spectral sequence.

## Primary / authoritative references checked

1. M. A. Bennett, G. Martin, K. O'Bryant, A. Rechnitzer, **Counting zeros of Dirichlet L-functions**, *Mathematics of Computation* 90 (2021), 1455--1482, DOI `10.1090/mcom/3599`. Definition (1.2), the immediately following definition of `N(T,chi)`, and Theorem 1.1 explicitly settle the both-sign count, multiplicities, conductor, and imprimitive-character conventions. Author-hosted PDF: <https://personal.math.ubc.ca/~bennett/BeMaObRe-MathComp-2021.pdf>. arXiv: <https://arxiv.org/abs/2005.02989>. Retrieved web references: `turn907900549view0`, `turn907900549view1`.
2. H. L. Montgomery and R. C. Vaughan, **Multiplicative Number Theory I**, Chapter 14, Corollary 14.3 and Theorem 14.5. The former gives the zeta positive count with `O(log T)` error; the latter states the positive-count convention for Dirichlet characters, including half-weight endpoint zeros. Author-hosted excerpt: <https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/18.0_pp_452_462_Zeros.pdf>. Retrieved web reference: `turn907900549view2`.

Numerical sanity checks of the calculus constants, separate from the proof: `J(1)=-0.915965594177219...`, `integral_0^infinity log(r)/(1+r^2)^2 dr=-pi/4`, `v=0.818309886183791...`, `v(1-v)=0.148678816357662...`. The algebraic/analytic arguments above establish these constants, not the numerical checks.
