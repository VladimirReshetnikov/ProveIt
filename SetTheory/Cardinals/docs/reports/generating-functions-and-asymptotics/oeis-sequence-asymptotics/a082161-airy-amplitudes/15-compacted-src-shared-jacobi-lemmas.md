# Shared relaxed Jacobi lemmas, with proofs

This self-contained dependency is copied verbatim from Sections 2–5 of the independently approved relaxed-DAG proof. It includes more scalar convergence material than the compacted proof needs, but contains every contraction, gap, profile and projection estimate used there. The relaxed source itself is unchanged.

Source SHA-256: 753f84914e7c28fff56b093c7b37dc9674067b21954cdd7aa2f4400376630c4c

The largest Airy zero is z; a=2^(-1/3)z; F(x)=Ai(z+2^(1/3)x). Initial counting recurrence: r_(n,m)=r_(n,m-1)+(m+1)r_(n-1,m), r_(n,0)=1 and r_(n,m)=0 for m>n.

## 2. Exact recurrence and contractive symmetrization

Put

\[
d_{N,j}=\frac{r_{(N+j)/2,(N-j)/2}}{((N+j)/2)!}
\]

when `0≤j≤N` and `j≡N mod 2`, and zero otherwise. Direct substitution gives

\[
d_{0,j}=\mathbf 1_{j=0},\qquad d_{N,-1}=0,
\qquad
d_{N,j}=\frac{N-j+2}{N+j}d_{N-1,j-1}+d_{N-1,j+1}.
\tag{4}
\]

In particular `a_n=n!d_{2n,0}`. Values outside the admissible support are interpreted as zero.

For `N≥1`, define on `0≤j≤N+1`

\[
D_N(j)^2=\frac{\Gamma(N+2)\Gamma(N+1)}
{\Gamma(N-j+2)\Gamma(N+j+1)},\qquad D_N(0)=1,
\]

and `v_N(j)=d_{N,j}/D_N(j)`. All vectors are padded with zeros in `ℓ²(Z_{≥0})`. Define `S_N` to be the symmetric Jacobi matrix on `0,…,N+1`, padded by zero, with edge weights

\[
b_{N,j}=\sqrt{\frac{N-j+2}{N+j}},\quad 1\le j\le N+1,
\]

and define a diagonal contraction by

\[
Q_N(j)=\sqrt{1-\frac{j(j-1)}{N(N+1)}}
\quad(0\le j\le N+1),\qquad Q_N(j)=0\quad(j>N+1).
\]

The factorial identities

\[
\frac{D_N(j)}{D_N(j-1)}=b_{N,j},\qquad
\frac{D_{N-1}(j)}{D_N(j)}=Q_N(j)
\]

on the support where the second ratio is needed establish the exact identity

\[
v_N=S_NQ_Nv_{N-1}.
\tag{5}
\]

Both `b` and `Q` lie in `[0,1]`. If `J` denotes the half-line adjacency matrix, then `0≤S_NQ_N≤J` entrywise. If `λ_N` is the largest eigenvalue of `S_N`, then `‖S_NQ_N‖≤λ_N`. The finite Jacobi matrix is irreducible, so its top eigenvector `ψ_N` can be taken positive and of norm one. Its spectrum is symmetric about zero because it exchanges the two parity subspaces. In particular its operator norm is `λ_N`.

## 3. The coarse Airy limit and a uniform spectral gap

Write `ε=N^{-1/3}` and `x_j=(j+1)ε`. The quadratic form is exactly

\[
\begin{aligned}
\langle v,(2I-S_N)v\rangle={}&
\sum_{j=0}^{N}b_{N,j+1}|v_{j+1}-v_j|^2+|v_0|^2\\
&+\sum_{j=1}^{N}(2-b_{N,j}-b_{N,j+1})|v_j|^2
+(2-b_{N,N+1})|v_{N+1}|^2.
\end{aligned}
\tag{6}
\]

Here `|v_0|²` is the first Dirichlet-gradient interval, with fictitious value `v_{−1}=0`; no nonphysical edge coefficient `b_{N,0}` is introduced.

For `1≤j≤N+1`,

\[
1-b_{N,j}
=\frac{2(j-1)}{(N+j)(1+b_{N,j})}
\ge\frac{j-1}{N+j}.
\]

It follows from (6) that, for universal positive constants `c,C`,

\[
\varepsilon^{-2}\langle v,(2I-S_N)v\rangle
\ge c\sum_{j=0}^{N+1}x_j|v_j|^2-C\varepsilon\|v\|^2.
\tag{7}
\]

On each fixed `x` window the edge weights tend uniformly to one, and

\[
\varepsilon^{-2}(2-b_{N,j}-b_{N,j+1})\longrightarrow 2x_j
\]

uniformly there. Interpolate linearly with value `ε^{-1/2}v_j` at `x_j` and zero at zero. The gradient terms in (6) give local `H¹` bounds for any sequence with bounded scaled energy. Equation (7) gives uniformly small `L²` tails outside a large fixed window. Local compactness, followed by this tail bound, gives strong `L²` compactness. The boundary interval enforces the trace zero at zero. The resulting liminf form is

\[
\int_0^\infty (|f'(x)|^2+2x|f(x)|^2)\,dx.
\]

For completeness, convergence of norms in this interpolation follows first on a fixed window from the local gradient bound and the Riemann-sum identity, and then globally by (7). Sampling smooth compactly supported functions with zero boundary value gives the reverse, limsup bound. Applying the elementary min–max principle in both directions therefore gives convergence of each fixed low eigenvalue of `ε^{-2}(2I−S_N)` to that of

\[
\mathcal H=-\frac{d^2}{dx^2}+2x,
\qquad f(0)=0.
\]

The latter eigenvalues are `μ_k=−2^{2/3}z_k`, where `z_1=z>z_2>…` are the negative Airy zeros. Thus, if `λ_{2,N}` is the second-largest positive eigenvalue for large `N`,

\[
\lambda_N=2+2a\varepsilon^2+o(\varepsilon^2),\qquad
\lambda_N-\lambda_{2,N}
\sim 2^{2/3}(z-z_2)\varepsilon^2.
\tag{8}
\]

As a map between opposite parity subspaces, `S_N` has singular values equal to its positive eigenvalues (and possibly additional zeros). Hence, after deleting its top singular direction, its norm divided by `λ_N` is at most `1−cN^{-2/3}` for all sufficiently large `N`. This parity formulation is essential: the negative eigenvalue `−λ_N` is not a second slow direction within the occupied parity space.

## 4. A finite quasimode supplies all quantitative estimates needed initially

The Airy equation reads `F''=2(x+a)F`. Define

\[
\begin{aligned}
F_2(x)&=\frac{2(-a+2x)}{15}F(x)
+\frac{x(2a+x)}{15}F'(x),\\
F_3(x)&=\frac{F(x)-xF'(x)}{3},\\
f_N(x)&=F(x)+\varepsilon^2F_2(x)+\varepsilon^3F_3(x),\\
\widehat\lambda_N&=2+2a\varepsilon^2+3\varepsilon^3
+\frac{13a^2}{15}\varepsilon^4+\frac{5a}{3}\varepsilon^5.
\end{aligned}
\tag{9}
\]

Choose a fixed smooth cutoff `χ`, equal to one on `[0,1]` and zero on `[2,∞)`, and sample `χ(j/N^{1/2})f_N(x_j)`. Let `\widehat f_N` denote its `ℓ²` normalization. Changing or omitting the cutoff in local calculations produces an error smaller than every inverse power of `N`.

Here is an explicit way to check and bound the quasimode residual. At a sample point the two edge coefficients are

\[
b_-(x,\varepsilon)=\sqrt{\frac{1-x\varepsilon^2+3\varepsilon^3}
{1+x\varepsilon^2-\varepsilon^3}},\qquad
b_+(x,\varepsilon)=\sqrt{\frac{1-x\varepsilon^2+2\varepsilon^3}
{1+x\varepsilon^2}}.
\]

Expand `b_- f_N(x−ε)+b_+ f_N(x+ε)−\widehatλ_N f_N(x)` through degree five in `ε`, reducing every derivative using `F''=2(x+a)F`. Every coefficient vanishes. At the left boundary the omitted sample is zero because `F(0)=F_2(0)=F_3(0)=0`. On the support of the cutoff, `xε²=O(N^{-1/2})`; Taylor remainders are bounded by `Cε⁶` times a fixed polynomial in `x` multiplying Airy decay. All such polynomial–Airy envelopes are square-integrable. Derivatives of the cutoff contribute only `exp(−cN^{1/4})` times a power of `N`. Since the unnormalized sampled norm is asymptotic to `ε^{-1/2}‖F‖_{L²}`, this proves

\[
\|(S_N-\widehat\lambda_N)\widehat f_N\|=O(\varepsilon^6).
\tag{10}
\]

The Airy gap (8) identifies the nearby eigenvalue with `λ_N`; projecting the residual on the complement of `ψ_N` then gives

\[
\lambda_N=\widehat\lambda_N+O(\varepsilon^6),\qquad
\|\psi_N-\widehat f_N\|=O(\varepsilon^4).
\tag{11}
\]

The sign is fixed by the positive leading Airy profile. Several useful consequences follow without a separate quantitative localization theorem:

\[
\begin{aligned}
\|\psi_N-\psi_{N-1}\|&=O(N^{-1}),\\
\|(I-Q_N)\psi_N\|&=O(N^{-4/3}),\\
\psi_N(0)&=\sqrt2\,N^{-1/2}(1+O(N^{-1/3})).
\end{aligned}
\tag{12}
\]

For the first, the explicitly normalized samples in (9) have `ℓ²` derivative `O(N^{-1})` with respect to continuous `N`; the two approximation errors in (11) are smaller. For the second, use `1−√(1−t)≤t` for `0≤t≤1`, the finite polynomial moments of the sampled Airy profile, and (11). For the endpoint, the pointwise error is at most the `ℓ²` error, and

\[
I:=\int_0^\infty F(x)^2\,dx=2^{-1/3}\operatorname{Ai}'(z)^2,
\qquad \frac{F'(0)}{\sqrt I}=\sqrt2.
\]

A Riemann-sum estimate with an integrable derivative gives a relative `O(ε)` normalization error; the endpoint Taylor error is `O(ε²)` and the normalized quasimode error divided by the leading endpoint is `O(ε^{5/2})`. These identities therefore verify the quantitative endpoint estimate in (12). Standard Airy decay needed above follows, for example, directly from the decaying solution of the Airy ODE; only its polynomially weighted integrability and exponential tail are used.

## 5. Convergence of the scalar amplitude

Set

\[
P_N=\prod_{i=1}^N\lambda_i,\qquad
u_N=v_N/P_N,\qquad M_N=S_NQ_N/\lambda_N.
\]

Then `u_N=M_Nu_{N−1}`, `‖M_N‖≤1`, and `‖u_N‖≤1`. Let `E_p` be projection onto height parity `p`. The positive eigenvector has equal squared mass on the two parities: this follows by taking the scalar product of each half of `S_Nψ_N=λ_Nψ_N` with that half. Therefore

\[
g_N=\sqrt2 E_{N\bmod2}\psi_N,\qquad
h_N=\sqrt2 E_{(N-1)\bmod2}\psi_N
\]

are unit vectors, with `S_Nh_N=λ_Ng_N`. By (12),

\[
\|h_N-g_{N-1}\|=O(N^{-1}),\qquad
\|(I-Q_N)h_N\|+\|(I-Q_N)g_{N-1}\|=O(N^{-4/3}).
\tag{13}
\]

The second estimate for `g_{N−1}` uses the first estimate only for its approximation by explicit Airy samples, rather than the crude `O(N^{-1})` difference: direct use of (11) at `N−1` gives the stated `O(N^{-4/3})` estimate with `Q_N`. It also follows by observing that `Q_N≥Q_{N−1}` pointwise on the old support and treating its negligible eigenvector tail.

Decompose

\[
u_N=A_Ng_N+w_N,\qquad w_N\perp g_N.
\]

Write `Π_N=I−|g_N⟩⟨g_N|` on the occupied parity subspace. The singular gap from §3 gives, for every vector `y` on the preceding parity,

\[
\|\Pi_NM_Ny\|
\le (1-cN^{-2/3})\|Q_Ny\|
\le (1-cN^{-2/3})\|y\|.
\tag{14}
\]

Indeed `Π_NS_N=S_N(I−|h_N⟩⟨h_N|)` on that parity; this projection removes the top singular direction, regardless of whether `y` is perpendicular to `h_N`. Also, (13) implies

\[
\|M_Ng_{N-1}-g_N\|=O(N^{-1}).
\]

Applying (14) to `w_{N−1}` and the latter estimate to the scalar term yields

\[
\|w_N\|\le (1-cN^{-2/3})\|w_{N-1}\|+CN^{-1}.
\tag{15}
\]

Iteration gives `‖w_N‖=O(N^{-1/3})`. One general estimate used here and later is

\[
\sum_{k=N_0}^N k^{-r}
\prod_{i=k+1}^N(1-ci^{-2/3})=O_r(N^{2/3-r}).
\tag{16}
\]

To prove it, split at `N/2`. The earlier half is exponentially small in `N^{1/3}` times a polynomial; on the later half bound the product by `exp(−c'(N−k)N^{-2/3})` and sum a geometric series. A finite initial segment makes no difference.

The scalar equation is

\[
A_N=t_NA_{N-1}+\langle k_N,w_{N-1}\rangle,
\quad
t_N=\langle Q_Nh_N,g_{N-1}\rangle,
\quad k_N=Q_Nh_N-g_{N-1}.
\tag{17}
\]

The unit-vector identity `⟨h,g⟩=1−‖h−g‖²/2` and (13) show

\[
t_N=1+O(N^{-4/3}),\qquad \|k_N\|=O(N^{-1}).
\tag{18}
\]

Since `|A_N|≤1`, (15), (17), and (18) give

\[
A_N-A_{N-1}=O(N^{-4/3}).
\]

Thus

\[
A_N=A_\infty+O(N^{-1/3}).
\tag{19}
\]

Positivity gives `A_N≥0` and hence `A_∞≥0`; strict positivity is established in §7.


## Scalar eigenvalue product

The finite eigenvalue expansion in (11) gives log lambda_N=log 2+aN^(-2/3)+(3/2)N^(-1)+O(N^(-4/3)). Summing it yields P_N=kappa 2^N exp(3aN^(1/3))N^(3/2)(1+O(N^(-1/3))), where kappa>0. This follows by the usual integral/Euler summation for the first two powers and absolute convergence of the residual series.
