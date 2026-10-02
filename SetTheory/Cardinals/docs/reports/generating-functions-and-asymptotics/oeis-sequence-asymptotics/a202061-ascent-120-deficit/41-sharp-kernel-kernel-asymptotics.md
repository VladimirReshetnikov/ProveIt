# Critical positive jump kernel: local asymptotics and exact constants

Supplementary derivation note. The release theorem needs only the exact Hessian/variance identities, local positive Gaussian lower bound, and uniform fixed-q square-root transfer. Those parts are independently reviewed. Stronger full local equivalents and amplitude statements in this note are not part of that audit boundary.

This note concerns the positive kernel in the frozen report
`oeis-a202061-report/a202061-report.tex`. It does not modify that report.
All logarithms are natural. The local estimates below are proved from the
report's exact positive binomial formula. Their use in a sharp global
coefficient asymptotic requires a separate path argument.

## 1. Constants and notation

Write z for the smallest positive root of z^3−5z^2+6z−1=0, and put

\[
\rho=3z^2-10z+2,\quad t=z^{-1},\quad
\alpha={8z^2-29z+9\over7},\quad
\kappa={17z^2-59z+13\over7}.
\]

The effective variance after fixing length and summing over the down
parameter q is

\[
v={2z^2-7z+2\over2}=0.346010735815047934813907448501\ldots.
\]

The variance at fixed q, with length summed at x=ρ, is

\[
\nu={1+2z-z^2\over2}=0.678447933946104721947199755011\ldots,
\qquad \alpha\nu=v.
\]

Define

\[
C_\ell={\sqrt{7z^2-24z+5}\over2\sqrt\pi}
=0.203637718490862197496201230446\ldots,
\quad
C_q={\sqrt{-16z^2+55z-10}\over2\sqrt\pi}
=0.145426900330507185467244782819\ldots.
\]

The covariance matrix needed before summing over q is

\[
\Sigma=\begin{pmatrix}
-(11z^2-37z+4)/7&2(5z^2-17z+2)/7\\
2(5z^2-17z+2)/7&(2z^2-7z+2)/2
\end{pmatrix}
=\begin{pmatrix}
.41382692996310429939&-.33454719680776555776\\
-.33454719680776555776&.34601073581504793481
\end{pmatrix}.
\]

It is positive definite, and

\[
\det\Sigma={864z^2-2978z+559\over98}>0.
\]

Let s=r−q, so the actual macro-height increment is d=1+s. Define

\[
\widetilde B(\ell,q,s)=\rho^\ell z^{-s}
 B(\ell,q,q+s),\qquad J_{\ell,s}=\sum_q\widetilde B(\ell,q,s).
\]

The sum is over admissible q≥1; inadmissible coefficients are zero.

## 2. Strong uniform local theorem

Fix C>0 and K>3. As the external parameter n tends to infinity, uniformly
for integers ℓ≥(log n)^K and

\[
|q-\alpha\ell|+|s|\le C\sqrt{\ell\log n},
\]

one has

\[
\widetilde B(\ell,q,s)=
{C_\ell\over2\pi\sqrt{\det\Sigma}}\ell^{-5/2}
\exp\left[-{1\over2\ell}
\begin{pmatrix}q-\alpha\ell&s\end{pmatrix}
\Sigma^{-1}
\binom{q-\alpha\ell}{s}\right](1+o(1)). \tag{2.1}
\]

Here C_ℓ is the constant defined above, not a function of the integer ℓ.
The o(1) is uniform. In particular the cubic Taylor contribution to its
logarithm is O((log n)^{3/2}/sqrt(ℓ)), which tends to zero under K>3.
The ordinary one-parameter statement follows with log n replaced by
log ℓ and no external minimum-length condition.

Summing over q gives the strong uniform statement

\[
J_{\ell,s}={C_\ell\over\sqrt{2\pi v}}\ell^{-2}
\exp[-s^2/(2v\ell)](1+o(1)),
\quad |s|\le C\sqrt{\ell\log n}. \tag{2.2}
\]

The numerical constant C_ℓ/sqrt(2πv) is
0.138109483615507449708749623915… .

The same equivalent holds if the q sum is restricted to

\[
|q-\alpha\ell|\le C'\sqrt{\ell\log n}
\]

for any fixed C'>|Σ_qs| C/v. One may enlarge C' slightly if the bound on
s is formulated with |q−αℓ|+|s| rather than just |s|. The conditional center
and variance of q are

\[
q=\alpha\ell+{\Sigma_{qs}\over v}s+O(\sqrt\ell),\qquad
\operatorname{Var}(q\mid\ell,s)\sim
{\det\Sigma\over v}\ell,
\]

with

\[
{\Sigma_{qs}\over v}=-{4(z-3)(2z-1)\over7},\qquad
{\det\Sigma\over v}=-{213z^2-731z+132\over49}>0.
\]

It is important to allow this shifted q saddle. If q is fixed within O(1)
of αℓ, the height variance in (2.1) is instead

\[
v_{\rm fixed\ q}={\det\Sigma\over\Sigma_{qq}}
={398z^2-1413z+278\over182},
\]

which is strictly smaller than v. A construction fixing q=round(αℓ)
therefore does not recover the optimal kinetic coefficient.

### Proof directly from the positive binomial formula

Denote the summand of the report's block formula by T(ℓ,j,r,k). Uniform
Stirling expansion, with a=j/ℓ, b=r/ℓ and u=k/ℓ in a compact interior set,
gives

\[
T(\ell,j,r,k)=\ell^{-3}A(a,b,u)e^{\ell S(a,b,u)}(1+O(\ell^{-1})),
\]

where S is the report's entropy and

\[
A(a,b,u)=
{\sqrt{a(1-b-u)(a+b+u)}\over
(2\pi)^2u^2\sqrt{(b-u)(a-b+u)}(1+a)^{3/2}}. \tag{2.3}
\]

There are no unspecified powers hidden in A. The factor ℓ^−3 consists
of four binomial square-root factors and one extra factor ℓ^−1 in the
Catalan-type coefficient.

For fixed a,b, the k saddle is unique because

\[
S_{uu}=\frac2{a+u}-\frac2u-\frac1{b-u}
-\frac1{a-b+u}-\frac1{1-b-u}-\frac1{a+b+u}<0. \tag{2.4}
\]

At the critical point it is u=κ. Also

\[
e^{S_a}={(a+u)^2(1+a)\over a(a-b+u)(a+b+u)}>1, \tag{2.5}
\]

since numerator minus denominator equals (a+u)^2+a b^2>0. Thus j has
an endpoint maximum at q. At the critical point e^{−S_a}=z; summing
j=q,q−1,… contributes (1−z)^−1, with uniform relative error o(1).

For a fully elementary global-tail justification, S is a sum of three
concave binomial entropies:

\[
2\{L(a+u)-L(a)-L(u)\}
+\{L(a)-L(b-u)-L(a-b+u)\}
+\{L(1+a)-L(1-b-u)-L(a+b+u)\}.
\]

Its Hessian is negative definite in the interior. Indeed equality in the
first two concavity forms forces da/a=db/b=du/u, and equality in the last
then forces all three to vanish. Consequently the critical point is the
unique global maximum on the relevant affine constraints, and away from
a fixed neighborhood the exponentially smaller terms are uniform. The
same argument, compactness, and (2.5) control the j endpoint globally.
Polynomially many boundary terms do not affect these estimates.

Set w=b−a and take the Hessian H of S(a,a+w,u) at (α,0,κ).
The upper-left 2×2 block of (−H)^−1 is exactly Σ. Summing the lattice
Gaussian in k supplies a factor sqrt(ℓ). Thus ℓ^−3 becomes ℓ^−5/2.
Taylor expansion has linear part s log z and cubic remainder

\[
O\left({(|q-\alpha\ell|+|s|+|k-\kappa\ell|)^3\over\ell^2}\right).
\]

Retain k in a Gaussian window around its shifted saddle, of width
sqrt(ℓ)(log n)^a for any 0<a<1/2; Gaussian tails outside a slowly growing
window are negligible. All retained displacements remain
O(sqrt(ℓ log n)), giving the claimed uniform o(1). Endpoint j tails are
geometric and may similarly be truncated at O(log n). The leading
constant from (2.3) is

\[
{A(\alpha,\alpha,\kappa)\over1-z}
\sqrt{2\pi\over-S_{uu}(\alpha,\alpha,\kappa)}
={C_\ell\over2\pi\sqrt{\det\Sigma}}.
\]

This identity and the Hessian calculation are checked exactly in the
companion SymPy script. Completing the square in q and summing its
lattice Gaussian proves (2.2), and gives the shifted center displayed
above. Strict concavity handles the remaining tails.

## 3. Actual macro-step length and increment

Let K_{L,d} be the unrestricted coefficient of macro-length L and height
increment d, after applying the critical length and height tilt:

\[
K_{L,d}=\rho^L t^d\sum_{q\ge1}
[x^L t_0^{q+d-1}]\frac{x}{1-x}Q_q(x,t_0).
\]

The dummy t_0 in coefficient extraction is independent of the fixed
critical t. Convolution in the leading geometric factor gives

\[
K_{L,d}={\rho\over(1-\rho)z}
{C_\ell\over\sqrt{2\pi v}}L^{-2}
 e^{-d^2/(2vL)}(1+o(1)), \tag{3.1}
\]

under the same moderate-deviation conditions. Replacing d−1 by d changes
the exponent by o(1). Keeping only the leading x in x/(1−x) is sufficient
for a lower bound, and changes the leading constant to
(ρ/z)C_ℓ/sqrt(2πv). Restrictions to the shifted q window remain valid.

The length marginal of (3.1) is a constant times L^−3/2. Thus after a
height window of width sqrt(L) and a length window of width comparable
to L up to logarithms have been summed, the per-step polynomial loss is
L^−1/2, up to logarithms. A fixed (L,d) kernel's L^−2 must not be used as
the per-step entropy cost after these integrations.

## 4. Fixed-q transfer and the sharp cutoff derivative

Use the discriminant

\[
\Delta(x,z_0,t_0)=
[(1-x)(z_0-(1-x))+xt_0(x-z_0)]^2
-4xt_0(1-z_0)(1-x)z_0.
\]

Let z_c(x,t_0) be its smallest positive z_0 root, continued analytically
near (ρ,t). The square-root branch of Q yields, uniformly in that
neighborhood,

\[
Q_q(x,t_0)=C_q(x,t_0)z_c(x,t_0)^{-q}q^{-3/2}
(1+O(q^{-1})),
\]

where

\[
C_q(x,t_0)=
{\sqrt{-z_c\Delta_{z_0}(x,z_c,t_0)}
 \over4\sqrt\pi\,xt_0(1-z_c)}.
\]

At the critical point the derivatives are

\[
-\partial_{\log x}\log z_c=\alpha^{-1},\qquad
-\partial_{\log t_0}\log z_c=1,\qquad
-\partial^2_{\log t_0}\log z_c=\nu. \tag{4.1}
\]

Consequently, for ε=log(x/ρ)=O(log H/H) and q~H,

\[
Q_q(x,t)z^q=C_q q^{-3/2}
\exp\{q\epsilon/\alpha+O(q\epsilon^2)+o(1)\}. \tag{4.2}
\]

The distribution of r, with probability proportional to
[t_0^r]Q_q(x,t_0)t^r, has

\[
E r=q[1+O(\epsilon)]+O(1),\qquad
\operatorname{Var}(r)=q[\nu+O(\epsilon)]+O(1).
\]

It obeys a uniform lattice local CLT on any fixed sqrt(q) window, with
the Gaussian centered at q(−∂_{log t_0}log z_c). In particular its
height increment 1+r−q has drift O(log H) when q~H, negligible relative
to sqrt(H). Any inward half-window of width c sqrt(H), c>0, retains a
fixed positive proportion of the mass, uniformly at both boundaries of
a height strip whose width is much larger than sqrt(H).

For completeness, aperiodicity and the Fourier tail estimate can be
seen without an abstract quasi-powers theorem. The fixed-gap formula
has W_j(x,t_0)=((1+β)/(1-x))^j F_j(η), with β=xt_0/(1-x), η=x²t_0/(1-x)²
and F_j having nonnegative coefficients. On t_0=t e^{iθ}, away from
θ=0 mod 2π, the ratio |1+βe^{iθ}|/(1+β) is strictly below one. Terms
j≥q/2 therefore contract exponentially; terms j<q/2 are already
exponentially smaller by the uniform z_c<1 transfer estimate. This
proves the Fourier tail bound. The small arc follows by differentiating
the analytic singularity and the amplitude, proving the local CLT.

These estimates rigorously supply the analytic input for the cutoff
claim log(ρ_H/ρ)~(α/2)(log H)/H. For the lower-row argument, choosing a
strip [H−H^γ,H] and q in [H−2H^γ,H−H^γ] ensures q≤h for every starting
height; (4.2) supplies the mass, and the inward half-Gaussian supplies a
uniform positive fraction of legal destinations in the strip.

## 5. Variational consequence and candidate sharp constant

At leading scale, an available length is L≤h/α, while integrating the
length and height windows leaves ½ log L per step. Saturating available
length therefore gives a local killing rate α log h/(2h). The moderate
deviation cost is (height velocity)^2/(2v) per unit total length.

With H_n=n^{2/3}(log n)^{1/3}, Φ(n)=H_n²/n and h(nt)=H_n y(t), the
candidate continuum action for a returning excursion is

\[
\mathcal I[y]=\int_0^1\left\{{y'(t)^2\over2v}
+{\alpha\over3y(t)}\right\}\,dt,
\quad y(0)=y(1)=0,\quad y>0\text{ on }(0,1). \tag{5.1}
\]

Its minimum is

\[
C_* =\left({3\pi^2\alpha^2\over2v}\right)^{1/3}
=2.23262530761284492217976470053\ldots.
\]

One convenient parametrization of the minimizer is

\[
y=Y\sin^2\theta,\qquad
 t={\theta-\sin\theta\cos\theta\over\pi},\quad 0\le\theta\le\pi,
\qquad Y^3={2v\alpha\over3\pi^2}.
\]

This has y~constant·t^{2/3} near either endpoint. In macro-index time,
it is simply a sine-square height profile.

The local results establish the exact inputs and their uniformity;
they do not alone prove a matching global path upper bound or convergence
of the normalized deficit. A legal near-minimizing discrete construction
can use (2.2) to obtain the corresponding limsup bound, provided its
endpoint repair, exact-length conditioning and legality estimates are
proved separately.

## 6. Reproduction

Run `python derive_constants.py` in this directory. It reduces all
identities modulo z^3−5z²+6z−1, differentiates the exact discriminant,
independently computes the entropy Hessian, and checks the Stirling
amplitude. Decimal numbers are evaluations of exact algebraic formulas,
not fits to sequence coefficients.
