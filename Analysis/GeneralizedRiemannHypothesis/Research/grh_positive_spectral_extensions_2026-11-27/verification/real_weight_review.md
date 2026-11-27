# Independent review: one real positive prime weight

Reviewed 2026-11-27. This review concerns the candidate developed with the `article_research` agent. The analytic proof, coding mechanism, reflection inversion, and prime-square correction check out. No substantive mathematical gap was found in the version specified below. Qualifications about exact recovery and novelty are essential.

## Candidate and verdict

Enumerate all pairs `(chi_j,a_j)` where chi_j is primitive and nonprincipal and a_j belongs to `{0,1,sqrt(2)}`. Let q_j be the conductor and w_j=q_j+1. Choose positive computable coefficients c_j by the Article's multiquadratic prefix code, with the total budget reduced so that `sum c_j w_j <= 1/8`. Put

\[
 W(n)=1+2\sum_{j\ge1}c_j\Re\{\chi_j(n)n^{-ia_j}\}.
\]

Then `3/4 <= W(n) <= 5/4`, and W is real and uniformly computable as a function of n to a requested precision. The coefficient construction depends only on the enumeration, conductors, and distinct rational primes, never on any zero.

Define

\[
 S(x)=\sum_{n\le x}\Lambda(n)W(n)(1-n/x),\qquad
 F(t)=e^{-t/2}\{S(e^t)-e^t/2\}.
\]

Under Dirichlet GRH, the real autocorrelation of this one signal determines all labelled, oriented nontrivial Dirichlet zero multisets, including every multiplicity. No simplicity, linear independence of ordinates, disjointness of spectra, or noncollision of shifted spectra is needed. This answers the explicitly stated real-nonnegative-weight question in the supplied Article, using second-order correlation alone.

The full exact limiting function is the datum. This is not a stable finite-precision reconstruction algorithm or a uniform sample-complexity result.

## 1. Shifted explicit formula and conductor uniformity

For a primitive nonprincipal chi of conductor q and |a|<=sqrt(2), use the Mellin integral

\[
 \sum_{n\le x}\Lambda(n)\chi(n)n^{-ia}(1-n/x)
 =\frac{1}{2\pi i}\int_{(2)}-\frac{L'}L(s+ia,\chi)
       \frac{x^s}{s(s+1)}\,ds.
\]

Under GRH, shifting to Re(s)=1/4 crosses precisely the nontrivial zeros, at `s=1/2+i(gamma-a)`. It crosses neither the kernel poles at 0,-1 nor any trivial zero; there is no principal L-pole since chi is nonprincipal. Consequently

\[
 S_{\chi,a}(x)
 =-\sum_\gamma\frac{m_\chi(\gamma)x^{1/2+i(\gamma-a)}}
 {(1/2+i(\gamma-a))(3/2+i(\gamma-a))}
 +O\bigl(x^{1/4}\log(q+2)\bigr),
\]

with a uniform constant for all q and this compact range of a. The baseline zeta term contributes x/2 and its usual zero sum.

Here is a direct justification of the crucial uniform bound, avoiding an unproved conductor-dependent error. For the completed entire function Xi, Hadamard logarithmic derivatives give

\[
 \frac{\Xi'}\Xi(s)-\frac{\Xi'}\Xi(2+iv)
 =\sum_\rho\left(\frac1{s-\rho}-\frac1{2+iv-\rho}\right).
\]

The functional equation on the critical line and GRH yield

\[
 \Re\frac{\Xi'}\Xi(2+iv)
 =\sum_\gamma\frac{3/2}{(3/2)^2+(v-\gamma)^2}
 \ll\log(q(|v|+2)).
\]

The Euler series at Re=2, gamma factor, and conductor term justify the final estimate. For `s=1/4+iv`, every difference summand is bounded by an absolute constant times `(1+(v-gamma)^2)^(-1)`, so the full complex logarithmic derivative is also `O(log(q(|v|+2)))`. Removing the gamma and elementary factors gives the same estimate for L'/L. On the shifted contour `v=Im(s)+a`, the compact shift only changes an absolute constant. Integration against `1/|s(s+1)|` is therefore `O(log(q+2))`.

The same Poisson estimate gives the local zero count and

\[
 \sum_\gamma\frac{m_\chi(\gamma)}{1+(\gamma-a)^2}
 \ll\log(q+2)
\]

uniformly in the shift. Horizontal contours can be chosen outside intervals of radius a constant divided by `log(q(T+2))` around the shifted ordinates; their logarithmic derivative bound is `O(log^2(q(T+2)))`, so their contribution tends to zero. This contour choice may depend on chi, which causes no issue: first prove each individual formula, then sum the final uniform bounds.

Since `sum c_j log(q_j+2) < infinity`, both the shifted zero sums and the remainders can be summed over all characters. This is stronger than a merely pointwise explicit formula and is the necessary justification for the countable aggregate.

## 2. The reflection signs and the factor of two

Let

\[
 D(\lambda)=(1/2+i\lambda)(3/2+i\lambda).
\]

The first half of `2 Re(chi(n)n^(-ia))` has a zero frequency gamma-a. The conjugate half has a zero frequency gamma+a for the conjugate character. Complex conjugation gives

\[
 m_{\bar\chi}(u)=m_\chi(-u).
\]

Therefore at frequency lambda the two contributions are precisely

\[
 m_\chi(\lambda+a)+m_\chi(a-\lambda),
\]

not `m_chi(lambda-a)+m_chi(lambda+a)`. The proposed formula uses the correct reflected second argument. In particular, with

\[
 A_\lambda=m_\zeta(\lambda)+\sum_{j\ge1}c_j
 [m_{\chi_j}(a_j+\lambda)+m_{\chi_j}(a_j-\lambda)],
\]

we have A_lambda>=0, A_-lambda=A_lambda, and

\[
 F(t)=G(t)+O(e^{-t/4}),\qquad
 G(t)=-\sum_\lambda\frac{A_\lambda}{D(\lambda)}e^{i\lambda t}.
\]

The sum of the absolute values of these coefficients is finite. The frequency union over all characters can have accumulation points; local finiteness of that union is not assumed or required. Absolute summability justifies regrouping all collisions and taking means.

## 3. Autocorrelation and algebraic decoding

If

\[
 C(h)=\lim_{T\to\infty}\frac1T\int_0^T F(t+h)F(t)\,dt,
\]

then

\[
 C(h)=\sum_\lambda\frac{A_\lambda^2}{|D(\lambda)|^2}e^{i\lambda h}.
\]

The coefficients are even, so C is real and even. For every real lambda, including points outside the frequency set,

\[
 P(\lambda)=\lim_{U\to\infty}\frac1U\int_0^U C(h)e^{-i\lambda h}\,dh
 =\frac{A_\lambda^2}{|D(\lambda)|^2}.
\]

Termwise averaging is valid by the absolutely summable double series. Positivity recovers A_lambda as `|D(lambda)| sqrt(P(lambda))`, with no phase or sign ambiguity. This is the reason ordinary autocorrelation, despite being even, suffices once several tagged spectral centers are present.

For the prefix code, the digit in coordinate j is the sum of two multiplicities. The local zero bound implies

\[
 m_{\chi_j}(a_j+\lambda)+m_{\chi_j}(a_j-\lambda)
 \le H_\lambda(q_j+1)
\]

for a uniform integer H_lambda of size `O(1+log(|lambda|+4))`. The factor of two merely changes that universal constant. The Article's prefix separation therefore applies unchanged after the coefficient budget is reduced.

More explicitly, `c_0=1`, `w_0=2`, `c_j=2^(-k_j)sqrt(p_j)`, and `D_n=2^(max_{j<=n} k_j)`. For integers `|u_j|<=(n+1)w_j`, the nonzero algebraic integer `D_n sum_{j<=n} c_j u_j` has conjugates at most `(17/8)D_n(n+1)<3D_n(n+1)`. Its nonzero integral norm gives the same lower bound

\[
 d_n=D_n^{-1}(3D_n(n+1))^{-(2^n-1)}.
\]

The reduced tail is no larger than in the Article. Thus coincident ordinates across infinitely many characters do not make labels ambiguous.

## 4. Three-center reconstruction

For one fixed chi, write m(t)=m_chi(t), and let the decoded data be

\[
 S_a(t)=m(a+t)+m(a-t),\qquad a\in\{0,1,\sqrt2\}.
\]

The identity

\[
 D_a(t):=S_a(t+a)-S_0(t)=m(t+2a)-m(t)
\]

is correct. If p_k,q_k are positive Pell integers with

\[
 u_k=2(q_k\sqrt2-p_k)\ne0,\qquad u_k\to0,
\]

then all the quantities in the finite telescoping identity

\[
 \begin{split}
 m(t+u_k)-m(t)
 &=\sum_{r=0}^{q_k-1}D_{\sqrt2}(t+2r\sqrt2)\\
 &\quad-\sum_{r=1}^{p_k}D_1(t+2q_k\sqrt2-2r)
 \end{split}
\]

are known except the two endpoint multiplicities. Local finiteness of the individual zero spectrum implies `S_0(t+u_k)=0` for every sufficiently large k: both t+u_k and -t-u_k eventually lie in punctured neighborhoods without atoms. Positivity then implies m(t+u_k)=0. The negative of the displayed finite sum equals m(t) for every sufficiently large k.

This proves exact recovery at every real t. An equivalent uniqueness proof observes that the difference of two compatible multiplicity functions is odd under reflection in all three centers and therefore periodic under both 2 and 2sqrt(2). A nonzero atom would have a dense translation orbit, contradicting local finiteness.

With an exact symmetrization oracle one may test `S_0(t+u_k)=0` and stop at the first such k. From finite numerical approximations to an autocorrelation, exact zero testing is not automatically available. It is safer to state the reconstruction as an eventually constant sequence of explicitly determined integers, or explicitly mention the exact oracle model.

For h<0 in the correlation, either define F for all real t by its original finite prime sum with x=e^t>0, or omit the finite initial interval where t+h<0. This has no effect on the limit.

## 5. Sharpness and its scope

For arbitrary locally finite point measures, symmetrization around centers A is injective exactly when the additive group generated by `2(a-a_0)` is nondiscrete. If it is dense, the reflection argument proves uniqueness. If it equals hZ with h>0, choose 0<delta<h/2 and take the distinct combs

\[
 \mu=\sum_{k\in\mathbb Z}\delta_{a_0+\delta+kh},\qquad
 \nu=\sum_{k\in\mathbb Z}\delta_{a_0-\delta+kh}.
\]

Every allowed reflection swaps them, so every symmetrization agrees. For a single center, two reflected single atoms already give nonuniqueness.

Thus three suitably spaced centers are minimal for this general class of locally finite infinite spectra. The statement must not be promoted to minimality for actual Dirichlet zero spectra. It is also false as a minimality claim for finite measures or finite multisets: two distinct centers already eliminate a nonzero periodic finite signed difference.

## 6. Literal primes and the square correction

For the prime-only sum

\[
 S_p(x)=\sum_{p\le x}(\log p)W(p)(1-p/x),
\]

the proposed correction is correct:

\[
 B(t)=\frac23+4\sum_{j:\chi_j^2=1}c_j
 \Re\frac{e^{-ia_jt}}{(1-2ia_j)(3-2ia_j)}.
\]

Indeed,

\[
 \int_0^{\sqrt x}u^{-2ia}(1-u^2/x)\,du
 =\frac{2x^{1/2-ia}}{(1-2ia)(3-2ia)}.
\]

The factor 2 in W gives the displayed factor 4. The baseline term is `(2/3)sqrt(x)`. The prime number theorem for the fixed character chi^2 gives zero main term for nonprincipal chi^2. Chebyshev's bound provides a uniform bound before summing over j, so dominated convergence is legitimate with `sum c_j<infinity`. Higher powers contribute `O(x^(1/3)log^2 x)` because W is uniformly bounded. Consequently

\[
 F_p(t)=e^{-t/2}\{S_p(e^t)-e^t/2\}+B(t)
\]

differs from F(t) by o(1) and has the same autocorrelation.

## 7. Novelty review

The supplied Article already proves a complex-weight universal reconstruction theorem and explicitly asks whether one real nonnegative prime weight can encode the labelled spectrum. The present construction addresses that question by inserting three modulations and recovering the resulting symmetrizations. The new contribution should be described at this level.

The underlying irrational-reflection uniqueness mechanism is closely related to established phase-retrieval results and must not itself be advertised as unprecedented:

- Lukas Liehr, *Arithmetic progressions and holomorphic phase retrieval*, Bulletin of the London Mathematical Society 56(11) (2024), 3316-3330; DOI 10.1112/blms.13134; <https://arxiv.org/abs/2308.05722>. Theorem 1.1 characterizes modulus uniqueness on parallel lines by exclusion of arithmetic progressions of line heights. Theorem 1.5 gives three irrationally spaced Gaussian/Fourier measurements. The full paper was opened at <https://arxiv.org/html/2308.05722v2>.
- Matthias Wellershoff, *Phase retrieval of entire functions and its implications for Gabor phase retrieval*, Journal of Functional Analysis (2024), article 110403; DOI 10.1016/j.jfa.2024.110403; <https://arxiv.org/abs/2202.03733>. It includes uniqueness from three parallel lines with irrationally related distances and nonuniqueness for equidistant families.

Targeted searches combining real positive prime weights, autocorrelation, Dirichlet zeros, and universal reconstruction did not locate the same prime-side construction outside the supplied repository. This supports calling it a new extension relative to the supplied Article, not asserting a proved worldwide priority claim. The literature search does not establish nonexistence of an earlier result.

## 8. Optional strengthening

For every prescribed rational epsilon in (0,1), the coefficient budget can be reduced further to enforce `sum c_j <= epsilon/2`, retaining the same algebraic norm bound and tail construction. Then

\[
 1-\epsilon\le W(n)\le1+\epsilon
\]

while all labels and oriented multiplicities remain exactly recoverable. This strengthens the statement without requiring any additional number theory. It also makes clear why no uniform noise-stability conclusion should be inferred from exact identifiability.
