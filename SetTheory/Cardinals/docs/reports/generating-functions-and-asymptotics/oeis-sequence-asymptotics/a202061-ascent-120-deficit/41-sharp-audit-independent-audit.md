# Independent audit of the sharp A202061 logarithmic deficit

Audit date: 2 October 2026.

## Verdict and scope

I find the two new arguments sufficient to establish

\[
 n\log\mu-\log a_n
 =\left(\frac{3\pi^2\alpha^2}{2v}\right)^{1/3}
 n^{1/3}(\log n)^{2/3}
 +o\bigl(n^{1/3}(\log n)^{2/3}\bigr),
\]

where \(\alpha=(8z^2-29z+9)/7\), \(v=(2z^2-7z+2)/2\), and \(z\) is the smallest positive root of \(z^3-5z^2+6z-1\). The constant is

\[
 C_*=2.23262530761284492217976470053\ldots.
\]

This verdict depends on the exact positive height-walk representation and the first-hit bound already proved in the frozen report. It does **not** infer a sharp limit from that report's older two-sided order bounds. I checked the new upper calibration, lower exact-length construction, the analytic input actually used by them, and the normalization and leading constants. The stronger global equivalents and ancillary cutoff assertions in the kernel note are not needed for this verdict, and this audit should not be read as a separate certification of every such assertion.

There is no unresolved leading-order gap in the two sharp bounds. The lower proof now explicitly permits a local-only kernel derivation; that is the safest theorem dependency. The conclusion is a sharp *logarithmic deficit*, not a multiplicative equivalent for \(a_n\) or an all-orders expansion.

## 1. Independent algebra and local lower estimate

The audit script `independent_identities.py` starts with the entropy of the four binomial factors in the frozen positive block formula, rather than assuming the kernel note's covariance matrix. It checks, modulo the cubic for \(z\):

- the tilted entropy's stationary point \((a,b,u)=(\alpha,\alpha,\kappa)\)
- the critical normalization \(\rho=(1-\alpha-\kappa)/(1+\alpha)\)
- the marginal height covariance \(((-H)^{-1})_{ww}=v\), for \(w=b-a\)
- the conditional \(q\)-center coefficient \(\beta=((-H)^{-1})_{aw}/v=-4(z-3)(2z-1)/7\)
- strict negative definiteness of the entropy Hessian, using exact rational root isolation to certify the principal-minor signs
- positivity of the saddle's factorial arguments
- the discriminant derivative identities that give \(\Psi_s=1/\alpha\), \(\Psi_\theta=0\), and \(\Psi_{\theta\theta}=v/\alpha\)

The supplied `kernel/derive_constants.py` also ran successfully, including its Hessian and amplitude checks. Its full amplitude is not necessary to identify the leading deficit constant.

Here is why the local-only estimate needed by the lower construction is rigorous. Retain just \(j=q\) in the exact positive formula. Uniform Stirling gives a summand

\[
 \ell^{-3}A(a,b,u)\exp(\ell S(a,b,u))(1+O(\ell^{-1})),
\]

with \(A\) bounded above and away from zero in a fixed interior neighborhood of the saddle. Put \(s=d-1\). After applying \(\rho^\ell z^{-s}\), the linear terms cancel. For fixed \(s\), minimizing the positive quadratic form over the \(q\) and \(k\) coordinates gives exactly \(s^2/(v\ell)\), because the \(ww\) entry of the inverse negative Hessian is \(v\).

Take \(q,k\) in fixed windows of width proportional to \(\sqrt\ell\) around these conditional centers. There are at least \(c\ell\) integer pairs. Their extra quadratic cost is bounded. Their total displacement from the original saddle is \(O(\sqrt{\ell\log n})\), so the cubic entropy remainder is

\[
 O((\log n)^{3/2}/\sqrt\ell)=o(1)
\]

uniformly when \(\ell\ge c(\log n)^7\). This yields

\[
 \sum_q \rho^\ell t^d B(\ell,q,q+d-1)
 \ge c\ell^{-2}\exp[-d^2/(2v\ell)-o(1)]
\]

in the required shifted \(q\)-window. Replacing \(d-1\) by \(d\) has error \(O(\sqrt{\log n/\ell})=o(1)\); \(t^d=z^{-1}z^{-(d-1)}\) changes only a fixed prefactor. No global saddle dominance, unrestricted tail summation, lattice local central limit theorem, or exact amplitude is needed for this lower estimate.

## 2. Uniform transformed-row upper estimate

Let \(H=n^{2/3}(\log n)^{1/3}\), \(F=H^2/n\), \(a=F/n\), and \(b=F/H\). The identities \(b^2=a\), \(aH=\log n\), and

\[
 H(a^2+ab+b^3)=o(1)
\]

are correct. They are essential to controlling the discriminant Taylor remainder uniformly over \(q\le RH\).

### Analytic prerequisite

At the critical point the two discriminant roots satisfy \(0<z_*<z_2<1\), and the denominator factors in the fixed-\(q\) rational formula stay nonzero. These inequalities persist on a fixed small real neighborhood of \((\rho,t)\). The elementary square-root coefficient convolution argument in the frozen report therefore applies with uniform constants there:

\[
 Q_q(x,T)T^{-q}\le Cq^{-3/2}e^{q\Psi(s,\theta)}.
\]

No identification of a spectral radius from the discriminant is involved. The fixed-\(q\) functions have a common positive neighborhood in the length and height variables, which also justifies fixed-\(q\) dominated convergence and the fixed Chernoff tilts below.

### Small normalized steps

Uniform differentiability on the compact time-height rectangle gives the asserted linear majorants. The derivative error can be chosen small enough because \(B'<\alpha/3\) and \(y+\epsilon\) stays in a fixed compact positive interval. The exponent bound becomes

\[
 q\Psi\le (B'/\alpha)(\log n)\,q/(h+\epsilon H)+o(1).
\]

For \(Q<q\le H/(\log n)^2\), the exponential multiplier is \(1+o(1)\), uniformly even when the current height is small; the positive \(\epsilon H\) in the denominator matters here. This tail is \(O(Q^{-1/2})\). For larger \(q\le h\le RH\), its total is at most

\[
 C(H/(\log n)^2)^{-1/2}n^{B'/\alpha}=o(1).
\]

Splitting the sign of \(d\) only in these vanishing tails is important: it does not double the critical row mass. For the finitely many \(q\le Q\), uniform domination and finite \(L,d\) truncation give a uniform limsup at most the corresponding unrestricted critical contributions. Equality need not hold near the terminal time because transitions are truncated. Thus the row limsup is bounded by the critical mass \(m_*<1\).

### Macroscopic steps

The two Chernoff arguments cover every excluded step, and their constants can be chosen independently of \(n,m,h\):

- For \(L>\eta n\), a fixed positive length tilt gives \(\exp[-s_0\eta n+O(H)]\)
- For \(|d|>\eta H\), a fixed signed height tilt gives \(\exp[-\eta\theta_0H+C R\theta_0^2H+o(H)]\); choose \(\theta_0\) after fixed \(\eta,R\)

The zero first height derivative of \(\Psi\) is indispensable in the second estimate. Summing over \(q\le RH\) adds at most a polynomial factor. Hence neither unusually long jumps nor large height changes escape the uniform row bound.

## 3. Telescoping, terminal degree, and first hit

For a macro-prefix of length \(m\) ending at height \(h\), the product of critical tilted weights equals the original multiplicity times \(\rho^m t^{h-1}\). With residual terminal degree \(k=n-1-m\), its normalized coefficient contribution therefore includes exactly

\[
 \rho^{k+1}t^{1-h}.
\]

The calibration transformation telescopes with the sign used in the proof. Undoing it leaves \(\exp[-Ff(0,1/H)]\) and the residual factor \(\rho^k t^{1-h}e^{Ff(m/n,h/H)}\). Since

\[
 f(s,y)\le Py+C(1-s),
\]

its logarithm is bounded above by

\[
 k(\log\rho+CF/n)+h(-\log t+PF/H)+O(1),
\]

which is uniformly bounded for large \(n\). Thus terminal length and final height cause no hidden exponential loss. Summing all transformed prefixes is bounded by a geometric series; it introduces no factor exponential in the number of steps or in \(n\).

The frozen first-hit estimate at threshold \(RH\) supplies \(\exp[-R^2F/(4D)]\). Each calibration is fixed before selecting sufficiently large fixed \(R\). Therefore this complement is negligible at the claimed constant. The order of choices is valid even though calibration slopes grow when their endpoint truncation is subsequently removed.

## 4. Calibration value and endpoint slopes

For \(f=g+py\), the inequality

\[
 2\sqrt{Bp'}-p'(y+\epsilon)\le B/(y+\epsilon)
\]

is the exact square inequality needed for the Hamilton-Jacobi bound. There is no sign reversal. The Kepler parametrization obeys

\[
 y'=\pi M\cot u,\qquad y''=-vB/y^2,
 \qquad M^3=2vB/\pi^2.
\]

Thus \(p_*=-y'/v\) is increasing and \(p_*'=B/y^2\). Both \(p_*^2\) and \(\sqrt{p_*'}\) are integrable at the endpoints. Restricting to \([\delta,1-\delta]\) and linearly reparametrizing gives bounded smooth calibrations. The change-of-variable factors tend to one, so their values tend to \(3B/M\). The limits \(\epsilon\to0\), \(\delta\to0\), \(B\uparrow\alpha/3\) are taken after the coefficient liminf for each fixed calibration. This gives \(C_*\) without using an unbounded slope in any finite-\(n\) row estimate.

## 5. Exact-length lower construction

All relevant costs and constraints in the sine-square construction check:

1. With \(J=\lceil(\log n)^3\rceil\), its minimum height and block length are \(\Theta((\log n)^7)\). The finite seed therefore costs only \(O((\log n)^7)=o(F)\).
2. The ascent seed has degree \(2h_0-1\), the descent seed degree 1, and the original first letter degree 1. Together with the leading \(x\) of each of the \(m\) blocks and \(\sum\ell_j=n-m-2h_0-1\), the total degree is exactly \(n\).
3. Symmetry and unimodality of centered integer-interval convolutions imply the two exact-sum constraints lose at most \((2n+1)^2\). Length and increment constraints are independent before their respective sums are fixed.
4. The height error uses both the prefix and complementary suffix sums. It is \(O(h_j/\sqrt{\log n})\) throughout, including near the descent endpoint. The reserved relative margin \(\eta=(\log n)^{-1/4}\) dominates this, the length-window error, the shifted \(q\)-saddle window, and integer rounding. Every retained term is legal.
5. A rectangle has about \(\ell^{3/2}/(\log n)^2\) choices, while its summed-\(q\) local kernel costs \(\ell^{-2}\). The net leading polynomial cost is therefore \(\ell^{-1/2}\), not \(\ell^{-2}\). This is the source of the correct entropy coefficient.
6. Varying the increments across their rectangles costs \(O(\sqrt{\log n})\) per block, and varying lengths costs less. The accumulated error \(O(M\sqrt{\log n}+M\log\log n+\log n+(\log n)^7)\) is \(o(F)\).

The deterministic sums are

\[
 \sum g_j^2/\ell_j=(1+o(1))4\pi^2\alpha^2n/M^2,
 \qquad \tfrac12\sum\log\ell_j=(1+o(1))M\log n/3.
\]

Integer rounding is harmless because the minimum length grows as the seventh logarithmic power. In justifying the first sum, Taylor approximation near the sine peak is understood with an absolute remainder, rather than a pointwise relative remainder where the derivative is zero. The sum-level statement is unchanged. The omitted endpoint logarithms contribute \(O(J\log n)=o(M)\), and do not alter the entropy sum.

Consequently the leading cost is

\[
 \frac{2\pi^2\alpha^2 n}{vM^2}+\frac{M\log n}{3}.
\]

Its minimizer has \(M^3\sim12\pi^2\alpha^2 n/(v\log n)\), and its value is \((1+o(1))C_*F\). This matches the calibration bound for every sufficiently large integer \(n\), without a subsequence or interpolation argument.

## Reproduction

Run `python audit/independent_identities.py` from the sharp-deficit directory. The expected output is saved in `audit/independent-identities-output.txt`. These exact identities certify the algebra used above; the uniform estimates and path-counting arguments are the mathematical audit, not conclusions inferred from finite numerical fitting.
