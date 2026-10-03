# Independent adversarial audit: normalized rows and an exact central repair

Date: 2 October 2026. Source: `../a202061-third-order-research/normalized-kernel-lower-draft.md`. This is a new audit outside the frozen approved second-order release. Source identities are recorded separately.

## Verdict

The normalized-row lower-coefficient construction establishes

\[
D_n\le CF\left[1+\frac{7\log L}{3L}+\frac\kappa L\right]+o(F/L),
\quad \kappa=\log Y_0-2\log3+2c_*.
\]

I found no unresolved normalization, mean-flow, concentration, legality, exact-degree, injectivity, or trial-action error at the target scale. The proof uses the previously audited exact macro-kernel, its differentiated analytic square-root transfer, and its local positive Gaussian lower bound. It does not require a new local central limit theorem or differentiability of an asymptotic remainder.

Combined with `one-sided-next-constant-proof.md`, this proves the new two-sided statement

\[
D_n=CF\left[1+\frac{7\log L}{3L}+\frac\kappa L\right]+o(F/L).
\tag{T}
\]

This is a research theorem with the explicit dependencies above. It does not retroactively change any frozen release or establish a multiplicative equivalent for \(a_n\).

The checks below supply details that are easy to lose in the compact construction, especially the exact macro-length convention and the rounded time change.

## 1. The local threshold is an exact positive subkernel

Write \(h_0=L^{21}\), \(\eta=2/L^2\), \(u=(1-\eta)h\), and let \(\chi_h\) retain all integers \(q\le\lfloor u\rfloor\), with fractional weight \(u-\lfloor u\rfloor\) at the next integer. Its values lie in \([0,1]\), its support lies below \(u+1\), and its weighted sum is continuous in \(h\). Hence it is a lower subkernel, even though it is a convenient real interpolation rather than a combinatorial counting function.

For large \(h\), the row at zero length tilt is below the unrestricted critical mass \(m_*<1\). At a fixed small positive length tilt, the endpoint term tends to infinity with \(h\), by the positive root exponent. Strict increase in the length tilt therefore supplies a unique small root \(V(h)>0\) with \(R_h(V(h),0)=1\). The finite-height endpoint calculation applies also to a fractional final term: altering one term changes row mass by \(O(\log h/h)=o(1)\). Thus

\[
V(h)=\frac\alpha h\left[\frac12\log h+\log\log h+c_*+o(1)\right]
\tag{1}
\]

uniformly on \(h_0\le h\le RH\), because the cutoff change contributes only \(O(\eta\log h)=O(1/L)\) to the bracket there. On all \(h\ge h_0\), the same argument gives the global comparability \(V(h)\asymp\log h/h\), with constants uniform for sufficiently large \(n\).

At this threshold, all but a vanishing part of the added endpoint mass lies at \(q=h[1+o(1)]\); its mass is \(1-m_*+o(1)\). The remaining bounded or intermediate indices have negligible first moment after division by \(h\). Therefore

\[
N(h):=\sum q\chi_h(q)W_q(V(h),0)
  =(1-m_*)h[1+o(1)],\qquad ch\le N(h)\le Ch.
\tag{2}
\]

For example, the low critical portion contributes at most \(O(\sqrt h)\) to the first moment, and splitting at \((1-\varepsilon)h\) makes the nonendpoint tilted portion negligible relative to \(h\); then let \(\varepsilon\downarrow0\).

The uniform analytic transfer implies the stronger convenient conditional-cumulant identity

\[
\partial^j\log W_q(s,\theta)=q\partial^j\Psi(s,\theta)+O(1),
\qquad 1\le |j|\le 2,
\tag{3}
\]

uniformly for every integer \(q\ge1\) in a sufficiently small real neighborhood. For large \(q\), use the analytic nonvanishing amplitude and the \(O(1/q)\) differentiated transfer remainder. The finitely many remaining rows are strictly positive at the origin and analytic in a common neighborhood, so their logarithmic derivatives are bounded after shrinking it. This justifies the all-q reduced-factor assertion in the draft.

On each interpolation interval,

\[
V'(h)=-\frac{(1-\eta)W_{\lfloor u\rfloor+1}(V(h),0)}{R_{h,s}(V(h),0)}.
\]

The numerator is \(\Theta(\log h/h)\), by the exact positive endpoint amplitude. From (2)-(3), the denominator is \(N(h)/\alpha+O(\log h)=\Theta(h)\). Consequently

\[
c\frac{\log h}{h^2}\le -V'(h)\le C\frac{\log h}{h^2}.
\tag{4}
\]

Similarly, differentiating \(N\) yields a boundary term of size \(O(\log h)\), plus \(V'\) times a q-length mixed moment bounded by \(Ch^2\). This proves \(|N'|\le C\log h\). At interpolation junctions these are one-sided derivatives; both functions are continuous. In particular they are locally Lipschitz, with the stated bounds on each compact h-range. No derivative of the o(1) in (1) was taken.

## 2. The energy-minimum argument does construct an exact duration-n arch

Define, for \(Y\ge h_0\),

\[
J_n(Y)=nV(Y)+2\sqrt{2/v}\int_{h_0}^Y\sqrt{V(h)-V(Y)}\,dh.
\]

It is continuous. From (4), the portion \(h\in[Y/4,Y/2]\) of the integral is at least \(c\sqrt{Y\log Y}\) for large \(Y\), so \(J_n(Y)\to\infty\). At the lower endpoint, \(J_n(h_0)=nV(h_0)\gg F\).

For every absolutely continuous path of duration n with endpoints h0 and maximum Y, the pointwise square inequality in the draft integrates to action at least J_n(Y). The total variation must cross each level between h0 and Y in both directions, so replacing its weighted variation integral by twice the upward integral is legitimate even for a nonmonotone trial. The explicit shifted Kepler trial has action O(F). Thus the global minimum of J_n is O(F) and occurs at an interior point.

One-sided differentiation in Y is valid. Near h=Y, the bound (4) compares \(V(h)-V(Y)\) to a positive constant times Y-h on any fixed local interval, so the differentiated integrand is dominated by \(C(Y-h)^{-1/2}\). The moving-endpoint term vanishes. Hence the derivative is

\[
J_n'(Y)=V'(Y)\left[n-\sqrt{2/v}
 \int_{h_0}^Y[V(h)-V(Y)]^{-1/2}\,dh\right].
\]

At an interpolation junction, both one-sided V' factors are strictly negative, and the bracket is the same continuous quantity. The minimum condition forces that bracket to vanish, including at a junction. This yields precisely the duration equation in the source.

Solving \(\dot h=\sqrt{2v(V(h)-V(Y))}\) upward and reflecting gives an arch of duration exactly n. Equality holds in the square inequality. Its action is J_n(Y), so this is an actual global action minimizer, not merely a formal stationary solution.

Its peak satisfies Y=Theta(H). The upper bound follows from kinetic coercivity:

\[
J_n(Y)\ge\frac{[2(Y-h_0)]^2}{2vn}.
\]

Since J_n(Y)=O(F) and nF=H², this gives Y=O(H). If Y<=sqrt(n), monotonicity gives nV(Y)>=nV(sqrt(n))>>F. Thus log Y>=L/2 eventually, and nV(Y)<=O(F) combined with V(Y)>=c log Y/Y gives Y>=cH.

## 3. Macro time and rounding introduce no unrecorded order-M cost

Let \(\lambda=V(Y)\) and \(\theta=\pm\sqrt{2(V(h)-\lambda)/v}\). Define the original real macro coordinate by \(dt/dj=N(h)/\alpha\). Then

\[
h'=(v/\alpha)N(h)\theta,
\quad \theta'=N(h)V'(h)/\alpha.
\tag{5}
\]

Below Y/2, the velocity is comparable to sqrt(h log h); above Y/2, the potential difference is comparable to (L/Y²)(Y-h). These comparisons show that the real macro duration m is Theta(sqrt(Y/L))=Theta(M0), where M0=F/L.

Rounding m to the nearest integer M and reparameterizing multiplies the physical h- and theta-velocities by m/M=1+O(1/M). It does not alter the pointwise energy identity \(\lambda+v\theta^2/2=V(h)\). In particular

\[
\int_0^M N(h(j))/\alpha\,dj=(M/m)n=n+O(n/M)=n+O(H).
\tag{6}
\]

This O(H) degree discrepancy is included in, and is smaller than, the later O(HL) repair allowance.

The sampled deterministic increments satisfy

\[
h_{j+1}-h_j=(m/M)(v/\alpha)N(h_j)\theta_j+O(L^2).
\]

Indeed (4)-(5) imply \(|\theta'|\le CL/h\) and \(|h''|\le CL^2\) almost everywhere. The apparent singularity at the peak cancels in (5). Across interpolation junctions h' remains continuous and the same almost-everywhere bound controls its Lipschitz norm; an unbounded number of junctions does not add a separate error.

Thus comparing row means with deterministic increments costs O(L²) per slot, plus the O(1/M) velocity reparameterization. Over an ascending prefix the latter sums to O(h/M), not O(number of slots times H/M).

## 4. The independent row laws have the required uniform moments

For a source height h on this arch, compare its normalized row at (lambda,theta) with the exact threshold row at (V(h),0). The identity \(\lambda+v\theta^2/2=V(h)\), the critical root expansion, and (3) give

\[
|\Psi(\lambda,\theta)-\Psi(V(h),0)|
 \le C(L/h)^{3/2}.
\]

The logarithmic reduced-factor change is O(sqrt(L/h)). Since q<=h, every fixed-q weight changes by a relative factor 1+O(L^(3/2)/sqrt(h)). This is uniform, including the entire critical small-q component. The row mass consequently equals 1+O(L^(3/2)/sqrt(h)); since h>=L^21, the sum of absolute log row masses is at most O(ML^-9)=o(M).

Conditional on q, (3) gives

\[
E[d\mid q]=(v/\alpha)q\theta+O(qL/h+1),
\quad E[e\mid q]=q/\alpha+O(q\sqrt{L/h}+1).
\]

Changing the q-mean from its threshold value N(h) costs at most
\(ChL^{3/2}/\sqrt h\). Multiplying that error by theta in the first formula proves

\[
E d=(v/\alpha)N(h)\theta+O(L^2),\quad
E e=N(h)/\alpha+O(L^{3/2}\sqrt h).
\tag{7}
\]

The length here is the **entire exact macro degree**, including the leading factor in the macro multiplier. There is no additional constant per sampled macro-step. In the later patch alone, the local positive coefficient estimate uses internal length e-1 and hence incurs a fixed factor per patch slot; this costs O(r), which is o(M).

For an additional height tilt |z|<=c/sqrt(hL), the change in each exponent qPsi is bounded: the theta*z cross term is O(1). Conditional height variance is O(q), and conditional means are O(sqrt(hL)); their mixture variance is O(hL). The same bounds hold throughout that tilted interval. For an additional length tilt |z|<=c/h, conditional means are O(h) and conditional variances O(h), giving mixture variance O(h²). Integrating the corresponding second log-row derivatives yields exactly the centered subexponential moment bounds used by the draft. No independence among q and the other variables within a slot is assumed.

## 5. Prefix and complementary-suffix control is sufficient for legality

On the ascending portion below Y/2, the number of previous slots is at most C sqrt(h/log h), so their total height-variance bound is at most C L h^(3/2)/sqrt(log h). Their deterministic drift error, by (7) and Section 3, is at most

\[
CL^2\sqrt{h/\log h}+Ch/M=o(h/L^2)
\]

uniformly for h>=L^21. In the Bernstein bound at threshold h/(20L²), the quadratic regime applies and gives exponent at least c sqrt(h log h)/L^5. At the smallest height, this is at least cL^(11/2)sqrt(log L), far larger than log M=O(L).

Near the peak use the total variance bound O(MHL)=O(nL) and threshold cH/L². The exponent is at least cF/L^5, also much larger than L. A union bound over all M boundary positions therefore tends to zero. The descending side is reconstructed backward from its fixed endpoint and uses a complementary suffix of independent variables. This does not condition any row law and does not assert independence after conditioning.

On this event, each actual source height differs from its deterministic value by at most h/(10L²). Every retained q is at most (1-2/L²)h+1, which lies below that actual height for large n. Thus every sampled row is genuinely legal. The full exact macro structure has d=1+r-q with r>=0, so legal q also prevents a nonpositive destination; the separately controlled positive boundary heights are consistent with this.

The additional two events have probability tending to one by ordinary variance bounds:

* the sampled total degree differs from its mean by at most LH sqrt(M)
* the exact gap Delta between central endpoints has absolute value at most L sqrt(nL)

For the second event, the deterministic outside height increments sum to zero because the removed interval has symmetric endpoints, while the total mean mismatch is O(ML²)=o(sqrt(nL)). Hence the stated bound controls the actual gap, not only a centered variable. Intersecting these events with legality still leaves probability 1-o(1).

## 6. The patch can repair every retained realization at o(M) cost

Take r=M^(3/4)+O(1), with the specified parity, and remove the r central slots. Near the peak, |h''|<=CL² and h'(M/2)=0 imply

\[
\max_{a\le j\le b}|Y-h_j|\le CL^2r^2=o(Y),
\]

since Y=Theta(M²L). In particular the missing expected degree is

\[
r(1-m_*)Y/\alpha\,[1+o(1)].
\tag{8}
\]

For the full expected degree, sum the error in (7) to obtain O(ML^(3/2)sqrt(H))=O(HL). The quadrature error for N is at most its total variation along the arch, bounded by C L Y=O(HL). Equation (6) contributes only O(H). Thus total expected degree differs from n by O(HL).

After subtracting the exact seed degree 2 floor(h0)+1 and the sampled degree, the integer residual D obeys

\[
\frac D{rY}\longrightarrow\frac{1-m_*}{\alpha}
\]

uniformly over the retained high-probability event. The errors divided by rY are bounded by constants times
\(L/r+L\sqrt M/r+h_0/(rH)\), all tending to zero. In particular D is positive and much greater than r.

Assign r positive integer total degrees summing to D and differing by at most one; their internal lengths are these degrees minus one. Assign integer height increments by rounding successive multiples of Delta/r, so they sum exactly to Delta and differ by at most one. This cumulative rounding also keeps each intermediate patch boundary within one unit of its linear interpolation. Both patch endpoints are Y[1+o(1)], hence all patch boundary heights have that form.

The internal lengths are asymptotic to (1-m_*)Y/alpha. The shifted local q-saddle is therefore

\[
\alpha(e_i-1)+\beta_{qd}(d_i-1)=(1-m_*)Y[1+o(1)].
\]

Its Gaussian q-window lies strictly below the actual source height by a fixed positive multiple of Y. Indeed m_*>0, the window width is O(sqrt(Y)), and

\[
|d_i|\le |\Delta|/r+1=o(\sqrt{YL})=o(Y).
\]

The audited local positive Gaussian lower bound is applicable uniformly: each internal length is exponential in L and |d_i| is within its O(sqrt(e_i L)) range. Multiplying its r estimates costs at most

\[
CrL+C\sum_i d_i^2/Y
\le CrL+C\Delta^2/(rY)+Cr/Y
\le CrL+CM L^3/r=o(M).
\tag{9}
\]

This pays for the q-window and all local prefactors rather than silently discarding a fixed factor per global slot. Exact integer physical degree and endpoint height hold for each retained outside realization, not merely in expectation or along a subsequence.

The two seed blocks are exactly those in the audited lower construction: degree 2 floor(h0)-1 to ascend, degree 1 to descend, plus the original leading letter of degree 1. Their cost is O(h0)=polylog(n)=o(M). All critical height tilts cancel over the complete path.

## 7. The weighted count is injective in the positive expansion

The number M of middle slots and the r patch positions are fixed before sampling. Given a completed marked macro-path, deleting those positions recovers every outside triple (degree,q,increment) and its underlying micro-block choice. Different outside data therefore cannot create the same completed entry of the exact positive expansion.

If a fixed macro triple has multiplicity greater than one, its exact kernel coefficient already counts those choices, and the probability law simply uses that positive total weight. One may equivalently expand the law to the underlying micro-choices to make the injection literal. The patch sums only a specified legal q-window and a positive subset of micro-choices. Its fractional outside chi factors are each <=1. Thus summing the product lower bounds over all retained independent outside realizations is a legitimate lower bound on the coefficient. No unsupported count of unmarked paths or division by the number of repairs is involved.

## 8. Removing the tilts loses only o(M)

Undoing the outside normalization introduces the exponent
\(-\lambda\sum e_j-\sum\theta_jd_j\), plus \(\sum\log R_j=o(M)\).
The sampled degree differs from n by the actual patch and seed degrees. Since \(\lambda=O(L/H)\), replacing its term by -lambda*n costs O(rL)+polylog(n)=o(M).

For each outside interval, let E_j be its reconstructed boundary error and g_j=h_(j+1)-h_j. Discrete summation by parts expresses \(\sum\theta_j(d_j-g_j)\) using boundary terms and \(\sum(\theta_j-\theta_{j-1})E_j\). The interior sum is O(M/L), since the derivative bound is CL/h_j and |E_j|<=h_j/(10L²); consecutive deterministic heights are uniformly comparable because h_j>=L^21.

At a central edge, |theta|<=CrL/Y and |E|<=CY/L², so the boundary term is O(r/L). At a seed edge E has only the bounded floor-rounding error. These estimates prove the asserted o(M), with no centering after the good event is imposed.

The deterministic sum \(\sum\theta_jg_j\) differs from its Stieltjes integral by at most O(L²). For each unit interval bound the error by oscillation(theta) times total variation(h); sum the bound CL/h times |dh| over the two monotone halves. The result is at most CL log(Y/h0)=O(L²). The removed central interval contributes only O(rL), by the global bound |theta*h'|<=CL. Therefore

\[
\lambda n+\sum_{\mathrm{outside}}\theta_jd_j
 =nV(Y)+2\sqrt{2/v}\int_{h_0}^Y\sqrt{V(h)-V(Y)}\,dh+o(M).
\]

The retained event has probability 1-o(1), whose negative logarithm is o(1). Combining all weighted counts and patch estimates gives D_n<=J_n(Y)+o(M), exactly as claimed. Since M=Theta(F/L), this is the required precision.

## 9. The fixed Kepler trial computes the constant without perturbing the minimizer

The minimizing action is bounded above by the shifted leading Kepler trial h0+H*y_*(t/n). Its derivative is exactly that of H*y_*. On y>=L^-6, the row-threshold expansion is uniform and gives

\[
\frac nF V(Hy)=\frac\alpha{3y}
 +\frac\alpha{2Ly}\left[\frac73\log L+\log y
       +2\log(2/3)+2c_*+o(1)\right].
\]

The elementary logarithmic expansion has uniform o(1) remainder in its bracket on this domain; the threshold remainder is also uniform because the smallest h tends to infinity. The constant h0 shift changes the resulting integrated potential by o(F/L): use |V'(h)|<=CL/h² on the interior, h0/H smaller than every fixed inverse power of L, and the integrable Kepler endpoint comparison.

More explicitly, on y<=L^-6, ds is comparable to sqrt(y)dy and both leading potential and kinetic endpoint integrals are O(F L^-3). For the exact shifted potential, the elementary upper bound
\(V(h_0+Hy)\le CL/(h_0+Hy)\le CL/(Hy)\)
provides the same integrable domination; the endpoint itself has measure zero. No uncontrolled constant at the seed height is integrated over a macroscopic time.

On the full leading arch,

\[
\frac\alpha2\int_0^1\frac{ds}{y_*}=C,
\qquad
\frac{\int_0^1(\log y_*)\,ds/y_*}
 {\int_0^1ds/y_*}=\log Y_0-2\log2.
\]

The leading kinetic plus potential integral is C. These formulas give precisely the constant \(\log Y_0-2\log3+2c_*\) after multiplying by F. The one-sided lower-coefficient theorem, and hence (T) together with the companion proof, follow.

## Scope of this signoff

The exact small-q critical mass is retained in the normalized laws; deleting it would invalidate the claimed scale. The argument also genuinely repairs both lattice constraints and does not use an unspecified local limit theorem. Its endpoint and stochastic losses are all explicitly o(F/L), and the constant is evaluated on a fixed trial path rather than by differentiating an uncontrolled remainder.

No unresolved mathematical obstruction remains within the stated imported dependencies. A future assembled report still requires checking that it reproduces these proofs and constants without transcription changes. No frozen report was modified during this audit.
