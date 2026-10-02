# All finite inverse-log orders: coefficient-to-action reduction

New research proof, 2 October 2026. This document does not amend a frozen release. It extends the imported, independently audited third-term mechanisms; independent review of this extension is still appropriate.

## 1. Statement and exact scope

Use the positive macro-kernel, critical constants, and notation of the approved third-term sources:

- `../a202061-third-order-research/normalized-kernel-lower-draft.md`
- `../a202061-third-order-upper-audit/lower-construction-audit.md`
- `../a202061-third-order-upper-audit/one-sided-next-constant-proof.md`

In particular, let

\[
 L=\log n,\quad H=n^{2/3}L^{1/3},\quad F=n^{1/3}L^{2/3},\quad M_0=F/L,
 \qquad D_n=n\log\mu-\log a_n.
\]

The imported analytic inputs are the exact positive macro expansion and terminal factor, its uniformly differentiated analytic square-root transfer, the critical root derivative identities, the local positive Gaussian lower bound, and the fixed-ceiling first-hit estimate. No new finite-height spectral equivalence is used.

Put

\[
 c_* =\log\frac{1-m_*}{2a_*},\qquad A=\log T+c_*.
\]

Define the polynomial truncation

\[
 k_N(T)=T/2+\log T+c_*+\sum_{j=1}^{N}\frac{p_j(\log T+c_*)}{T^j},
 \qquad \phi_N(h)=\frac{\alpha k_N(\log h)}h,
\tag{1.1}
\]

where the polynomials are uniquely obtained by formal substitution into

\[
 k-T/2-\log k+\log\!\left(\sum_{j\ge0}(3/2)_j k^{-j}\right)
       +\log\frac{a_*}{1-m_*}=0.
\tag{1.2}
\]

The first three are

\[
 p_1(A)=2A-3,\quad p_2(A)=-2A^2+10A-33/2,
\]
\[
 p_3(A)=\tfrac83A^3-24A^2+86A-120.
\]

For each fixed N choose a fixed h_b>1 large enough that \(\phi_N\) is positive, strictly decreasing, and strictly convex on \([h_b,\infty)\). Let \(\mathcal A_N(n)\) be the minimum of

\[
 \int_0^n\left[\frac{\dot h(t)^2}{2v}+\phi_N(h(t))\right]dt
\tag{1.3}
\]

over absolutely continuous paths \(h\ge h_b\) with \(h(0)=h(n)=h_b\). Different sufficiently large fixed choices of h_b alter this action by O(1).

**Reduction theorem.** For every fixed integer \(K\ge0\), with \(N=K+3\),

\[
                 D_n=\mathcal A_N(n)+o(M_0/L^K).
\tag{1.4}
\]

Constants, auxiliary cutoff exponents, and the threshold on n may depend on K. This is an all-finite-orders statement, not a uniform assertion when K grows with n. In particular it establishes neither a multiplicative asymptotic equivalent for \(a_n\), a polynomial prefactor, nor an exponentially complete transseries.

The logarithmic formula in (1.1) is **not** continued to h=0. Its fixed lower endpoint is essential to making the definition meaningful. A positive convex core extension with finite core action could instead be used, at an O(1) change.

## 2. Quantitative local Watson lemma

Let \(R_r(s,\theta)\) be the exact row with all destination states retained and with fractional q cutoff at real r: weight 1 through floor(r), weight r-floor(r) at floor(r)+1, and zero thereafter. The exact degree s counts the entire macro degree. Write

\[
 W_q(s,\theta)=a(s,\theta)q^{-3/2}e^{q\Psi(s,\theta)}(1+E_q(s,\theta)).
\]

The imported transfer gives analytic a, \(a(0,0)=a_*>0\), uniformly differentiated \(E_q=O(q^{-1})\), and

\[
 \Psi(s,\theta)=\frac{s+v\theta^2/2}{\alpha}
    +O(s^2+|s\theta|+|\theta|^3).
\tag{2.1}
\]

After finitely many small q are included, the logarithmic first and second derivatives of \(W_q e^{-q\Psi}\) are bounded independently of q in a fixed real neighborhood. This all-q fact is proved in the imported lower audit.

For \(T=\log r\), \(k=T/2+\log T+O(1)\), and every fixed J,

\[
 R_r(s,\theta)=m_*+
  a_*\frac{e^{k-T/2}}k
  \left[\sum_{j=0}^{J}(3/2)_jk^{-j}+O_J(k^{-J-1})\right]
  +O_J(r^{-1/4}T^{c_J}+|s|+|\theta|),
 \quad k=r\Psi(s,\theta).
\tag{2.2}
\]

The same bound is valid uniformly for k within any fixed distance of that band, and with any fixed number of k derivatives of the normalized scalar endpoint expansion. (Only the first two parameter derivatives of the exact row are needed elsewhere.) Fixed powers \(T^{c_J}\) are harmless; their exact exponent is unnecessary.

Here are details sufficient to control the head rather than simply appending a formal Watson series. The reduced-factor comparison gives, for a row of bounded total mass, an O(|s|+|theta|) error upon replacing its reduced weights by their critical values. Split the remaining scalar sum at r/k² and r/2. On the first part, \(e^{kq/r}-1\le Ckq/r\); summing the critical \(q^{-3/2}\) tail gives a perturbation O(r^{-1/2}), while the missing critical tail is O(k r^{-1/2}). On the middle part the entire tilted sum is at most

\[
 C\frac{k}{\sqrt r}e^{k/2}=O(r^{-1/4}T^c).
\]

On the last part, a Riemann-sum error and the fractional final term cost relative O(k/r), and the transfer remainder costs O(1/r). Its integral is

\[
 r^{-1/2}e^k\int_0^{1/2}(1-u)^{-3/2}e^{-ku}du.
\]

Taylor expansion of \((1-u)^{-3/2}\) through order J, followed by integration of u^j, gives the displayed factorial coefficients and a remainder O(k^{-J-2}) before the factor k is restored. Extending the moment integrals to infinity costs an exponentially small term in k. Differentiating with respect to k inserts powers of u and yields the corresponding differentiated remainder bounds. All these estimates remain uniform if the cutoff has a fractional last term.

There is a unique small positive row root \(s_r\) with \(R_r(s_r,0)=1\). The previously proved first approximation locates its k in the band just used. Taking the logarithm of (2.2), then using that the derivative in k of its implicit left side is \(1+O(1/T)\), proves by finite Taylor inversion

\[
 \frac{rs_r}{\alpha}
 =k_N(T)+O_N\!\left(\frac{(1+\log T)^{N+1}}{T^{N+1}}\right)
       +O_N(r^{-1/4}T^{c_N}).
\tag{2.3}
\]

The difference between \(r\Psi(s_r,0)\) and \(rs_r/\alpha\) is O(T²/r), already absorbed in the algebraic error. Formal polynomial inversion is legitimate because finite substitution leaves precisely the stated residual and the implicit derivative is bounded below by 1/2.

The explicit truncations have, for every fixed j,

\[
 \phi_N^{(j)}(h)=
 \frac{\alpha}{2}(-1)^j j!\frac{\log h}{h^{j+1}}
       [1+O_{N,j}(\log\log h/\log h)].
\tag{2.4}
\]

Thus the positivity, monotonicity, convexity, and all polynomial derivative estimates used below follow directly.

**Differentiability qualification.** The fractional-cutoff exact root is continuous and piecewise C¹; it is not generally C² at integer cutoff junctions. We do not assert arbitrary classical h derivatives of its remainder there. Its audited one-sided derivative bounds are enough for the lower construction. Differentiable Watson remainders are needed only in the smooth endpoint surrogate/k variable; the upper construction uses the explicit smooth \(\phi_N\). This distinction removes a potentially false regularity requirement without weakening (1.4).

A consequence used for the upper bound is a quantitative row gap. If \(r\ge H L^{-E}\), \(r\le(R+1)H\), \(|s|+|\theta|\) is n to a negative fixed power times a fixed power of L, and

\[
 r\Psi(s,\theta)\le k_N(\log r)-\delta+o(\delta),
 \qquad \delta=L^{-K-2},\quad N=K+3,
\tag{2.5}
\]

then

\[
                         R_r(s,\theta)\le1-c\delta.
\tag{2.6}
\]

Indeed (2.3) has error o(delta) uniformly in this range. The actual k may lie far below the endpoint band; first bound the row by \(1+O(|s|+|\theta|)\) times the increasing scalar envelope \(G_r(k)=\sum_q\chi_r(q)W_q(0,0)e^{kq/r}\), and use monotonicity to replace k by the right side of (2.5). This replacement is in the endpoint band and has bounded envelope mass, so the multiplicative reduced-factor error is o(delta). The k derivative of this scalar envelope near the root tends to \(1-m_*>0\), by the endpoint calculation. Its root differs from the exact row root in k coordinates by an algebraically small error. The mean-value theorem now gives (2.6), with c depending only on the critical kernel after n is large enough.

## 3. General action facts and endpoint bounds

The arguments in this section apply to \(V=\phi_N\), and their coarse comparisons also apply to the exact fractional-cutoff potential used in Section 4.

For endpoints a and a proposed peak Y define

\[
 J_a(Y)=nV(Y)+2\sqrt{2/v}\int_a^Y\sqrt{V(h)-V(Y)}dh.
\tag{3.1}
\]

The pointwise square inequality shows that every path with that peak has action at least J_a(Y). At an interior minimum of J_a, differentiation gives

\[
 n=\sqrt{2/v}\int_a^Y[V(h)-V(Y)]^{-1/2}dh.
\tag{3.2}
\]

The rising energy solution \(\dot h=\sqrt{2v[V(h)-V(Y)]}\), reflected at its peak, has precisely this duration and action J_a(Y). The minimum exists: J_a(a)=nV(a) is too large, and J_a(Y) tends to infinity as Y tends to infinity. For the exact fractional potential, the derivative condition uses the one-sided derivatives, whose strictly negative factors multiply the same continuous bracket; this is the audited energy argument.

For fixed a, or any a that is a fixed power of L, a shifted Kepler trial gives action O(F). Kinetic coercivity and nV(Y) then imply Y=Theta(H). The same conclusion holds for a=H epsilon, epsilon=L^{-E}, using the regularized Kepler trial. For \(\phi_N\), convexity of the action functional gives a unique minimizer, symmetric about its midpoint and strictly concave in physical height in its interior.

For \(h\le Y/2\),

\[
 V(h)-V(Y)\asymp\log h/h,
\]

uniformly once h_b is fixed large. For \(h\in[Y/2,Y]\), it is comparable to \((L/Y²)(Y-h)\). These give endpoint action bounds

\[
 \int_{\{h\le a\}}\left[\dot h²/(2v)+V(h)\right]dt
       \le C\sqrt{a\log a},\qquad h_b\le a\le Y/2.
\tag{3.3}
\]

The corresponding reciprocal-height integral obeys

\[
                         \int_0^n\frac{dt}{h(t)}\le Cn/H=C M_0.
\tag{3.4}
\]

To verify the possible small-h issue in (3.4), split the height integral at a=Y/L^C for any fixed C>2. Above a, \(\log h\asymp L\), giving O(sqrt(Y/L)) by the beta-integral endpoint comparisons. Below a, the bound \(\log h\ge\log h_b>0\) gives O(sqrt a), also O(sqrt(Y/L)); more sharply the integral is O(sqrt(a/log a)). The peak part is integrable by the square-root estimate.

For \(h_b\le a_1\le a_2\ll H\), evaluating (3.1) at the two minimizing peaks yields

\[
 0\le\mathcal A_{a_1}(n)-\mathcal A_{a_2}(n)
 \le2\sqrt{2/v}\int_{a_1}^{a_2}\sqrt{V(h)}dh
 \le C\sqrt{a_2\log a_2}.
\tag{3.5}
\]

Both minimizing peaks are above a_2; all endpoint ranges used here satisfy that condition. Thus changing a fixed lower endpoint to h0=L^A costs only a fixed power of L, and changing it to H epsilon costs O(F sqrt epsilon).

## 4. Coefficient lower bound with tunable normalized rows

Fix K and set

\[
 B=K+3,\quad \eta=L^{-B},\quad A=4B+10,\quad h_0=L^A,
 \quad N=K+3.
\tag{4.1}
\]

Use the exact fractional row cutoff \(u=(1-2\eta)h\), its root \(V_\eta(h)\), and its q moment \(N_\eta(h)\). All constants in the imported lower audit are uniform when eta tends to zero: the only cutoff factor is 1-2eta, eventually in [1/2,1]. In particular,

\[
 V_\eta(h)\asymp\log h/h,\quad
 -V_\eta'(h)\asymp\log h/h²,\quad
 N_\eta(h)\asymp h,\quad |N_\eta'(h)|\le C\log h.
\tag{4.2}
\]

Derivatives at cutoff junctions are one-sided. Let its exact duration-n energy-minimizing arch have peak Y=Theta(H), energy lambda=V_eta(Y), and signed momentum theta. Reparameterize by \(dt/dj=N_\eta(h)/\alpha\); its real macro duration is Theta(M0). Round that duration to an integer M and sample the symmetric arch at the M slots as in the approved audit. The energy identity is unchanged and

\[
 |\theta_j|\le C\sqrt{L/h_j},\quad
 |\theta'|\le CL/h_j,\quad |h''|\le CL².
\tag{4.3}
\]

At each nonpatch slot independently sample the full row proportional to

\[
 \chi_{h_j}(q)w(e,q,d)e^{\lambda e+\theta_jd}.
\]

Its normalization, means, and centered mgfs have the same bounds as in the audit:

\[
 R_j=1+O(L^{3/2}/\sqrt{h_j}),\quad
 \mathbb E d_j=(v/\alpha)N_\eta(h_j)\theta_j+O(L²),
\]
\[
 \mathbb E e_j=N_\eta(h_j)/\alpha+O(L^{3/2}\sqrt{h_j}),
\tag{4.4}
\]

and centered log mgfs are at most \(Cz²h_jL\) for \(|z|\le c/\sqrt{h_jL}\), or \(Cz²h_j²\) for length \(|z|\le c/h_j\). Their proof only uses (4.2), the small tilts, and the imported analytic transfer; no precision is lost when eta changes.

Remove r=M^{3/4}+O(1) central slots, with the parity making their deterministic edge heights equal. Use the left prefix and the independent right complementary suffix from the two fixed seeds. Require the stronger tube

\[
                         |E_j|\le\eta h_j/10.
\tag{4.5}
\]

Below Y/2 the cumulative variance is at most \(CLh^{3/2}/\sqrt{\log h}\), while deterministic drift mismatch is at most

\[
 CL²\sqrt{h/\log h}+Ch/M=o(\eta h).
\]

Bernstein at scale eta h has exponent at least

\[
 c\eta²\sqrt{h\log h}/L
 \ge cL^{A/2-2B-1}\sqrt{\log L}
 =cL^4\sqrt{\log L}.
\tag{4.6}
\]

The quadratic Bernstein regime applies because its threshold times the maximal subexponential scale divided by the variance is O(eta sqrt(log h/L)). Near the peak the exponent is at least \(c\eta²F/L\), again much larger than L. Consequently the union over M=exp(O(L)) boundaries succeeds with probability tending to one. Every retained q is at most (1-2eta)h+1 and is legal under (4.5).

Keep also the original high-probability bounds

\[
 |X-\mathbb EX|\le LH\sqrt M,\qquad |\Delta|\le L\sqrt{nL}.
\tag{4.7}
\]

The total degree bias is still O(HL). The missing central degree divided by rY tends to \((1-m_*)/\alpha\); rounding, seeds, and fluctuations are negligible relative to rY. The exact integer patch from the approved audit therefore applies without alteration, with a fixed positive legality margin at q=(1-m_*)Y[1+o(1)]. It enforces both the exact total degree and exact final height and costs

\[
                 O(rL+ML^3/r)=o(M_0/L^K).
\tag{4.8}
\]

This bound holds for every fixed K because M grows exponentially in L. The two seeds cost a fixed power of L. The injection argument is exactly the audited one: patch locations are fixed, deletion recovers the outside marked data, and every fractional factor is at most one.

All formerly o(M) analytic losses now have explicit adequate rates:

- Row normalizations: \(O(ML^{3/2-A/2})=o(M_0/L^K)\)
- Interior integration by parts using (4.3),(4.5): \(O(ML\eta)=O(ML^{1-B})=o(M_0/L^K)\)
- Central boundary terms: \(O(rL\eta)\)
- Removing the missing central tilt/action: \(O(rL)\)
- Stieltjes quadrature: \(O(L²)\)
- Macro-duration rounding and degree-mean bias: included in the exact patch; their deterministic action corrections are fixed powers of L
- Negative logarithm of the retained probability: o(1)

It follows that

\[
                  D_n\le\mathcal A_{V_\eta,h_0}(n)+o(M_0/L^K).
\tag{4.9}
\]

Compare this minimum with the \(\phi_N\) arch having endpoints h0. Set a=H L^{-C}, C=2K+8. On h>=a, (2.3), the cutoff shift, and the derivative of the explicit truncation give

\[
 |V_\eta(h)-\phi_N(h)|\le\frac C h
 \left[\eta L+\frac{(1+\log L)^{N+1}}{L^{N+1}}+n^{-c}L^{c'}\right].
\tag{4.10}
\]

Its integrated contribution is bounded by (3.4), hence is o(M0/L^K). Below a, both potentials are bounded by C log h/h, and integration along the phi_N arch gives O(sqrt(a log a))=O(F L^{-C/2})=o(M0/L^K). Finally (3.5) replaces endpoint h0 by hb at a fixed-power-of-L cost. Therefore

\[
                         D_n\le\mathcal A_N(n)+o(M_0/L^K).
\tag{4.11}
\]

## 5. Exact convex-potential calibration with soft endpoints

Keep N=K+3 and set

\[
 \epsilon=L^{-E},\quad E=2K+8,\qquad \delta=L^{-K-2},\quad u=y+\epsilon,
\]
\[
 U_n(y)=\frac nF\left[\phi_N(Hu)-\frac{\alpha\delta}{Hu}\right]
       =\frac{\alpha}{Lu}\,[k_N(\log(Hu))-\delta].
\tag{5.1}
\]

For fixed R and all sufficiently large n, on 0<=y<=R,

\[
 U_n(y)\asymp u^{-1},\quad -U_n'(y)\asymp u^{-2},\quad
 U_n''(y)\asymp u^{-3},\quad |U_n^{(j)}(y)|\le C_j u^{-j-1}.
\tag{5.2}
\]

These follow from (2.4) and \(\log(Hu)=(2/3)L+O_E(\log L)\). The same potential is positive decreasing and convex on the whole half-line after n is large, since Hu>=H epsilon tends to infinity.

Let y_n be the duration-one action minimizer with endpoints zero for

\[
                  \int_0^1[y'^2/(2v)+U_n(y)]dt.
\tag{5.3}
\]

The direct method gives existence: kinetic coercivity gives a uniform H¹ bound for every minimizing sequence and uniform convergence in one dimension. Convexity gives uniqueness. The variational inequality for nonnegative test variations gives y_n''<=vU_n'(y_n)<0 in distributions, so concavity and the endpoint values force strict interior positivity; the Euler equation then gives \(y_n''=vU_n'(y_n)<0\), symmetry, and a single peak. A Kepler trial has bounded action because U_n(y)<=C/(y+epsilon)<=C/y. Kinetic coercivity and the lower potential bound at the maximum show its peak belongs to a fixed compact subinterval of (0,infinity). Choose R above this compact interval and large enough also for the first-hit estimate.

Its energy relation and (5.2) give uniform reciprocal-height control:

\[
 \int_0^1\frac{dt}{y_n(t)+\epsilon}\le C.
\tag{5.4}
\]

Indeed, if Y is its peak, then

\[
 U_n(y)-U_n(Y)\ge c\left[(y+\epsilon)^{-1}-(Y+\epsilon)^{-1}\right].
\]

The rising reciprocal-height integral is bounded by a constant times

\[
 \sqrt{Y+\epsilon}\int_0^Y
     (y+\epsilon)^{-1/2}(Y-y)^{-1/2}dy\le C.
\]

All required derivatives grow only as fixed powers of L. For example,

\[
 |y_n'|\le C\epsilon^{-1/2},\quad
 |y_n''|\le C\epsilon^{-2},\quad
 |y_n'''|\le C\epsilon^{-7/2}.
\tag{5.5}
\]

Define

\[
 p=-y_n'/v,\quad A=p'=-U_n'(y_n)>0,\qquad
 J(A)=\min_{0\le y\le R}\{Ay+U_n(y)\},
\]
\[
 g(1)=0,\quad g'=vp²/2-J(p'),\qquad f(t,y)=g(t)+p(t)y.
\tag{5.6}
\]

Strict convexity places the minimizing y in J(p'(t)) exactly at y_n(t), including the permitted boundary at t=0,1. Consequently

\[
 -f_t+vf_y²/2=J(A)-Ay\le U_n(y)
\tag{5.7}
\]

for every y in [0,R]. Integration by parts, using y_n(0)=y_n(1)=0, gives the exact identity

\[
 f(0,0)=\int_0^1[y_n'^2/(2v)+U_n(y_n)]dt.
\tag{5.8}
\]

Thus there is no perturbative Legendre-minimum error at any order. The bounds (5.5) and \(0\le J'(A)\le R\) imply \(\|f\|_{C²}\le L^P\) for some fixed P=P(K). The constrained Legendre minimum is C¹ at the boundary transition; this is sufficient for g'' and the C² Taylor bound.

Let A_epsilon be the unperturbed physical phi_N action with endpoints H epsilon. Evaluating the unperturbed functional at y_n and using (5.4) gives

\[
                    Ff(0,0)\ge A_\epsilon-CM_0\delta.
\]

The reverse inequality Ff(0,0)<=A_epsilon is immediate by using its minimizer. By (3.5),

\[
           Ff(0,0)=\mathcal A_N(n)+O(F\sqrt\epsilon+M_0\delta)
                  =\mathcal A_N(n)+o(M_0/L^K).
\tag{5.9}
\]

## 6. Uniform transformed-row contraction and the coefficient upper bound

Use the exact transformed kernel

\[
 w(e,q,d)\exp\{F[f(k/n,h/H)-f((k+e)/n,(h+d)/H)]\}
\tag{6.1}
\]

on legal states 1<=h<=RH, q<=h, and k+e<=n-1. Put \(\gamma=F/n\), \(\beta=F/H\), so beta²=gamma and gamma H=L.

Choose a fixed tail exponent T0 larger than P+2, increasing it if needed. On e<=H L^{T0}, |d|<=sqrt(H)L^{T0}, the C² Taylor error in the exponent is bounded by n^{-1/3}L^{P'} for a fixed P'. The linear tilts are

\[
                         s=-\gamma f_t,\qquad \theta=-\beta p.
\]

By (2.1),(5.7), with r=h+H epsilon,

\[
 r\Psi(s,\theta)
 \le\frac{r\gamma}{\alpha}U_n(h/H)+n^{-1/3}L^{P''}
 =k_N(\log r)-\delta+n^{-1/3}L^{P''}.
\tag{6.2}
\]

The legal cutoff q<=h is only enlarged to the fractional cutoff at r for an upper bound. All analytic tilts and transfer-amplitude changes are n to a negative fixed power times fixed powers of L. Since r>=H epsilon, the row-gap lemma (2.6) applies. Including the Taylor factor, every good-step row has mass at most 1-c delta.

The discarded steps are o(delta), uniformly. The full transformed exponent is bounded by

\[
                 C\gamma L^P e+C\beta L^P|d|.
\]

For e>H L^{T0}, a fixed sufficiently small extra positive degree tilt in the common analytic neighborhood bounds the sum by exp[-cH L^{T0}+CH]. For |d|>sqrt(H)L^{T0}, use both signs with extra height tilt theta0=c L^{T0}/sqrt(H). The root expansion bounds its logarithm by

\[
 -cL^{2T0}+C_Rc²L^{2T0}
      +O(L^{P+T0+1/2}+L^{P+1}+L).
\]

Choose c sufficiently small after R, and then T0>P+2. Cubic analytic errors are n^{-1/3} times a fixed power of L. The resulting bound is exp[-c' L^{2T0}]. These estimates sum unrestricted destinations and therefore cover every omitted legal step. The whole transformed row is at most

\[
                               1-c_0\delta.
\tag{6.3}
\]

The positive Neumann sum is bounded by 1/(c0 delta), whose logarithm is O(log L). The terminal factor is exactly the imported \(\rho^{n-1-k}t_*^{1-h}\). Since g(1)=0 and all f derivatives are fixed powers of L, its product with the terminal calibration factor is uniformly bounded: the corrections to log rho and -log t_* are O(gamma L^P) and O(beta L^P), respectively, and tend to zero. The initial height correction is beta p(0)=o(1). Hence

\[
                    D_n^{[\le RH]}\ge Ff(0,0)-O(\log L).
\tag{6.4}
\]

Choose the fixed R also so that the imported first-hit exponent R²/(4D0) exceeds the limiting action C by a fixed amount. The unconstrained contribution is then exponentially smaller than the confined bound; adding it changes (6.4) only by an exponentially small logarithmic error. Therefore

\[
                         D_n\ge\mathcal A_N(n)+o(M_0/L^K).
\tag{6.5}
\]

Combining (4.11) and (6.5) proves (1.4).

## 7. What this does and does not settle

All errors formerly controlled only at o(M0) have explicit tunable rates. In particular:

- the critical head mass is retained; it is not replaced by endpoint mass
- fractional cutoff interpolation requires no nonexistent smoothness at integer knots
- every sampled block is legal on a quantitatively high-probability event
- both integer constraints are repaired exactly, with sub-inverse-log cost
- the upper calibration matches the full smooth-potential action exactly
- row slack is quantitative, not qualitative
- endpoint softening and fixed-core choices have explicit errors below the target scale

A rigorous finite-order expansion and inversion of the scalar action, provided separately in `action-expansion/`, now turns this reduction into the all-finite-orders logarithmic hierarchy. The hierarchy concerns only the dominant n^{1/3} times logarithmic sector of log coefficients. It leaves every multiplicative-prefactor question open.
