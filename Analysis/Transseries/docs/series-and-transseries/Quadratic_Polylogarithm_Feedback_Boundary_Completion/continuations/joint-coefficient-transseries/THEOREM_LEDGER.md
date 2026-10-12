# Theorem ledger

## Purpose and reading conventions

This ledger records the claims proved in **Uniform Coefficient Transseries across the Polylogarithmic Order-Three Resonance**, their assumptions, dependencies, and relationship to the inspected ProveIt snapshot `8f5afd4d7565df808359f6a0c22f87f79a119bb9` (12 October 2026). It is a review map, not an independent certification or a report of completed repository intake. References below use the actual TeX labels so they remain stable if displayed numbering changes.

“Contribution” means an addition, refinement, or explicit reconciliation relative to the sources inspected for this project. It does not establish first priority in the worldwide literature. Classical ingredients include Jonquière's expansion, Gamma identities, Lagrange inversion, Fourier inversion, parabolic cylinder functions, and holomorphic implicit inversion. The article also credits prior probabilistic work on nonclassical Gaussian corrections and Gaussian–large-jump transitions.

For the main coefficient results, use the following common notation:

```text
L = log n;  s = 3 + epsilon;  lambda = epsilon L/2;
A = zeta(s-1);  u = sqrt(b^2 + 2 zeta(s));
f(z) = u - sqrt(u^2 - 2 Li_s(z));
v(r) = f(r exp(v(r)));  a_n = [r^n]v(r);
R_b = exp(-f(1)) = exp(-(u-b)).
```

The square-root branch is selected at zero. Unless a result states otherwise, `lambda` belongs to a fixed compact real interval, `b` belongs to a fixed compact subinterval of `(0,infinity)`, and `n` is sufficiently large uniformly on those sets. A truncation order `N` is always fixed independently of `n`.

Define the removable functions and exact scale by

```text
E_2(epsilon) = Gamma(1-epsilon)/((1+epsilon)(1+epsilon/2));
Z(epsilon) = zeta(1+epsilon) - 1/epsilon;
K_epsilon(ell) = Z(epsilon) + (1-E_2(epsilon) exp(-epsilon ell))/epsilon;
nu = A^2/b^2;
V = b B^2/n = K_epsilon(log B) + nu,  B > 1;
q = E_2(epsilon) B^(-epsilon)/V;
xi_m = (m-nA/b)/B.
```

At zero, `K_0(ell) = ell + 3/2`. The Fourier logarithm is `Log(-iy) = log|y| - i pi sign(y)/2`. The notation `H_a^[j]` means the `j`th derivative in the **order** `a`; it does not mean a spatial derivative. The finite correction functions are

```text
C_0(xi) = g(xi),
C_j(xi;q,epsilon)
  = (1/j!) sum_{k=1}^j S(j,k) (-q/2)^k epsilon^(j-k) H_(2k)^[j](xi),
```

where `g` is the standard normal density and `S(j,k)` are Stirling numbers of the second kind.

## 1. Exact representation and normalization

### `prop:poisson` — Exact coefficient–probability identity

**Source:** `sections/02-model-and-scale.tex`.

**Assumptions:** real `s > 2`, `b > 0`, and the quadratic germ above. Let `X_n` be compound Poisson with probability generating function `exp(n(f(z)-f(1)))`.

**Conclusion:** exactly `R_b^n a_n = P(X_n=n)/n` and `E X_n = n A/b`. The coefficients of `f` are positive and obey `[z^k]f(z) >= 1/(u k^s)`.

**Dependencies:** the branch formula, positivity of its Taylor expansion, Lagrange inversion, and the standard compound-Poisson generating function.

**Contribution and qualification:** this is a proved reduction already used in the boundary-completion predecessor, included to make the new analysis self-contained. It holds on both sides of critical feedback. It does not assert that `R_b` is the actual radius when `b < A`; the interior-fold radius then exceeds this endpoint reference.

### `lem:local` — The centered local exponent

**Source:** `sections/02-model-and-scale.tex`, especially `eq:local-exponent` and `eq:deficit-pair`.

**Assumptions:** `|epsilon| <= 1/4`, `b` in a fixed compact positive interval, small nonzero `t` with `|arg t| <= pi/2`, and the stated logarithm branch.

**Conclusion:**

```text
f(exp(-t))-f(1)+(A/b)t
  = t^2/(2b) {K_epsilon(-Log t)+nu} + O(|t|^(5/2)),
```

uniformly in the parameters and sector. The colliding Gamma and zeta terms are combined before estimation. The nonlinear quadratic feedback contributes the explicit `nu` term.

**Dependencies:** the convergent Jonquière expansion, the identity `2 Gamma(-2-epsilon) = -E_2(epsilon)/epsilon`, cancellation at zero, and a uniform square-root Taylor expansion.

**Contribution and qualification:** the uniform paired exponent is the analytic input needed for the joint coefficient theorem. Estimating its two singular summands separately would lose the claimed uniformity. The bound is a finite local remainder; it is not a description of every smaller transseries sector.

### `thm:scale` — Existence, uniqueness, and size of the scale

**Source:** `sections/02-model-and-scale.tex`, `eq:scale` through `eq:q-equivalent`.

**Assumptions:** the common compact-window hypotheses and sufficiently large `n`.

**Conclusion:** the exact scale equation has exactly one solution **with `B > 1`**. For `phi(lambda)=(1-exp(-lambda))/lambda`, continued at zero,

```text
B_0^2 = n L phi(lambda)/(2b),
B/B_0 = 1 + C_lambda/(L phi(lambda)) + O((log L)^2/L^2),
q = 2 exp(-lambda)/(L phi(lambda)) + O(log L/L^2) > 0,
```

where `C_lambda` is displayed in `eq:C-lambda`. In particular `q` is uniformly comparable to `1/L`.

**Dependencies:** the paired functions, a one-change-of-sign derivative argument in `H = log B`, and a uniform expansion around `log B_0`.

**Contribution and qualification:** this provides the exact nonlinear normalization that absorbs the iterated logarithms. The theorem does not assert uniqueness among all positive roots, nor finite variance of the underlying law. The scale remains valid through `epsilon = 0` and on either side of it in the compact moving-order window.

## 2. Finite Gaussian order-derivative calculus

### `prop:H` — Parabolic cylinder and Gamma forms

**Source:** `sections/03-gaussian-jets.tex`, `eq:H-definition`, `eq:H-cylinder`, and `eq:H-zero`.

**Assumptions:** `Re a > -1` for the defining Fourier integral.

**Conclusion:**

```text
H_a(xi) = (1/(2 pi)) integral_R exp(-i xi y-y^2/2) (-iy)^a dy
        = exp(-xi^2/4) D_a(-xi)/sqrt(2 pi),
H_a(0) = 2^((a-1)/2)/Gamma((1-a)/2),
partial_xi H_a = H_(a+1).
```

Order derivatives in the stated domain are represented by convergent logarithmic Fourier integrals.

**Dependencies:** Gaussian integrability, Gamma integration, and the parabolic-cylinder differential equation and initial values.

**Contribution and qualification:** the special-function identity and its classical analytic content are not claimed as new. The choice of argument `-xi` and Fourier branch are essential to the positive-tail sign. These kernels package the new finite moving-order corrections.

### `eq:correction` and `eq:finite-difference-approx` — Exact finite coefficient rules

**Source:** `sections/03-gaussian-jets.tex`.

**Conclusion:** the displayed `C_j` is a finite homogeneous polynomial of total degree `j` in `q,epsilon`, with coefficients given by Gaussian order derivatives. An alternative truncation uses the removable divided differences of `H_a` in its order. The identity behind both rules is `eq:stirling-generating`.

**Dependencies:** the finite Taylor coefficient rule for `(exp(epsilon z)-1)/epsilon`, Stirling numbers, and order differentiation under a Gaussian integral. The error equivalence of the two truncations is proved as part of `thm:all-orders`.

**Contribution and qualification:** the finite calculus combines moving order, noncentral location, and feedback at every fixed logarithmic order. It does not assert convergence of the infinite sum of corrections. In general the correction is not a Gaussian multiplied by an ordinary polynomial in location.

### `cor:central-corrections` — Central coefficient calculus

**Source:** `sections/03-gaussian-jets.tex`, `eq:central-C` and `eq:central-first`.

**Assumptions:** the finite correction definitions; evaluate at `xi = 0`.

**Conclusion:** every `C_j(0)` is a finite Stirling-weighted Gamma moment, with the exact constants and powers of two shown in `eq:central-C`. In particular `C_1(0)/g(0) = q(2-gamma-log 2)/4`.

**Dependencies:** `prop:H`, Gamma reflection, and the finite correction formula.

**Contribution and qualification:** the moving-order central formula is a compact extension of the prior marginal moment description. Its marginal restriction is explicitly reconciled with that predecessor below.

## 3. Uniform coefficient theorem

### `lem:fourier-tail` — Uniform Fourier domination

**Source:** `sections/04-uniform-expansion.tex`.

**Assumptions:** the common compact-window hypotheses. Let `chi_n` be the characteristic function of `(X_n-nA/b)/B`.

**Conclusion:** `|chi_n(y)| <= exp(-c_1 y^2)` for `|y| <= B n^(-1/4)` and `|chi_n(y)| <= exp(-c_2 sqrt(n))` from there to the lattice cutoff `pi B`, with positive constants independent of the moving parameters.

**Dependencies:** the uniform positive lower bound on `[z^k]f`, a truncated second-moment sum through `n^(1/4)`, the `k=1` intensity on the outer arc, and `thm:scale`.

**Contribution and qualification:** this supplies the genuinely uniform global Fourier bound requested by Q1. The proof uses positivity of the exact law; it does not extend a locally truncated exponent to all frequencies.

### `thm:all-orders` — Every fixed logarithmic order, uniformly on the lattice

**Source:** `sections/04-uniform-expansion.tex`, `eq:uniform-lattice` and `eq:all-orders-coefficient`.

**Assumptions:** the common compact-window hypotheses and an arbitrary fixed integer `N >= 0`.

**Conclusion:**

```text
sup_{m in Z} | B P(X_n=m) - sum_{j=0}^N C_j(xi_m;q,epsilon) |
  <= C_N L^(-N-1).
```

At `m=n`, the same statement is the expansion of `n B R_b^n a_n`. The finite divided-difference truncation has the same error order. Equation `eq:elementary-first` expresses the first correction in the simpler scale `B_0`; `eq:Q1-solved` gives the requested compact-location leading limit.

**Dependencies:** `prop:poisson`, `lem:local`, `thm:scale`, `lem:fourier-tail`, and the finite Stirling calculus. The proof uses a frequency cutoff of order `sqrt(log L)`, an integrable finite expansion on the core, and exact-law domination outside. Its local nonlinear remainder has size controlled by `n B^(-5/2)`, which is beyond every fixed inverse-logarithmic order.

**Contribution:** the central proposed research result: a nonlinear joint moving-order/moving-feedback coefficient theorem with all fixed corrections, noncentral locations, and a uniform remainder. It answers the compact Q1 target in the boundary-completion report, rather than merely recovering its fixed-order theorem.

**Qualifications:** the error is **absolute** over the lattice. A bounded standardized location gives a relative Gaussian conclusion because the limiting density is bounded away from zero on compact sets. Growing-location relative estimates need additional tail analysis. Constants depend on `N` and the fixed parameter compacts. The proof does not allow `N` or the bound on `lambda` to grow with `n`, and does not justify the untruncated local exponential as a globally integrable Fourier transform.

## 4. Convergent normalization, marginal matching, and outer composition

### `prop:scale-chart` — Convergent two-variable scale chart

**Source:** `sections/05-marginal-and-universality.tex`, `eq:Y-scale` and `eq:Y-equation`.

**Assumptions:** the quadratic model and compact real `(lambda,b)` sets.

**Conclusion:** `B^2 = B_0^2 Y(h,w;lambda,b)` after `h=1/L`, `w=(log L)/L`, where `Y` is holomorphic near `(h,w)=(0,0)`, uniformly along the parameter compacts, and `Y(0,0)=1`. Its Taylor series converges after physical substitution for sufficiently large `L`.

**Dependencies:** the exact scale equation, removal of the quotient at `lambda=0`, the holomorphic implicit function theorem with derivative one, compactness, and uniqueness of the large positive scale.

**Contribution and qualification:** this is an exact finite-variable analytic chart for the normalization. Its convergence must not be transferred to the coefficient correction series.

### `cor:marginal` — All marginal central coefficients as constants

**Source:** `sections/05-marginal-and-universality.tex`, `eq:critical-T` through `eq:matching`.

**Assumptions:** exactly `s=3`, `b=A=zeta(2)`, and fixed `N`.

**Conclusion:** let `T>1` satisfy `T-log T = L+5-log(2A)`, equivalently the specified lower-real-branch Lambert formula. Then

```text
R_b^n a_n = sqrt(A/pi) n^(-3/2) T^(-1/2)
            {sum_{j=0}^N D_j/T^j + O(T^(-N-1))},
D_j = Q_j(-log 2).
```

**Dependencies:** `thm:all-orders` at `epsilon=0`, the exact Lambert scale, the central Gamma formula, and the definition of the already existing `Q_j`.

**Contribution and qualification:** this is exact normalization matching and resummation of previously established marginal coefficients. The Lambert scale is exact; the coefficient expansion in its reciprocal is asymptotic. The coefficient scale and an inverse-function Lambert scale have different constants and should not be interchanged.

### `thm:universality` — Two-derivative composition principle

**Source:** `sections/05-marginal-and-universality.tex`, `eq:G-parameters` through `eq:G-leading`.

**Assumptions:** `f=G(Li_s)` where, uniformly over the family, `G(0)=0`, its Taylor coefficients are nonnegative, `G'(0)` has a fixed positive lower bound, and `G` is holomorphic and uniformly bounded on a disk extending a fixed positive distance beyond `zeta(s)`. The moving-order compact hypothesis is unchanged.

**Conclusion:** the full absolute lattice expansion of `thm:all-orders` holds with

```text
c = G'(zeta(s)),  kappa = A^2 G''(zeta(s))/c,  mu = c A;
B^2/(n c) = K_epsilon(log B)+kappa,  B > 1;
xi_m = (m-n mu)/B,
```

and precisely the same correction functions. For `v=f(r exp(v))`, the coefficient normalization is `R=exp(-f(1))`. After normalization and centering, all fixed inverse-logarithmic orders depend on the outer function only through its first two endpoint derivatives.

**Dependencies:** uniform Cauchy estimates for `G`, endpoint Taylor expansion through degree two, the intensity bound `[z^k]f >= eta k^(-s)`, and the same scale/Fourier proof as the quadratic case.

**Contribution and qualification:** this proves a sufficient nonlinear universality class beyond eventually exact linear tails. Higher endpoint derivatives can affect sectors beyond every fixed inverse-logarithmic order, so equality of full transseries is not asserted. Signed coefficients, vanishing linear coefficient, shrinking analytic margins, or arbitrary parameter-dependent families are not included. The square-root example satisfies the stated disk hypothesis by choosing a margin smaller than `b_-^2/2`.

## 5. Relative positive windows and transition profile

### `lem:kernel-wing` — Kernel tails and order derivatives

**Source:** `sections/06-positive-wing.tex`, `wing:leading-polynomial`, `wing:first-kernel-tail`, and `wing:uniform-tail-expansion`.

**Assumptions:** fixed integers `k,j >= 1` and `x -> +infinity`.

**Conclusion:** `H_(2k)^[j](x) = O(x^(-2k-1)(1+log x)^(j-1))`, with an explicit leading polynomial. In particular `H_2^[1](x) = -2 x^(-3)(1+6x^(-2)+O(x^(-4)))`.

**Dependencies:** a convergent one-sided convolution formula, Gaussian moments, an expansion uniform in a complex order disk, and Cauchy order-derivative bounds.

**Contribution and qualification:** this is the positive-tail estimate needed to convert the absolute theorem to a relative theorem. Its analytic structure is classical; the proof and uniform order differentiation are supplied for the precise application. No symmetric negative algebraic tail is asserted.

### `thm:positive-windows` — Positive windows of polynomial size in `log n`

**Source:** `sections/06-positive-wing.tex`, `wing:relative-mixture`, `wing:gaussian-window`, and `wing:power-window`.

**Assumptions:** the quadratic common hypotheses, fixed `M>0`, and `r_L -> infinity` with `r_L <= L^M`; standardized locations are actual lattice locations with `r_L <= xi <= L^M`.

**Conclusion:** uniformly, `B P(X_n=m) = (g(xi)+q xi^(-3))(1+o(1))`. For fixed `delta in (0,2)`, the Gaussian dominates up to `sqrt((2-delta)log L)`, and the power term dominates beyond `sqrt((2+delta)log L)` within the stated window.

**Dependencies:** `thm:all-orders` with a fixed `N>3M`, `q` comparable to `1/L`, and `lem:kernel-wing` for each retained correction. The absolute remainder becomes relatively negligible because its ratio to `q xi^(-3)` is `O(L^(3M-N))`.

**Contribution and qualification:** this gives a partial positive-side answer to Q2. It is not a determination of the maximal window, and does not treat growing negative deviations or macroscopic deviations. On the coefficient diagonal, these windows force feedback toward criticality rather than permit arbitrary fixed `b>A`.

### `cor:supercritical-matching` — Relative matching with the supercritical coefficient law

**Source:** `sections/06-positive-wing.tex`, `eq:supercritical-matching`.

**Assumptions:** the coefficient diagonal `m=n` lies in the positive power-dominated window `sqrt((2+delta)log L) <= xi <= L^M`, with fixed `M,delta>0` and the common compact hypotheses.

**Conclusion:** `R_b^n a_n ~ b^(s-1) (b-A)^(-s) n^(-s)` uniformly in this overlap.

**Dependencies:** `thm:positive-windows`, the scale identity, `E_2(epsilon)->1`, and `epsilon log xi -> 0` uniformly on a fixed polynomial window.

**Contribution and qualification:** this recovers the known supercritical amplitude along approaching-critical sequences. It does not replace the predecessor's fixed-supercritical theorem or reprove it on its full domain.

### `thm:wing-lambert` — Lambert location of the Gaussian–power transition

**Source:** `sections/06-positive-wing.tex`, `wing:lambert-center`, `wing:expanded-center`, and `wing:transition-profile`.

**Assumptions:** the common hypotheses, `q -> 0+`, and bounded real transition coordinate `tau`.

**Conclusion:** the larger positive root of `g(x_*)=q x_*^(-3)` has

```text
x_*^2 = -3 W_(-1)(-(2 pi)^(1/3) q^(2/3)/3).
```

For lattice locations satisfying `xi_n^2 = x_*^2+2 tau+o(1)`, uniformly on compact `tau` sets,

```text
B P(X_n=m)/(q x_*^(-3)) -> 1+exp(-tau).
```

The proof also checks lattice rounding and local realization on the coefficient diagonal by moving feedback when its compact interval contains `zeta(2)` in its interior.

**Dependencies:** `thm:positive-windows`, the exact scalar Lambert inversion, and controlled parameter differentiation of the scale for the diagonal realization.

**Contribution and qualification:** the report gives an explicit center and profile for its moving polylogarithmic family. The Gaussian–power-tail transition is a known phenomenon in probability. This theorem is positive-side only, with a bounded transition coordinate; the leading equivalent `x_* ~ sqrt(2 log log n)` alone is insufficient to locate the profile to its required accuracy.

## 6. Local reciprocal inverse endpoints

These results concern a different inverse problem. Set `alpha=s-1>0`, `y=zeta(1+alpha)-Li_(1+alpha)(exp(-t))`, and let `t_alpha(y)` be the branch positive for small positive `y`. Initially use `0<|t|<2pi`, `-pi<arg t<pi`, followed by analytic continuation on the logarithmic cover. They do not use the compound-Poisson law.

### `thm:ramification` — Minimal local ramification

**Source:** `sections/07-reciprocal-endpoints.tex`.

**Assumptions:** real `s>1`; ramification means substituting `y=w^N` for a positive integer `N` and asking whether the inverse extends holomorphically at `w=0`.

**Conclusion:** the minimal finite index is classified completely:

| Order | Minimal ramification |
| --- | --- |
| `0<alpha=p/q<1`, with `p,q` coprime | `N=p` |
| Noninteger `alpha=p/q>1`, with `p,q` coprime | `N=q` |
| Irrational `alpha` | No finite index |
| Integer `s>=2` | No finite index; logarithmic obstruction |

Thus the endpoint is unramified and holomorphic exactly at `s=1+1/m`, `m>=2`. The same classification holds for `exp(-t_alpha(y))`, the corresponding inverse of the polylogarithm.

**Dependencies:** the convergent local expansion `y=-Gamma(-alpha)t^alpha+t A_alpha(t)`, ordinary holomorphic inversion after uniformizing rational powers, and the nonzero fractional or logarithmic terms proving minimality. At integer orders the appropriate logarithmic Jonquière expansion is used.

**Contribution and qualification:** this sharpens the predecessor's noninteger local charts into an exact classification, including removable reciprocal endpoints. It is entirely local. It does not determine a global Taylor radius, assert global univalence on a new sheet, or rule out another inverse singularity at the same modulus.

### Exact reciprocal Lagrange coefficients — unnumbered subsection

**Source:** the reciprocal-coefficient subsection of `sections/07-reciprocal-endpoints.tex`, following `thm:ramification`.

**Assumptions:** `alpha=1/m`, `m>=2`, with `b_m=-Gamma(-1/m)>0` and the specified local germ `G_m`.

**Conclusion:** exact coefficient extraction formulas are supplied for `t(y)` and `exp(-t(y))`; in particular

```text
t(y) = b_m^(-m) y^m - m zeta(1/m) b_m^(-2m) y^(2m-1)
       + O(y^(3m-2)).
```

The article displays additional terms for `m=2`.

**Dependencies:** the reciprocal uniformizing coordinate and ordinary Lagrange inversion.

**Contribution and qualification:** exact local consequences of the removable endpoint, useful for independent verification and eventual formalization. Their convergent local series do not provide a global inverse-radius theorem.

### `thm:reciprocal-chart` — Reciprocal-order crossover chart

**Source:** `sections/07-reciprocal-endpoints.tex`.

**Assumptions:** fixed `m>=2`, positive `y -> 0`, `T=log(1/y)`, `alpha=1/m+epsilon`, and `tau=epsilon T` in a fixed compact real set.

**Conclusion:**

```text
t_alpha(y) = y^m U(h,r,q_ep;tau),
h = 1/T,  r = y^(m-1),  q_ep = y^m,
U(0,0,0;tau) = b_m^(-m) exp(m^2 tau).
```

Here `U` is holomorphic in the three independent small variables and on a complex neighborhood of the compact `tau` set; its Taylor series converges after substitution. The article denotes the third local variable by `q`; it is unrelated to the Fourier correction parameter. For each fixed `j>=1`, the order derivative at **fixed deficit `y`** satisfies

```text
partial_alpha^j t_alpha(y)|_(alpha=1/m)
 = b_m^(-m) (-m^2)^j y^m (log y)^j
   + O(y^m (1+|log y|)^(j-1)).
```

**Dependencies:** the convergent noninteger local expansion, consistent logarithms, explicit leading factor, and a holomorphic implicit equation with nonzero derivative `1/m` after normalization.

**Contribution and qualification:** the chart resolves the moving-order logarithmic dependence around a locally removable endpoint. Fixed-deficit differentiation differs from fixing the original polylogarithm value `zeta(s)-y`. Neither the jet index nor the compact bound on `tau` may grow in the stated conclusions.

### Q9 cut-modulus obstruction — unnumbered final subsection

**Source:** the final subsection of `sections/07-reciprocal-endpoints.tex`.

**Assumptions:** fixed real `1<s<3/2`, upper-bank continuation, and `u -> 0+`.

**Conclusion:**

```text
|Li_s(exp(u)+i0)|
  = zeta(s) + Gamma(1-s) cos(pi(s-1)) u^(s-1) + o(u^(s-1))
  < zeta(s)
```

for sufficiently small `u`.

**Dependencies:** the boundary value of the leading fractional power and the sign of `Gamma(1-s) cos(pi(s-1))` on the stated interval.

**Contribution and qualification:** this disproves the blanket extension of the predecessor's integer cut-modulus inequality to all real `s>1`. It does **not** refute its printed integer theorem, settle the exact validity range of the inequality, or determine the global inverse radius. Q9 remains a global research question with a proved local obstruction and a precise reciprocal-order caveat.

## 7. Verification and limits of the proof package

The analytic implications run from the exact model through the paired local exponent and positive Fourier bounds to the all-order theorem. The positive relative results then add kernel tails. The reciprocal inverse section is an independent analytic branch of the article. The convergent scale chart and marginal matching depend on the exact normalization but are not prerequisites for the Fourier proof.

`sections/08-verification-and-research.tex` documents the accompanying checks: finite coefficient recurrences independent of the asymptotic formula, exact finite Stirling and Gamma identities, high-precision Fourier quadrature, reciprocal inverse calculations, and cut-bank diagnostics. The code and machine-readable outputs retain their parameter grids and errors. These checks test formulas, branches, and computations; the uniform analytic bounds come from the proofs. No interval-arithmetic certification or proof-assistant formalization is claimed.

The principal limitations to retain in any abbreviated statement are: **`B>1`; compact real `lambda`; compact positive feedback; each fixed truncation order; positivity and a fixed analytic margin for composition; absolute versus relative lattice error; positive versus negative growing windows; local versus global inverse geometry; and asymptotic coefficient expansions versus convergent holomorphic charts.** The research questions in the article identify the additional analysis required to cross these boundaries.
