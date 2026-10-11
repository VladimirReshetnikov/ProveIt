# Independent proof audit: two-exponent harmonic resonance

**Reviewed:** `agent_harmonic/two_exponent_section.tex`, 10 October 2026.
**Scope:** local continuation, finite Stirling specialization, every admitted affine direction, exceptional tangent directions, exact pole orders, and the all-order Stieltjes primitive. No numerical calculations were rerun.

**Conclusion:** the stated theorems are correct under their stated hypotheses. No substantive gap was found. Two brief explanatory additions are recommended below.

## 1. Local continuation and moving-divisor extraction

The Gamma-ratio and Hurwitz-tail truncations produce summands bounded by
`O(n^(1-Re(s+t)+Re(u)-L))`. At the base point this exponent is `m-L`; the stipulated choice `L>m+2` is therefore more than sufficient for normal convergence on a suitably small parameter neighborhood. Parameter derivatives only require fixed logarithmic factors. Exactly the term with index `ell=m+1` has a zeta pole there. The holomorphic remainder in Proposition `h2:prop:local` is consequently justified, locally uniformly in the shift.

For a fixed direction with `q=alpha+beta != 0`, write

\[
f(\varepsilon,u)=\sum_{i,j\ge0}f_{ij}\varepsilon^i u^j.
\]

After extracting `u^r` from `f/(q epsilon-u)`, the coefficient of `epsilon^(-h)`, for `h>=1`, is

\[
q^{-h}\sum_{i+j=r+1-h} f_{ij}q^{-i}
=q^{-h}[u^{r+1-h}]f(u/q,u).
\]

The constant coefficient excludes precisely the term `i=0,j=r+1`. The stated value of the holomorphic remainder restores this omitted coefficient and adds `Delta_(m,r+1)`. This proves all the principal coefficients and the finite part in `h2:eq:main`.

The retained `O(epsilon)` is valid for every fixed admitted complex direction, including either coordinate direction. Once the finite principal part and constant coefficient have been removed, the result is an analytic one-variable germ vanishing at zero. The statement does not claim uniformity as `q` approaches zero, and no such uniformity should be inferred.

## 2. Finite Stirling specialization

The Gauss connection formula has the stated coefficients and powers. Its regular kernel is analytic at the Mellin endpoint. At infinity it decays at least exponentially on compact subsets of `Re(a)>0`, allowing a polynomial factor at coincident exponents. Its Mellin transform divided by Gamma is entire in the order, and its value at `w=-m` is `(-1)^m m!` times the endpoint Taylor coefficient.

For sufficiently small nonzero `u`, the singular kernel has no Mellin pole at `w=-m`; the zero of `1/Gamma(w)` therefore annihilates its value. The resulting regular-kernel coefficient is a polynomial in `a` of degree at most `m+1`. The finite identity for `k^m`, the weighted binomial summation, and polynomial interpolation at positive integers then give `T_m(a,u)` correctly.

The order of restriction is essential and is explicitly preserved in the text. In particular, `L_m(a,u)` itself can have a pole at `u=0`; its combination with `C_a(u)P_m(-m,u)/u` is holomorphic. The proof uses only the latter assertion and the well-defined Laurent coefficients of `L_m`, so there is no illicit interchange at the moving pole.

## 3. Pole orders and exceptional rays

For `m=0` or positive odd `m`, the leading coefficient is nonzero because `P_m(-m,0)=zeta(-m)`. For positive even `m`, `P_m(s,0)` vanishes identically in `s`, and the first coefficient in `u` is independent of the direction and equals `(m+1)B_m/(2m)`, which is nonzero. These facts give exactly the orders stated in `h2:cor:poles`.

If `alpha+beta=0`, the affine path lies entirely in the local divisor `s+t+m-1=0`. For `m=0` or positive odd `m`, and also for positive even `m` with `r>=1`, the relevant leading numerator is nonzero near the base point. Such a path has no ordinary meromorphic pullback from which to take a Laurent finite part. Taking a limit of the displayed formula as `q` tends to zero is not a substitute. The sole stated removable case is positive even `m` with `r=0`: here joint holomorphy permits every path, including these tangent paths.

**Recommended addition:** state the preceding exceptional-ray distinction explicitly immediately after the pole-order corollary. The theorem already excludes the problematic directions, so this is clarification rather than a correction.

The auxiliary generalized-Bernoulli expression for `q_(m+1)` is correct. For a short derivation, put `g(v)=v/(1-e^(-v))`. The beta integral, initially for `Re(u)<0`, yields

\[
\frac{\Gamma(x+u)}{\Gamma(x)}
=\frac1{\Gamma(-u)}\int_0^\infty
 e^{-xv}v^{-1-u}e^{-uv}g(v)^{1+u}\,dv.
\]

Its endpoint expansion gives `q_j=(-u)_j[v^j]e^(-uv)g(v)^(1+u)`. Since `g(-v)=e^(-v)g(v)`, replacing `v` by `-v` gives the formula printed in the proof. Polynomial continuation extends it in `u`. The subsequent Bernoulli coefficient is correct: at the required odd power only the two products involving the linear terms contribute.

**Recommended addition:** include this brief justification or an explicit reference for the auxiliary coefficient identity; it is currently asserted without derivation.

## 4. All-order Stieltjes primitive

The normal slice at depth two follows from a normally convergent Hurwitz-tail sum before continuation, so it legitimately fixes the outer order first. The pole and all regular coefficients, including their Stieltjes signs and factorials, are correct.

For `ell>=0`, differentiation of `-s zeta(s+1,a)` at `s=0` gives

\[
\partial_a\zeta^{(\ell+1)}(0,a)
=(-1)^{\ell+1}(\ell+1)\gamma_\ell(a).
\]

Also

\[
\partial_a\zeta^{(j)}(-1,a)
=\zeta^{(j)}(0,a)-j\zeta^{(j-1)}(0,a),
\]

with the second term absent when `j=0`. The finite factorial-weighted sum telescopes exactly to `zeta^(ell)(0,a)`. Differentiating `h2:eq:primitive` therefore gives the stated `J_ell(a)` for every order, with no missing constant or Gamma term. The right half-plane supplies a common analytic branch in the shift throughout.
