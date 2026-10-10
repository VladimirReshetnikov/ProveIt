# Independent review of the final geometry section

**File reviewed:** `output/polylogarithms_uniform_continuation_20261010/article/geometry.tex` as present on the final integration path, not merely the earlier research notes.

**Scope:** sharp finite signed-measure classification, its critical boundary, the real-variable Hurwitz interpolation and complete monotonicity, and the entire upper-half-disk zero arc including radius one.

## Verdict

I found no mathematical error in the final proofs. The repaired critical endpoint argument is correct and handles the atom/density cancellation that prevents using the interior sign-split argument at the boundary. The Laplace identity and all derivative inequalities in the critical deficit corollary hold for every real `x>0`, not merely positive integers. The disk-arc proof remains valid at `R=1`, including strictness and real analyticity at the endpoint radius.

One concrete typesetting typo remains in the version inspected: around line 553, `two kernel \quadratures` has an unintended control-sequence backslash. No `\quadratures` macro is defined in the final article. It should read `two kernel quadratures`. I notified root and did not edit the file.

## 1. The cancellation kernel and the interior measure

For fixed `T>0`, the kernel's bracket is `O_T(v)` at `v=0`; its possible singularity at `v=T` has exponent `a-1>-1`; and its tail has the exponential factor from `1/(exp(v)-1)`. The stated pointwise absolute convergence is therefore correct even for `a<1` and `b<=1`, provided the bracket remains combined.

The transform of the bracket is exactly

`Gamma(a)n^(-a)(1-exp(-nv))`.

For `a>=1` the bracket is nonnegative, including the `a=1` case where it vanishes on `v<T`. Tonelli is applicable. At `n=1` its contribution to the kernel is one, matching the mass of the explicit negative term.

For `0<a<1`, the absolute bracket transform is `O(v^a)` as `v->0`. On `T<=2v`, both pieces integrate to `O(v^a)`. On the remaining interval, the mean value theorem gives `C_a v T^(a-2)`, whose integral from `2v` to infinity is again `O(v^a)`. Multiplication by `v^(b-2)` makes the full absolute double integral finite precisely in the asserted interior range `a+b>1`. This proves the Fubini step and the finite signed density there.

The moment identity's last cancellation is also correct:

`-n^(-a-b)+n^(-a) sum_(j=1)^n j^(-b)
 =n^(-a)H_(n-1)^(b)`.

Using `u=exp(-T)` shifts `u^(n-1)du` to `exp(-nT)dT`, so no index or Jacobian factor is missing.

## 2. One crossing, endpoint signs, and simplicity

For `0<a<1`, the scaled `g` is negative on `(0,1)` and positive on `(1,infinity)`. At any positive level `I(T1)=C`, the ratio

`(exp(T1 s)-1)/(exp(T2 s)-1)`

is strictly decreasing when `T2>T1`. Subtracting its value at the sign-change point makes both pieces of the signed integral strictly negative. Since that ratio is less than one, this proves `I(T2)<C`; the reverse inequality for `T2<T1` is equally valid. This is a valid crossing theorem even though `I` itself need not be globally decreasing at negative levels.

At a crossing, the logarithmic derivative `-s/(1-exp(-Ts))` is strictly decreasing and negative. The same sign calculation gives a strictly negative derivative, proving simplicity. Differentiation is dominated uniformly on compact positive `T` intervals: near zero the differentiated integrand remains `O(s^(b-1))`, the singularity at one is integrable, and the large-`s` tail is exponential.

The beta identity is correct without requiring a divergent beta integral. Integrating the `a+1` expression by parts gives `a B(b,a)/(1-b)`, and subtracting `B(b,a)` gives

`integral g(s)/s ds = (a+b-1)B(b,a)/(1-b)`.

All integrals in this derivation converge absolutely for `a>0`, `0<b<1`. The three small-`T` asymptotic cases therefore have the stated positive leading constants when `a+b>1`. At infinity, dominated convergence gives `I(T)->0`, so the density is negative there. This completes the existence and uniqueness argument.

## 3. The critical density and its missing mass

At `a+b=1`, the integrable function `c(s)=g(s)/s` has zero integral and negative-to-positive signs. Since `s/(exp(Ts)-1)` is strictly decreasing,

`I(T)=integral c(s)[q_T(s)-q_T(1)] ds < 0`.

The scaled prefactor is now exactly `T^0=1`, hence `k(T)<-1` for every positive `T`.

The integrability repair is sufficient. The bound

`0 <= 1/T-s/(exp(Ts)-1) <= min(s,1/T)`

is valid for every positive `s,T`. On `(0,1)`, `s|c(s)|` is integrable. On the tail, `c(s)=s^(b-2)`; splitting at `1/T` gives `O(T^(-b))`. Since `b<1`, this controls the critical kernel near `T=0`. For `T>=1`, the majorant `|g(s)|/(exp(s)-1)` is integrable, so `I(T)` is bounded and tends to zero. Thus `k(T)` is bounded at infinity and has at worst `O(1+T^(-b))` behavior at zero.

These bounds imply, in particular, that

`integral exp(-xT) T^j |k(T)| dT < infinity`

for **every** real `x>0` and integer `j>=0`. The proof has enough control for the all-real-variable statements that follow; it is not restricted to the single measure norm `integral exp(-T)|k|`.

The extra factor `T` justifies differentiating the Laplace integral termwise. The small-`v` absolute bracket estimate becomes `O(v)`, which combines with `v^(b-2)` to give the integrable `v^(b-1)`. On large `v`, shifted gamma integrals are bounded by a constant times `1+v exp(-xv)`, and the external `exp(-v)` factor supplies convergence. These bounds are uniform when `x` stays in a compact subset of `(0,infinity)`.

Therefore the difference between the critical Laplace integral and the displayed interpolation `m(x)` is constant on the whole connected interval `x>0`. The Laplace integral tends to zero as `x->infinity` by dominated convergence. The integer asymptotic `m_n->1/a` determines the constant as `-1/a`. Using a limit along the integers is fully sufficient to identify an already constant function. At `x=1`, the resulting density mass is `-1/a`, giving precisely the positive atom `1/a` at one.

## 4. Hurwitz interpolation and complete monotonicity on all real x>0

The conversion between the two interpolation formulas is correct. With `b=1-a`, the integral in the definition of `m(x)` gives

`x^(-a)[zeta(b)-zeta(b,x+1)]-x^(-a-b)`.

The Hurwitz shift relation

`zeta(b,x)=x^(-b)+zeta(b,x+1)`

then yields `x^(-a)[zeta(b)-zeta(b,x)]`. Equivalently, the displayed convergent difference integral does this directly. Its integrand is `O(v^(b-1))` at zero and decays at infinity for every `x>0`; when `0<x<1` it is negative, which causes no problem because `m(x)` need not be positive away from its integer moment data.

The deficit is consequently

`d_a(x)=integral exp(-xT)[-k(T)] dT`.

The endpoint bounds reviewed above justify every derivative for every real positive `x`. Since `-k(T)>1` pointwise,

`(-1)^j d_a^(j)(x) > integral T^j exp(-xT)dT = j!/x^(j+1)`.

Subtracting `1/x` leaves the Laplace transform of the strictly positive density `-k(T)-1`, so the asserted strict complete monotonicity is valid. At integer `x=n`, the change of variables gives exactly the positive Hausdorff density `-kappa(u)>1`. There is no index shift error: the moments are `u^(n-1)`, not `u^n`.

## 5. Radius-one endpoint existence

For `R<1`, the expansion of `(1-Ru)^(-2)` is uniformly absolutely convergent on the support, and all moment coefficients are nonnegative. Thus `J_R(1)>=2R m2>0` is justified.

At `R=1` and `a+b>1`, the negative part of the measure is supported away from one. Its contribution remains finite; the positive part is monotone under either `R->1` or `c->1`. Both limiting procedures therefore produce the same extended integral against `(1-u)^(-2)`, which is strictly positive, possibly infinite.

At the critical line the former argument cannot be used because the negative density reaches one. The final replacement is correct:

`D=1-2cu+u^2=(u-c)^2+1-c^2`,

`0 <= (1-c)/D <= 1/(1+c) <= 1` for `0<=c<1`.

The multiplier tends to zero for each `u<1` and to `1/2` at `u=1`. Bounded convergence applies against the **total variation** of the finite signed measure. It proves

`(1-c)J_1(c) -> mu({1})/2 = 1/(2a)>0`.

Therefore `J_1(c)->+infinity`, which is exactly the missing endpoint sign needed for existence. The possible density singularity has already been absorbed by finite total variation, so no hidden estimate on that singularity is required in this step.

## 6. Uniqueness, strictness, and motion of the zero arc

The kernel ratio derivative is correctly computed:

`d/du[K_c'(u)/K_c(u)]
 =2R(c'-c)(1-R^2u^2)/(1-2Rc'u+R^2u^2)^2`.

For `R=1` it can vanish at the single endpoint `u=1`, but it is strictly positive throughout `(0,1)`. The ratio is therefore strictly increasing on the closed support in the sense needed by the separated-sign test. In particular, a positive atom at one and a negative density on the interior still give strict inequalities. The same point addresses the logarithmic-derivative argument for simplicity and the implicit derivatives `G_x>0`, `G_s<0`.

The cumulative function `H(u)=-mu([0,u])` is strictly positive for `0<u<1` in both regimes. Integration by parts includes the endpoint atom correctly: the full cumulative mass at one is zero, while its left limit jumps at the atom. Consequently the boundary term vanishes and the displayed integral in `H` is valid. At a zero it makes `c/R` an interior weighted mean, proving `0<c<R` and the angular enclosure.

With `x=Rc`, `s=R^2`, the denominators remain bounded away from zero in a neighborhood of every root, including `s=1`, because `0<x<s<=1`. The functions `u/D` and `u^2/D` are strictly increasing on the interior as claimed. Thus `x'(s)>0` and local real analyticity follow from the implicit-function theorem. The extension through zero is also justified: the already proved enclosure `0<x(s)<s` forces the geometric root to approach `(0,0)`, where `G_x=2m2>0`, so it coincides with the unique local analytic branch. No separate assumption on the limiting angle is needed.

The small-radius coefficients follow from the correctly expanded equation

`G=2m2 x-m3 s+4m3 x^2-4m4 xs+m5 s^2+O((|x|+|s|)^3)`.

The elementary `a=b=1` circle and kernel check are both correct.

## 7. Outer-order density motion

The Mellin-convolution formula has the correct normalization: in the `T` variable, multiplication of Laplace transforms by `n^(-delta)` is convolution with `T^(delta-1)/Gamma(delta)`. The absolute exponential integrability established earlier supplies a finite signed measure after convolution, so moment uniqueness applies. Local integrability at zero and continuity away from zero justify the pointwise identity. At the old crossing the convolution integrates a strictly positive function over a nonempty interval, placing the new crossing strictly to its right in the `T` coordinate and strictly to its left in `u`.

The section correctly limits this statement to `a1+b>1`, where there is an ordinary density crossing to move, and does not confuse density-crossing monotonicity with angular-zero monotonicity.

## Final recommendation

The mathematical section is ready for integration. Remove the unintended backslash from `\quadratures`. Keep the current distinctions between analytic boundary values and ordinary series convergence, formal numerical diagnostics and interval certificates, abscissa motion and angular monotonicity, and the finite-measure method versus the subcritical geometry problem. Those qualifications correspond to real differences in the proof and should remain.
