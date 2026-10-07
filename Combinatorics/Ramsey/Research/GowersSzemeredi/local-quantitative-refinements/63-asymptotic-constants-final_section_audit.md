# Independent audit of bounded-norm and localization sections

The section filenames in this review refer to the modular drafting sources, which are incorporated in the single delivered TeX article. Initial proof-note reviews were supplemented by the final section and integration audits.

This is an internal review by a second AI researcher. It is not external peer review, Lean verification, or a publication-priority claim. The review covered `sections/bounded_norm.tex` and `sections/localization.tex` as present during manuscript assembly on 7 October 2026.

## Overall finding

No mathematical gap was found. The bounded-norm statements have the stated quantifiers, the localization energy normalization is consistent, and the positive-cover interface retains all required powers of the group order and cell-size upper bound. The finite localization theorem explicitly includes the width hypothesis needed by its geometric cover.

## Bounded-norm section

1. **Pointwise constraint.** Both three-variable expressions are separately affine. Their vertex maxima are one, including the `u=-w` case. Averaging produces `1+R(2h) >= 2|R(h)|` with the correct signs.
2. **Squaring and averaging.** `1+R(2h)` is nonnegative, so squaring is valid. For odd order, doubling is bijective and `E R=(E f)^2=0`; the result is exactly `1+S >= 4S`. This proof is simpler than the initially proposed quadratic-potential formulation and fully sufficient.
3. **Even-order obstruction.** Every finite abelian group of even order has a nontrivial character into `{−1,1}`, which is centered and has every Gowers norm equal to one.
4. **Finite-order correction.** Extreme points of the centered cube polytope have exactly one zero coordinate and equal numbers of `+1` and `−1` coordinates; an all-boundary point is impossible when `N` is odd. Thus `E f² <= 1−1/N`. The slack at zero is `(1-r)(1+3r)`. Its concavity makes the smaller endpoint value `4/N−3/N²` a valid lower bound on the entire allowed interval, and division by `N` yields the exact stated correction.
5. **Sharpness example.** The cyclic function with one zero and two consecutive constant-sign blocks has `R(0)=1−1/N` and `R(h)=1−4h/N` for `1<=h<=(N−1)/2`. The count of negative nonzero products is `2h−1`, with exactly two zero products. Summing the squares gives `1/3−4/(3N²)+1/N³`.
6. **Scope of equality.** The text correctly asserts sharpness over all groups of a specified order via the cyclic example, without asserting attainment on every group or classifying all equality cases.
7. **Compact groups.** Surjective doubling preserves normalized Haar measure. Boundedness makes the applications of Fubini valid. The circle square wave has the displayed triangular autocorrelation and achieves `1/3`.
8. **Defect identity.** The product factors are both nonnegative. The stated probability bound is a direct application of the nonnegative expectation identity and has the correct `epsilon/(ab)` normalization.

## Localization section

1. **Cube normalization.** `C_r(u)=N^(r+1)||u||_{U^r}^{2^r}` agrees with the unnormalized sum over one base and `r` increments. The quotient always retains `M U^(k+2)` for `(k+1)`-cubes.
2. **Face integral.** The positive-orthant kernel integral is `2 t^(r+2)/(r+2)!`. Inclusion–exclusion over nearest faces produces the stated powers of two and factorials. The width assumption `w<=ell/2` makes contributions from opposite faces vanish, including the tie case.
3. **Face grouping.** Multiplication by the face density cancels the dimension-dependent factorial. Grouping by the union of fixed and excluded coordinates leaves `u^(k−t+2)(w−u)^t`, hence the positive remainder in the exact identity. All terms vanish at `u=0` when required.
4. **Lattice rounding.** The target coordinates are integers; therefore the absolute-value argument is affine on each unit interval of a center coordinate. The positive-part square is convex there, so coordinatewise mean-preserving rounding increases the expected kernel. The rounding kernel is independent of the target, and the endpoint masses are exactly one-half.
5. **Recentring.** Defining `f_epsilon^c(x)=f_epsilon(x−epsilon·c)` and `tau_c(b)=tau(b+c)` makes `F^c(b)=F(b+c)` exactly, without an omitted phase or translate.
6. **Window count.** A cube with increment vector `b` has integer span `||b||_1`. Its embedded span is `M||b||_1<N`. Exactly `N−M||b||_1` windows of `N` consecutive residues contain it. `M>=3` also guarantees the complementary gap cannot produce an additional containing arc.
7. **First Cauchy–Schwarz.** There are `NM` windows. Thus `M²E_c <= NM sum_t sum_b |F_t^c(b)|²`, or equivalently the latter double sum is at least `(M/N)E_c`. The set of short integer increments embeds injectively in `G^k` because `2w<N`, so extension of the domain introduces no multiplicity error.
8. **Polarization.** For each monomial indexed by `J`, only vertices with support contained in `J` occur. The polynomial of degree `|J|+1` undergoes differences in the variables `b_i` for `i in J`, together with the extra variable `y`. The result is exactly `y product_{i in J} b_i`; all factorials are invertible under the explicit assumption `N>k+1`. Expanding the square with second base `s−y` gives the phase `e_N(−y tau_c(b))`, matching the stated twist.
9. **Mixed Gowers–Cauchy–Schwarz.** The unnormalized mixed cube sum has `k+2` averaging variables. Each of the `2^k` vertex functions appears twice, so the exponent is `1/2^k` on each individual cube sum. The group-order powers cancel correctly. Hölder in the windows, followed by selection of one of the `N` sliding partitions, gives total cube mass at least `(M/N²)E_c`.
10. **Positive-cover interface normalization.** Dividing that mass by `M U^(k+2)` leaves `E_c/(N² U^(k+2))`. Inserting `E_c>=kappa E_A/T` gives exactly the lemma's right side. There is no lost factor of `M`, `N`, or `T`.
11. **Original input coordinates.** Under `s=dt`, the phase polynomial becomes `tau(a)=d sigma(r+da)`, and the vertex functions become `f_epsilon(t)=f(d(t−epsilon·q))`, with `q=d^{-1}r`. This gives the original derivative-energy expression exactly. Undoing the selected translation and the dilation gives `phi(x)=phi_epsilon^c(d^{-1}x+b)` with unchanged degree and output common difference `d`.
12. **Finite width and cell lengths.** Under `m>3k` and `N>=m²`, one has `2<=L<N`, `3<=M<N`, and `L<=w<L+1`. Since `N` is prime, `L` does not divide `N`, so the output sizes are precisely `L` or `L+1`. The condition `L+1<=h` is equivalent to `(3k−2)h>=3k+1`, and holds for `k>=2` and for `k=1,m>=9`, exactly as stated. The two exceptional pairs are identified separately.
13. **Asymptotic denominator.** With fixed `k`, the estimates for `w/m`, `w/(L+1)`, and `(m−1)/m` are uniform in `N>=m²`. The termwise bound for `D_k` is correct because `(k-r)/(k+2-r)` decreases as `r` increases. The displayed expansion through `k^{-3}` and its reciprocal have the correct coefficients.
14. **Geometric ceiling.** For the constant input, every twist has modulus one, so the cube sum is at most the indicator cube count. The generating function `z(1+z)^r/(1−z)^(r+2)` gives the leading coefficient `2^r/(r+1)!`. The condition `N>2r|Q|` suffices for consistent integer lifts and holds uniformly eventually in the declared order of limits. Summing with `|Q|<=U` gives the ceiling `v_k` in precisely the stated quotient normalization.
15. **General positive powers.** The gamma-function simplex integral cancels the generalized face density as asserted. The residual exponent at zero is positive for `s>0`. Lattice rounding is correctly restricted to `s>=1`, the convexity range used by the proof.

## Optional editorial clarifications

- In the headline localization inequality, the intended finite meaning of `v_k/D_k+O_k(m^{-1})` is already stated immediately afterward. An equivalent form `v_k/D_k−C_k/m` could be used if a one-sided error is preferred.
- The compact-group supremum norm can be understood as the essential supremum for measurable functions; changing a representative on a null set does not affect any stated conclusion.

Neither point is a mathematical obstruction. No edits to the audited sections were made by this reviewer.
