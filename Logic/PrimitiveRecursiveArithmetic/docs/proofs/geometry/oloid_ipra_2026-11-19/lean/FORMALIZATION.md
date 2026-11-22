# Lean formalization of the oloid

## Sources and status

The integration target is `VladimirReshetnikov/ProveIt` at commit
`b5d22df5b415d51a495fd447e5a44a59c54dd37d`. Its toolchain file specifies
Lean 4.32.0. The two algebra files use its `ConciseIPRA` syntax and its
`IPRADerivations` library. No copy of mathlib or of ProveIt is needed in
this archive. To check in a checkout of that revision, with its Lake
dependencies available, use the following commands (adjust `PACKET` to
the directory containing these files).

```sh
lake build IPRADerivations.Core.PolynomialImplications
lake env lean "$PACKET/ChartAlgebra.lean"
lake env lean "$PACKET/EllipticReduction.lean"
lake env lean "$PACKET/Observations.lean"
```

The local environment used to prepare the packet had no Lean compiler or
Lake. The source is supplied as an uncompiled formalization outline. No
file contains a placeholder proof. The twelve integer-polynomial
certificates in the two algebra files were checked independently by exact
expansion. The script `check_lean_certificates.py` repeats this test and
reads the formulas and certificate coefficients directly from the Lean files. The complete volume, area, and inertia proofs still require
the geometric and convergence steps below to be encoded.

## Encoded pieces

* `ChartAlgebra.lean` gives proposed proof terms for nine closed object-theory sequents.
  It clears a common denominator before stating the identities. In its
  notation, if `d>0`, the real chart quantities called `c,a,b,s` in the
  following explanation are represented by the integer numerators
  `c,a,b,s` divided by `d`. Here `a=A_y`, `b=2q B_z`, and `s` is the
  ruling parameter. Its `Q/d=2q=1+c/d` in numerator notation.
  The physical normal is `N/d`, while `W=d Q (B−A)`. The second scaled
  vector is `E=d^5 (2q)^2 sqrt(q) ∂θP`. These definitions give the three
  component equations of the surface-area vector. The factors follow
  from `sqrt(q) ∂θ(c,a,b)=(-ab,bc,-a)` for the real quantities.
  The two discrepancy polynomials are
  `c²+a²−d²` and `c²+b²−Q²`. The coefficients of their linear
  combinations are written out in the proofs. For approximate input,
  these same identities bound the residual after division by the
  homogeneous denominator. In particular, the certificates can be
  specialized without testing equality of two real names.

* `EllipticReduction.lean` specifies three closed object-theory sequents with proposed proof terms.
  At `q=x/d` it proves the three differential identities after clearing
  denominators, including the powers of `d` required for nonintegral
  `q`. The polynomials `P,D,F` have the normalizations
  `P=d^j p(x/d)`, `D=d^j (x/d) p'(x/d)` and
  `F=d^(j+2) f(x/d)`. The rational correction is
  `g=p/(s q^j)`, and `R=f/(s q^j)`. The factor three comes from
  `3 Lg=(12q²−10q+1)g+2q(q−1)(4q−1)g'`.
  The factor `b` in the certificates is the common denominator
  of the final coefficients. Cancellation on [1/4,1] uses the
  displayed positive lower bound. It does not require an integral-domain
  axiom in the polynomial proof.

* `Observations.lean` gives rational mesh programs for the seven unit
  observables. `Tag.axial` means inertia about the line of centers, and
  `Tag.transverse` means inertia about either of the specified transverse
  principal axes. The two inertia tags are for unit density.
  The source records the integrands and the precision schedule shared by
  the analytic and geometric implementations. Its types are metatheoretic
  specifications of first-order programs.

## A uniform error bound for the executable observations

Put `t=tan(θ/2)`, `v=2t/(1+t²)`, `q=1−3v²/4`, `w=sqrt(q)` and
`h=2/(1+t²)`. All rational operations have positive denominator on
`0≤t≤1`. We have `1/4≤q≤1`, `1/2≤w≤1`, `|v'|≤2`, `|q'|≤3`,
`h≤2`, `|h'|≤4`. For each solid row the sum of absolute Laurent
coefficients of `R` is below 8 and every exponent is between −4 and 2.
Thus `|R|≤2048` and `|dR/dq|≤32768`. We also have
`|d(1/w)/dq|≤4`. The Lipschitz constant of `hR/w` is bounded by

    4·2048·2 + 2·3·(32768·2 + 2048·4) < 2^20.

The other four rows satisfy the same bound directly. With root depth
`k≥1`, the lower mesh root is at least 1/2 and its error is less than
`2^(-k)`. Replacing `w` by that value in a sample changes it by at most
`2·2048·4·2^(-k)=2^(14−k)`. An `N`-cell left sum has geometric mesh
error at most `2^20/N`, and averaging does not increase the sample
error. Taking `N=2^(n+23)`, `k=n+17` gives a total error at most
`2^(-n-2)`. This bound establishes coherence even when different
requested precisions use different root approximations. The constants
were chosen for a short proof. The separate elliptic-series verification
is faster for numerical values.

## First-order implementation and outstanding derivations

Represent an integer as a difference of naturals and a rational as two
signed-magnitude parts and a positive natural denominator. Addition and
multiplication can use unreduced fractions. All comparisons are by cross
multiplication. Translate the *fixed* integrands as primitive recursive
programs. The bounded prefix sum recurses on its cell index and carries
the common numerator and denominator. A positive-denominator integer
quotient is bounded by its dividend. The mesh root is the bounded
integer square root of the truncated quotient in `meshRoot`. For an
object-level term `F(n)` representing an observational name, equality
with another name `G(n)` can be encoded as the universal closure of
`2^n |F(n+c)−G(n+c)| ≤ 1` after multiplying through by both
denominators, with the fixed shift `c` set by the error budget. This
encoding compares *specified programs*. It has no bound variable over a
real, a subset of the plane, or an integrand.

The following modules under `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations`
have relevant internal theorems in the pinned revision.

| Module | Existing theorem | Application |
| --- | --- | --- |
| `Core.PolynomialImplications` | `ZExp.derive_imp` | Closed denominator-cleared polynomial consequences in the two supplied modules |
| `Geometry.MeshBracket` | `mesh_lower`, `mesh_upper`, `mesh_unique` | Two-sided radical estimates from bounded integer operations |
| `Analysis.RiemannSumRules` | `rs_additive`, `rs_scale`, `rs_bound`, `rs_close_const` | Affine combinations and summation of a common cellwise error |
| `Analysis.RiemannRefinement` | `refine_upper`, `refine_lower` | Translate a neighbor difference bound into a coarse/fine comparison |
| `Analysis.FiniteFTC` | `ftc_upper`, `ftc_lower` | Telescope cellwise first-order approximations to each exact differential |
| `Core.Fubini` | Finite iterated sums | Exchange the order of rectangular grid sums after zeroing omitted cells |

The remaining formalization can proceed in the following order.

1. Define natural term codes for `observe`, rational grids and regular
   names. Implement the directed error predicates by pairs of natural
   inequalities. Use `mesh_lower/upper` at each fixed radical call,
   including the radical `sqrt(3)` in the chart. Use the difference of
   two squares for radical differences on guarded intervals and finite
   product differences for Laurent powers. This derives the preceding
   uniform estimate by bounded induction, in the form required by
   `refine_upper/lower`. All sums can first be lifted to a common
   denominator on both coarse and fine meshes.
2. Define the solid as the convex hull of its two closed disks. A hull
   point has a bounded description `(1−s)U+sV`, with one point in
   each disk. Disk approximations can be generated from the rational
   circle parametrization and radial scaling. Support comparisons are
   obtained by the two-dimensional Schwarz identity
   `(u²+v²)(x²+y²)−(ux+vy)²=(uy−vx)²`.
   Apply the two support equations and reflect the positive quadrant.
   For a separate geometric set name use inner/outer rational
   enclosures. The hull contains `±e_i/2` for all three coordinates and
   therefore contains the ball of radius 1/4 about the origin. An outer
   distance error `η` is absorbed by the dilation factor `1+4η`.
   This bounds the volume-weighted error by explicit polynomials in `η`
   by radial scaling on a bounding box.
3. Encode surface area by sums of triangle areas of the regular ruled
   atlas, and solid moments by upper and lower vertical columns of its
   projection. Use the longitudinal slice argument of the paper. At fixed x the positive-quadrant parameters form the closed interval with endpoints t(q₊), t(q₋), and the weight is s=(x−a)/D with D≥1. The monotone projected coordinate Yₓ has increment at least l⁴/256 across any interval of length l. Construct its inverse by minimizing the rational sample residual on a bounded mesh. The disk support gap gives uniform upper containment even at a vertical tangent. Use the independent rational voxel brackets of the paper to identify ordinary solid measurements. Substitute Yₓ by estimates on endpoint increments in each one-dimensional cell. Reorder the two remaining rectangle sums after bounding the area of cells meeting x=a(t) or x=b(t). Finally substitute x=a+sD. Mesh the area chart separately, summing the local triangle errors obtained from bilinearity of the cross product. This step establishes the geometric interpretation of the
   mesh programs in the report.
4. Expand the remaining ruling and height polynomials. The unit-interval
   integral of a fixed monomial `s^j` follows by applying finite
   telescoping to `s^(j+1)/(j+1)`. Use the explicit column coefficients
   in `Observations.lean`. For the elliptic reduction put
   `H=sinθ cosθ sqrt(q) g(q)` in `FiniteFTC`. The two endpoint terms
   vanish. On `1/4≤q≤1`, a bound for the second derivative of `H` is
   obtained recursively using the displayed rational denominator and
   `sqrt(q)≥1/2`. Thus each cell has an `O(h²)` residual, with a fixed
   rational majorant computed before the induction. In the rational
   parameter the primitive is obtained by replacing sin and cos by
   `2t/(1+t²)` and `(1−t²)/(1+t²)`.
5. For the elementary surface period, a guarded rational substitution
   evaluating the `1/q` term is given in the report. For the two
   remaining periods, define `K` and `E` by the tags in
   `Observations.lean`. Finish by symmetry, by the scaling substitutions
   `x→r x` and by multiplication by the constant density. To work at
   fixed mass, retain `V I_mass=M I_unit-density` as a cleared equation
   and use a volume lower bound from an inscribed box before dividing.
