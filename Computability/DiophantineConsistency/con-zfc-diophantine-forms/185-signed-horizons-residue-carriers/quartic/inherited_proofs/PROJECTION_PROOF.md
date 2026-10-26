# Exact integer projection of the range-free anchor family

## Inputs and results

The final source is the root's frozen `anchor221/equation.json` with
`t=128+4z^2`, `K=t^4`, `F=t^K`, and the original C222 local calculus.
Its exact identity is recorded in the first projection certificate.
The five-step result in `final216/` has 216 integer variables,
155 quadratic residuals, degree 4, 7,315 collected monomials, and
coefficient height 142,238. Its residual coefficient height is 256.

The subsequent preferred affine result is
`final215/project_r0_v33/`. It has 215 integer variables,
154 quadratic residuals, degree 4, 7,364 collected monomials,
and coefficient height 13,607,065,661 before any later row-basis
or coordinate optimization. Its residual coefficient height is 95,232.
The alternative v20 elimination was also emitted and independently
checked, but has greater coefficient height.

For the small-coefficient source, the release should use these
`final216` and `final215` stages. Earlier diagnostic directories
`radical221`, `affine216`, and `radical215` were built from the
superseded t=256 variant and are not final release candidates.

The same exact projection chain has also been applied to both
sources with growth exponent K=2^20 t. The affine-growth source
substitutes this expression directly; the explicit-growth source
retains K and its defining affine residual. The results below are
before any later Pell-chart or row-basis optimization.

| Source | Projected directory | Variables | Residuals | Quartic monomials | Quartic height |
|---|---|---:|---:|---:|---:|
| anchor221, K=t^4 | final216 | 216 | 155 | 7315 | 142238 |
| final216, unit affine projection | final215/project_r0_v33 | 215 | 154 | 7364 | 13607065661 |
| anchor219, K=2^20 t substituted | affine_growth214 | 214 | 153 | 7214 | 2417851639242452488945685 |
| affine_growth214, unit affine projection | affine_growth213/project_r0_v33 | 213 | 152 | 7263 | 2417851639242452488945685 |
| anchor220, K=2^20 t retained | explicit_growth215 | 215 | 154 | 7312 | 1099511627932 |
| explicit_growth215, unit affine projection | explicit_growth214/project_r0_v33 | 214 | 153 | 7361 | 1099511627932 |

All six listed projections have independent `AUDIT.json` files
with status PASS. Their certificates pin the exact input and output
equations. The two growth-index choices are distinct arithmetic
sources; the projections themselves introduce no new semantic
assumption. All listed variables range over the unrestricted integers.

## 1. Common-radical projection theorem

Let Q_1,...,Q_m be integer polynomials of degree at most two in n
integer coordinates. Suppose v is an integer vector lying in the
kernel of the Hessian matrix of every Q_i. Choose a coordinate p
with v_p=1. Write ell_i for the directional derivative along v of
the linear part of Q_i. Suppose ell_r=epsilon is +1 or -1 for one
row r. Every vector x decomposes uniquely as

    x = y + t v,   y_p=0,   t=x_p.

The Hessian identities give the exact polynomial identity

    Q_i(y+t v)=Q_i(y)+ell_i t.

Thus the pivot equation Q_r(x)=0 is equivalent to the integer
polynomial definition t=-epsilon Q_r(y). The remaining equations
are precisely

    R_i(y)=Q_i(y)-epsilon ell_i Q_r(y)=0,   i!=r,

with y_p omitted. They remain quadratic. The forward map is
y_i=x_i-v_i x_p for i!=p; the reverse map inserts y_p=0, computes
t=-epsilon Q_r(y), and sets x_i=y_i+v_i t. These maps are mutually
inverse on the respective integer zero sets. No rational solution
or divisibility side condition is introduced.

Each system is encoded by the single sum of its residual squares.
Over the unrestricted integers this changes neither its existential
solvability nor the number-theoretic consistency calibration.

`final216/projection_certificate.json` gives all five v,p,r,
epsilon, pivot solution polynomials, retained coordinate lists,
and input/output hashes. Composing those maps proves the full
221-to-216 integer zero-set bijection. Each individual inverse has
degree at most two; no unnecessarily small degree is claimed for
their entire composition.

## 2. The additional affine relation

In the resulting 216-coordinate system, exact subtraction of
zero-based residual row5 from row18 gives

    4+12 x8+16 x9+4 x19-x20+x33=0.

Therefore set

    x33=x20-4-12 x8-16 x9-4 x19,

substitute this affine expression into all retained residuals, and
omit row5. Since row18 is retained and row18-row5 is exactly the
displayed vanishing affine relation, the omitted row follows.
The coordinate deletion and insertion are inverse integer affine
maps on zero sets. The high coefficient growth of this particular
chart is reported explicitly rather than concealed by a variable
count alone.

## 3. Independent checks and the limited obstruction

The reducer is inherited from ProveIt entry159. Its separate checker
does not import the reducer: it verifies every directional derivative
and reconstructs each projected row by the row-combination identity
above. It compares every coefficient of the expanded quartic,
checks the exact metrics, and rejects deliberate corruptions of
directions, slopes, restoration polynomials, retained coordinate
sets, domains, and digests. The affine checker verifies the actual
row relation and coordinate substitution separately.

The final216 common Hessian has full column rank modulo the checked
prime 1,000,003. Its common radical over Q is therefore zero. Its
quadratic residual rows have one affine dependence, the relation in
Section2. At final215 the quadratic row rank is154, equal to the
number of residuals, and its common Hessian radical is again zero.
These are meaningful exact obstructions to repeating these two
particular projection procedures. They are not global minimality
results and do not exclude other polynomial changes of coordinates,
nonconstant row multipliers, or a different arithmetic encoding.

## 4. Reusable maps

`coordinate_maps.py` evaluates the certified forward and inverse
maps without needing the discovery algorithm. It accepts a radical
certificate chain, optionally the affine certificate, and an integer
tuple. `lift` reconstructs a parent tuple; `project` evaluates the
forward map. On zeros these operations are inverse. On an arbitrary
tuple a lift sets the eliminated defining equations to zero and
does not assert that the other residuals vanish.

The ordinary unbounded proof of the root arithmetic source remains
an independent dependency. These finite algebraic certificates do
not establish that calibration or decide Con(ZFC).

## 5. Companion maps and precision tradeoff

Both companion families admit the same five common-radical
eliminations and the same displayed affine relation after those
eliminations. Their exact coordinate indices and restoration
polynomials are recorded separately, since later coordinate names
and positions depend on which growth-index coordinates were kept.
Use the applicable certificate pair with `coordinate_maps.py`:

* Affine-growth: `affine_growth214/projection_certificate.json`,
  then `affine_growth213/project_r0_v33/projection_certificate.json`.
* Explicit-growth: `explicit_growth215/projection_certificate.json`,
  then `explicit_growth214/project_r0_v33/projection_certificate.json`.

The 213-coordinate endpoint has no remaining constant
row-combination affine consequence and has zero common Hessian
radical. The 214-coordinate explicit-growth endpoint intentionally
retains the affine equation K=1048576 t. Eliminating that coordinate
recovers the much larger coefficient scale of the affine-growth
family. Thus retaining one variable has a measurable benefit in
coefficient height; it is not an unexamined missed projection.

Canonical equation hashes of the preferred final companion stages:

* 213 affine-growth:
  `b95151871d14a07da19b5906e23ccce71c7bc36522cd049e7b6f2a0974fa2e5d`.
* 214 explicit-growth:
  `ae39296e8083e3200bf18b705279d7cdfb5432b303045b7b9b5173333f9861ef`.

These numbers describe an explicitly constructed family and its
verified projections. They do not prove global minimality of
variable count, degree, coefficient height, or formula length.

