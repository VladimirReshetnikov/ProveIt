# A quartic with coefficient alphabet {-2, 1, 2}

## Exact result and scope

The preferred literal polynomial is `anchored/expanded_polynomial.json`.
It has **3,564 unrestricted integer variables, exact total degree four,
14,518 nonzero monomials, and coefficient alphabet exactly
`{-2, 1, 2}`**. Its constant coefficient is one. It is a sum of 3,350
squares of quadratic integer polynomials, explicitly listed in
`anchored/equation.json`.

The source is the complete 1,457-variable, 1,243-row signed-frame system
copied without modification as `anchored/source.json`, with SHA256
`7b6b5ed0759107c1e4b522fed3f9323572f7ab0c397df609911f3c70a5d24997`.
The transformation proved here is an exact, unconditional algebraic
equivalence with that literal source. The source's consistency equivalence
is supplied separately by the signed-frame and inherited direct-calculus
proofs. No new proof-checking, Pell, or source-calibration premise is
introduced by the coefficient reduction.

The result optimizes coefficient height, not number of variables. It is a
different tradeoff from the much smaller-variable quartics with large
coefficients. No global optimality or historical-priority claim is made
for converting arithmetic constraints into small-coefficient equations.
The specific contribution here is a complete coefficient collision audit
and a materialized consistency instance whose coefficients are all at
most two in absolute value.

## 1. The polynomial

Write the source variables as `x_0,...,x_1456`. Add 165 product variables
`p_0,...,p_164` and 1,942 unit variables `u_0,...,u_1941`. Every variable
ranges over all integers. Set

    U_0 = u_0 - 1,
    U_j = u_j - u_(j-1)^2                 (1 <= j <= 1941).

The new product definitions are

    T_h = p_h - x_(a_h) x_(b_h)          (0 <= h < 165).

Every ordered pair `(a_h,b_h)` is printed in `certificate.json`; the
matching residuals appear in `equation.json`. The remaining 1,243
residuals `R_i` are the transformed source rows specified there. The
single equation is

    H = U_0^2 + sum_(j=1)^1941 U_j^2
              + sum_(h=0)^164 T_h^2
              + sum_(i=0)^1242 R_i^2 = 0.                 (1)

These are fixed finite sums. They introduce no variable exponent,
variable-length family, bounded quantifier, coefficient oracle, or
unspecified function into the polynomial. The expanded JSON lists every
nonzero coefficient of (1), so it is also a complete polynomial
specification independent of any DAG interpretation.

For the fixed source used here, the coordinate count is

    1457 + 165 + 1942 = 3564,

and the row count is

    1243 + 165 + 1942 = 3350.

## 2. Why private units remove large coefficients

Ordinary gate equations such as `z-x-y=0` have small row coefficients.
Their sums of squares need not have small polynomial coefficients:
repeated uses of `x` accumulate many copies of `x^2`.

Give each linear occurrence its own unit variable. For example, replace

    z - x - y = 0

by

    z - x u_i - y u_j = 0,

with distinct, previously unused `u_i,u_j`. At any zero of (1), the unit
chain gives `u_0=1` and then `u_j=1` for every fixed index, so this is the
same equation. But the square of `x u_i` is the private monomial
`x^2 u_i^2`; it cannot accumulate with a different occurrence of `x`.

A source coefficient `c` is represented by `|c|` separate unit-marked
terms with the sign of `c`. For example,

    -4x  becomes  -x u_a - x u_b - x u_c - x u_d.

A constant occurrence is replaced by a private unit alone, so `-2`
becomes `-u_e-u_f`. Thus every transformed source term has coefficient
one or minus one. The construction pays for these units explicitly;
it does not relabel four identical monomials as four different terms.

An existing triangular gate output can stay unmasked: it occurs this
way only in its own equation. A further linear term can stay unmasked
if its variable has no other unmasked occurrence. If the same row
retains a pure product, that unmasked variable must have an index larger
than both product inputs. This last condition makes the unmasked cubic
cross term distinguishable. The anchored variant uses 152 such further
terms and therefore saves 152 units and rows relative to the 3,716-variable
unanchored construction. No original coordinate is removed by anchoring.

## 3. Product sharing and coefficient collisions

Multiplying a quadratic occurrence `xy` by a private unit would make a
cubic row and a sextic final equation. Instead, use a single shared
product variable when needed. If a source row already is exactly
`z-xy=0`, its earliest such row supplies the product wire. There are
383 distinct canonical source products. Otherwise add one new
definition `p-xy=0`; 165 are needed in the supplied construction.

Each transformed source row retains at most one unmasked quadratic
monomial. A product that occurs more than twice in the source is kept
only at its canonical source definition; other occurrences use its
wire with private units. A product occurring once or twice may retain
one occurrence in a row when that row has no other retained quadratic.
The complete construction checks that each raw quadratic monomial
occurs at most twice across all source and new-product rows.

Here is the complete collision argument for the squared polynomial.

1. **Unit-chain terms.** The seed contributes `u_0^2-2u_0+1`.
   The other unit rows contribute `u_j^2`, `u_(j-1)^4`, and
   `-2u_j u_(j-1)^2`. Their monomials are distinct except that a private
   constant occurrence may add one more copy of `u_j^2`, giving coefficient
   two. Each private unit is assigned to only one source term, so no
   third copy occurs. The seed unit is never used in a source term.

2. **Unmasked linear squares.** Each signal variable is used unmasked
   at most once in a linear term. Its square therefore has coefficient
   one. Signals and units have disjoint index ranges.

3. **Pure quadratic squares.** Each raw monomial `xy` occurs at most
   twice, always with coefficient one or minus one. Its squared monomial
   `x^2 y^2` consequently has coefficient one or two. No row contains two
   retained pure quadratics, so there is no cross-product of two raw
   quadratics that could collide with these squares.

4. **Pure cubic cross terms.** These come only from a raw product `xy`
   and an unmasked linear term `z` in the same row. The condition
   `z > max(x,y)` makes `z` the uniquely largest index in that monomial.
   Since every such `z` occurs unmasked only once, these monomials are
   all different. Each coefficient is two or minus two. A new-product
   output is larger than every source variable, so it satisfies the
   same condition.

5. **Terms containing private units.** A private unit belongs to exactly
   one source term, either `u_i` or `x u_i`. Its square has a squared
   unit factor, distinguishing it from every cross term. A cross term
   with a second unit-marked term is distinguished by its private pair
   of unit indices. A cross term with the unique unmasked linear term
   or unique raw quadratic is distinguished by its one private unit
   and by degree. Such terms contain a signal unless both factors are
   private constants; those latter products have two different unit
   variables and cannot be a unit-chain monomial.

Thus every collected coefficient is in `{-2,0,1,2}`. For the supplied
literal equation each of `-2,1,2` occurs, giving exact coefficient
height two. All its terms have degree at most four. The coefficient
of `u_0^4` is one, contributed by `U_1^2` and by no other row; hence the
total degree is exactly four. Only `U_0` has a literal constant term,
so the constant coefficient of the final polynomial is exactly one.

The full coefficient histogram is:

| Coefficient | Number of monomials |
|---|---:|
| -2 | 4,470 |
| 1 | 7,280 |
| 2 | 2,768 |
| Total | 14,518 |

## 4. Exact correspondence of solutions

Let the original source residuals be `A_i(x)`. For every old tuple `x`,
define its polynomial extension by setting every unit to one and each
new product wire to the indicated product of two source coordinates.
There is no search and no arithmetic side condition in this extension.

Suppose first that all `A_i(x)=0`. Every canonical old product wire then
equals its intended product, because its defining row is among the
source equations. Substituting the extension into each transformed
`R_i` consequently recovers `A_i(x)=0`. Every new product and every unit
row also vanishes, so `H=0`.

Conversely suppose that `H=0` over the integers. Each summand in (1) is
nonnegative, so every residual is zero. The unit chain forces every
unit to one. Each new product row fixes its wire to the prescribed
source product. The canonical old product rows are retained literally,
so they too fix their old wires to the prescribed products. Undoing
these substitutions in each `R_i=0` yields every `A_i(x)=0`.

The independent checker verifies the undoing by exact polynomial
identities, not by samples. After specializing units and new products,
it checks

    R_i = A_i + sum_(reused products xy -> z)
                    c_(i,xy) (z-xy),                     (2)

where every `z-xy` is an actual retained canonical source row and
`c_(i,xy)` is the original row coefficient. This proves both directions
without making an invalid pointwise claim that old product wires equal
their products at arbitrary off-zero inputs.

All new coordinates have been forced uniquely. Thus the source zero
set and the zero set of (1) are in bijection by coordinate projection
and its degree-two polynomial inverse. The construction preserves the
number of integer solutions, including zero, exactly. The same algebra
gives a bijection for the simultaneous row systems over any commutative
ring, and for the single sums of squares over an ordered field or over
the integers. No claim is made for the single sum-of-squares equation
over fields where nonzero squares can cancel.

All arguments here use fixed finite polynomial identities, induction
along a fixed finite unit chain, and ordered-integer arithmetic. They
are formalizable in ZFC (indeed in elementary arithmetic with the
specified finite polynomial data). Composing them with the source's
ZFC-provable consistency equivalence gives

    ZFC proves:  [there is no integer zero of H] <-> Con(ZFC).

This asserts the equivalence. It does not assert or prove either its
consistency side or its unsolvability side unconditionally.

## 5. Reproduction and independent checking

`build.py` generates the complete system, correspondence certificate and
expanded polynomial using only the Python standard library.
`verify.py` imports none of the builder. It checks all 1,243 source-row
identities (2), all 383 canonical old product definitions, all 165 new
products, all 1,942 unit equations, the collision conditions, every one
of the 14,518 collected coefficients, the exact degree, coefficient
alphabet, constant term and occurrence of all 3,564 variables.

The verifier uses ordered-pair polynomial convolution; the builder uses
an upper-triangular squaring loop. Both methods use exact Python integers.
The verifier checks the byte hashes of its supplied source and outputs.
Normal Python and optimized Python give the same receipt. Six negative
controls corrupt a unit seed, unit recurrence, product pullback,
expanded coefficient, source identity and transformed row sign; all are
rejected. These are focused finite certificate checks, not a claim to
have computed an actual accepting ZFC proof or an enormous Pell witness.

From this directory:

    python3 verify.py anchored --mutations
    python3 -O verify.py anchored --mutations
    python3 build.py anchored/source.json rebuilt --anchor-linear

The rebuilt equation, certificate and expanded polynomial are
deterministic and byte-identical to the supplied ones. No network or
third-party package is needed for these checks.

## 6. General reusable statement

The private-unit method is not specific to consistency. Given any finite
quadratic integer system, one may first share every distinct quadratic
monomial with a new product wire and mask every original linear and
constant occurrence separately. No original unmasked gate outputs are
then needed. If the source has `n` coordinates, `r` rows, `D` distinct
quadratic monomials, and total coefficient absolute-value sum `L`, this
direct version uses at most

    n + D + L + 1 variables,
    r + D + L + 1 quadratic rows.

Its final quartic has coefficient alphabet contained in `{-2,1,2}` and
the same projected integer zero set. The refinements in the delivered
instance reuse literal source products and retain collision-safe
unmasked terms, reducing those coarse counts. This is a reusable
coefficient-height compiler, not a universal bound on the number of
unknowns.
