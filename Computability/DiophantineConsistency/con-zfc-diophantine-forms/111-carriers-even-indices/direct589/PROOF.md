# Shared signs for repeated bounded intervals

## Result and boundary

At ProveIt commit `84e16e43092614bae262ca59651cb9d77e31a255`, the direct
C222 construction has a complete unrestricted-integer quartic in 604
variables, 372 quadratic residuals and 9,676 collected monomials. Its
coefficient height is 2,445,790,974,704. The exact parent is
`research/factorial-radius-output-sign-profile/raw/parent.json`; this
package includes its complete bytes and its domain certificate.

The present construction gives a quartic in **589 unrestricted integer
variables**, with **371 quadratic residuals**, **8,157 collected monomials**
and the **same coefficient height**. Every coefficient is supplied. Its
zero-existence equivalence to the pinned parent is proved below and checked
by exact polynomial identities. Composing with the pinned parent's
ordinary C222/CRT/Pell calibration gives

    ZFC proves:  (for all z in Z^589, Q589(z) != 0) iff Con(ZFC).

No K215 machine or Jones universal polynomial is used by this direct
branch. The inherited source calibration is cited, not newly formalized in
Lean or Rocq here. The new mathematics consists of a reusable sign-sharing
transformation and its exact instantiation. It does not establish a
global minimum, a new least variable count across all degrees, or an
unconditional proof of Con(ZFC).

## 1. The elementary sign lemma

For integers r,s,a,b, assume r+s=a+b, a>=0 and b>=0. Then

    (r>=0 and s>=0) iff r*s>=0.

The forward implication is immediate. For the reverse implication, if
r<0 then s>=-r>0, giving r*s<0; the same argument interchanges r and s.
This includes r*s=0 and a+b=0. No strict positivity, division, square
root, Pell equation, or power interpretation is involved.

For m pairs (r_i,s_i) with a common sum, two scalar sign conditions on
one anchor pair and one product sign condition for each other pair give
all 2m scalar signs. Thus 2m scalar conditions become m+1 conditions.
The anchor need not itself be a newly guarded pair: any independently
nonnegative pair with the same sum suffices.

## 2. Polynomial representation of a sign

Write

    T(a,b,c)=a^2+b^2+c(c+1).

For every integer n,

    n>=0 iff there exist integers a,b,c with n=T(a,b,c).

The reverse implication follows because c(c+1)>=0 at every integer c.
For the forward implication, Legendre's three-square theorem represents
4n+1 as a sum of three squares: 4n+1 is neither divisible by 4 nor 7
modulo 8. Modulo 4, exactly one of the three squares is odd. Writing that
root as 2c+1 and the other two roots as 2a and 2b gives the formula.

A product condition r*s>=0 therefore needs the single quadratic residual

    r*s-a^2-b^2-c^2-c=0

with three unrestricted integer witnesses. It replaces two scalar
residuals and six witnesses while keeping degree at most two. Although
the raw saving is three variables per replacement, the final projected
variable saving must be measured, because multiplication can prevent a
previous coordinate elimination.

## 3. The exact seven replacements

All indices below are zero-based in the **original raw body**, which has
1,259 variables and 1,177 residuals. Let x_j denote raw variable j.
Each row range consists of three consecutive literal residuals. Their
sum is exactly

    Q-r-s-1.

The same identity for an anchor pair gives equality of the two pair sums.

| New product | Anchor pair | Common Q | Product-pair rows | Anchor rows |
|---|---|---:|---|---|
| x562*x563 | (x549,x550) | x547 | 537,538,539 | 526,527,528 |
| x585*x586 | (x576,x577) | x574 | 553,554,555 | 547,548,549 |
| x593*x594 | (x576,x577) | x574 | 559,560,561 | 547,548,549 |
| x601*x602 | (x576,x577) | x574 | 565,566,567 | 547,548,549 |
| x619*x620 | (x610,x611) | x608 | 578,579,580 | 572,573,574 |
| x637*x638 | (x628,x629) | x626 | 591,592,593 | 585,586,587 |
| x123*x564 | (x91,x537) | x530 | 540,541,542 | 518,519,520 |

The first six anchor pairs are directly guarded in the new system.
For the last pair, x537 remains directly guarded. The three additional
unchanged rows 83,84,85 sum to

    x91-x94-x95-1=0.

Both x94 and x95 remain directly guarded, so x91>=1 before any source
arithmetic is interpreted. This licenses the seventh replacement just
as directly as the first six.

Exactly the following fourteen old scalar predicates are removed:

    123, 562, 563, 564, 585, 586, 593, 594,
    601, 602, 619, 620, 637, 638.

Every other old predicate, including the existing strict common-V,
paired-index-slack and factorial-lower-bound predicates, is copied
verbatim. Thus 75 predicates become 61 retained predicates plus seven
product predicates, or 68 in total. The new unprojected integer system
has 1,463 variables and 1,245 residuals. All 1,177 body residuals and all
1,259 body variable records are unchanged.

## 4. Complete zero-existence maps

From a new 68-predicate zero, keep the entire raw body assignment.
Every retained sign follows from its literal T-witness equation.
The seven source-row equalities and the sign lemma recover every one
of the fourteen omitted scalar signs. In particular, this recovery is
finished **before** the old semantic-prefix sign proof, before any
shared-frame estimate, and before any Pell, factorial, binomial, or CRT
interpretation. Choose a fresh T-triple for each recovered scalar sign.
Together with the 61 copied predicate triples this gives a zero of the
literal pinned 75-predicate parent at the same body assignment.

Conversely, a zero of the old 75-predicate parent makes each of the seven
products nonnegative. Keep the entire body assignment and the 61 retained
triples. Choose one fresh T-triple for each product, and forget the
fourteen replaced triples. This gives a zero of the new parent.

These are existential maps, not unique correspondences between the
private T-witnesses. The body coordinates are preserved in both directions.
No positivity of a power output is assumed in order to prove itself.

## 5. Projection to 589 integer variables

The supplied `support8_default/projection.json` lists 874 successive
monic substitutions. At each step an actual residual is exactly
v-f or f-v, with f an integral polynomial in still live coordinates.
Substitution into every other residual leaves degree at most two.
The defining residual and coordinate v are then removed.

An assignment to the surviving coordinates is a zero of the resulting
system if and only if, by restoring deleted coordinates in reverse order
using their supplied integral polynomials, it becomes a zero of the
whole unprojected system. Every deleted coordinate is uniquely restored;
none is discarded as unconstrained. Integrality does not require any
sign assumption because all variables range over Z.

The complete output has 589 variables and 371 residuals. If these literal
residuals are q_1,...,q_371, define the one ordinary Diophantine equation

    Q589(z_0,...,z_588) = sum_{j=1}^{371} q_j(z)^2 = 0.

The JSON residual file and the separately collected sparse coefficient
file completely specify this integer polynomial. They are not macros
calling a proof predicate or existential subroutine. The exact expansion
has 8,157 nonzero monomials and attained degree four. Over integers,
Q589=0 is equivalent to all the residuals being zero.

The actual variable gain over the pinned604 point is 15, not the raw
21-witness saving: six new product guards prevent six coordinate
eliminations that were available in the scalar parent. The support falls
by 1,519 monomials. Both figures are computed from complete expansions.

## 6. Verification and scope

`check_equal_sum.py` imports neither the builder nor the elimination
engine. It independently checks all original-body bytes, all old/new
guard rows, the seven complete equal-sum ideals, the extra x91 ideal,
all 874 inverse substitutions, every output residual, every surviving
coordinate and all 8,157 quartic coefficients. It also rejects changes
to a product coefficient, an integer restoration and a quartic coefficient.
The same code is run with normal and optimized Python; it uses no
assert statements for verification.

The optimization engine is the unchanged, hashed
`terminal_elimination.py` from the407/888 incoming archive, used only to
produce candidate substitutions. Its SHA-256 is
`73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027`.
The independent checker validates the produced mathematical certificate.

Two lower-height alternatives are also materialized: 601 variables,
383 residuals, 7,070 terms, height 964,213; and608 variables,390 residuals,
7,061 terms, height938,261. They trade variable count against coefficient
height; neither is silently substituted for the589-variable endpoint.

The final consistency equivalence composes this complete, unbounded
algebraic proof with the already reviewed ordinary theorem for the exact
pinned75 source. The present finite checks establish the displayed
polynomial transformations; they do not by themselves prove the inherited
C222/refutation correspondence, search for roots, prove Con(ZFC), or
constitute a new Lean/Rocq kernel proof.

## Further questions

1. Can common-denominator positivity be established independently of
   all scalar anchors without circular use of the shared-frame bound?
2. Can the product constraints be given a different integral coordinate
   parametrization that recovers the six lost monic eliminations?
3. Does a row-basis change expose further pairs with a common
   independently nonnegative sum, beyond the seven used here?
4. Can this local transformation be proved once in Lean and applied to
   a machine-checked complete direct C222 source theorem?
5. How does the same sign sharing perform on the lower-height retained
   source profiles and on later direct encodings with other controllers?

