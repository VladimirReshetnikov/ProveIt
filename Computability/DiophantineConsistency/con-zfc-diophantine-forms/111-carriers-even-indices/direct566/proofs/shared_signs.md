# Seven shared-sum guard replacements

This is the source75-to68 front-sign theorem used by the even-index packet.
The raw body and every guard are pinned in `source/signsharing/`.

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

