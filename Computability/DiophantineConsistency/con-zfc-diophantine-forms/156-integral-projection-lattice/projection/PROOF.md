# Integral projection through a nonunit affine pivot

## Scope

This component changes an explicitly supplied system of quadratic equations over the unrestricted integers. Its new contribution is a degree-preserving projection that the predecessor's unit-pivot eliminator excludes. The arithmetic and C222-to-ZFC interpretation is inherited through the exact source polynomials copied into the three profile directories. No new logical calibration is asserted.

The underlying rational-root argument is standard. The new result here is its certified use on these specific complete polynomial equations, including the resulting support and coefficient improvements. No claim of general mathematical priority or global minimality is made.

## General theorem

Let x be one variable, let y be the vector of all other variables, and suppose the integer-polynomial system contains

    a x + L(y) = 0,       a a nonzero fixed integer,

where L is affine. Suppose a different, retained equation is

    b(y) x^d + h_(d-1)(y) x^(d-1) + ... + h_0(y) = 0,

where d >= 1, all h_i and b have integer coefficients, and gcd(a,b(y))=1 for every integer y under consideration. In particular b=1 or b=-1 suffices. Replace x in every other equation by g(y)=-L(y)/a, clear its fixed rational denominators by a nonzero constant, and delete the affine pivot equation. This produces an integer-polynomial system in one fewer variable.

The coordinate projection is a bijection between the integer zero sets of the old and new systems. Its inverse inserts g(y).

**Proof.** Every old integer zero projects to a new one by direct substitution. Conversely, let y be an integer zero of the new system and set x=g(y), initially as a rational number. Every original equation vanishes at (x,y), since the pivot vanishes identically and the clearing constants are nonzero. Write x=u/v in lowest terms with v>0. Because x=-L(y)/a, v divides |a|. The retained degree-d equation, multiplied by v^d, implies v divides b(y)u^d. Coprimality of u,v implies v divides b(y), and gcd(a,b(y))=1 now forces v=1. Therefore x is integral and is an old integer zero. Uniqueness follows from the nonzero coefficient a. QED.

If every old residual is quadratic, substitution of the affine g preserves residual degree at most two. Squaring and summing the transformed residuals therefore gives a quartic or lower-degree polynomial. Removing nonzero scalar content from any individual residual preserves its zero set. Neither denominator clearing nor taking a sum of squares introduces extraneous integer zeros.

The leading coefficient hypothesis is essential. The single relation 2x-y=0 has integer projections only at even y; deleting x by rational substitution and discarding the equation would incorrectly permit odd y. A retained monic equation certifies exactly the missing integrality.

## Selected 240-variable profiles

Both selected Shared Factorial Error sources have 241 unrestricted integer coordinates x_0,...,x_240 and 178 residuals. The source residuals are indexed from zero. In each source, residual 88 is

    A - 2 x_39 = 0,

where

    A = x_103 - x_10 - x_11
        - 4(x_21+x_26+x_32+x_38+x_67)
        - 2(x_24+x_29+x_31+x_34+x_36+x_42+x_46+x_68).

Residual 23 is the independent defining equation

    x_39 - (x_11+2x_38)^2 = 0.

Delete residual 88 and replace x_39 everywhere else by A/2. The transformed residual 23 is, after primitive denominator clearing,

    A - 2(x_11+2x_38)^2 = 0.

It forces A to be even at every integer zero. Consequently A/2 is the integer square (x_11+2x_38)^2, and the inverse restoration requires no separate parity witness or new unknown.

All other residuals remain quadratic because A is affine. The deleted coordinate is removed from the ordered variable array; later indices are decremented by one. Every remaining coordinate is live in the fully collected polynomial.

| Profile | Variables | Quadratic residuals | Exact degree | Nonzero collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| shared240_balanced | 240 | 177 | 4 | 5,477 | 15,107 |
| shared240_lowheight | 240 | 177 | 4 | 9,217 | 4,512 |

The original low-height 241-variable source has 9,544 terms and height 4,512. Its new projection decreases variable count, residual count, and support while preserving degree and height. The previous 240-variable Shared Factorial Error endpoint has 21,482 terms and height 6,144; the new low-height endpoint improves both metrics at the same dimension and degree.

These two new equations are different polynomials and have different coefficient/support tradeoffs. They should not be conflated with the different predecessor built by eliminating the unit coefficient of x_103 in the same affine row.

## Factorial-free companion

The factorial-free principal source has 242 integer coordinates and 178 residuals. Its residual 88 is an affine relation with coefficient -2 at x_67. Retained residual 52 is

    x_67 - (2+4x_66+4x_66^2) = 0.

The nonunit affine substitution for x_67 is recorded completely in the certificate. The retained row forces its rational value to equal the displayed integer polynomial. Clearing fixed denominators gives 241 variables, 177 quadratic residuals, exact degree four, 5,141 collected monomials, and coefficient height 7,968.

The source's existing dimension-241 companion has 12,774 terms at the same height. The new polynomial is a substantially sparser point at that dimension; it does not reduce the minimum variable count of the direct family beyond the 240-variable construction.

## Logical composition

For each source let P_old be the sum of the squares of its residuals, and let P_new be the sum of the squares of the transformed residuals. The theorem above proves in elementary integer arithmetic

    exists y in Z^(n-1), P_new(y)=0
        iff exists x,y in Z^n, P_old(x,y)=0.

No consistency assumption is used. Composing with the source's identified C222/ZF/ZFC refutation calibration gives

    ZFC proves: [P_new has no integer zero] iff Con(ZFC).

The new transformation is ordinary mathematics formalizable in ZFC. Its exact finite implementation is checked independently; this component does not supply a new end-to-end proof-assistant derivation of the inherited calibration.

## Finite certificates

Each profile contains the exact copied source equation, the final residuals, the complete collected quartic, the coordinate map, the deleted pivot, the surviving integrality row, and every nonzero rational row-clearing multiplier. The independent checker compares all source pullbacks coefficient by coefficient using exponent-vector polynomials. It checks the monic integrality premise separately from the substitution identities.

For all three profiles, the homogeneous quadratic parts of the 177 retained residuals have rank 177 modulo the prime 1,000,003. Therefore they also have full row rank over the rationals: a nonzero constant rational linear combination cannot cancel every quadratic term to expose another affine residual. This certifies a precise limit of further affine row-combination searches for these fixed systems. It is not a bound on nonlinear consequences, changed arithmetic certificates, different projections, or global polynomial simplicity.
