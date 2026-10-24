# Certified propagation of nonnegativity before integer projection

## Exact theorem

Let `r_1,...,r_s` be quadratic polynomials with integer coefficients in `x_0,...,x_(n-1)`. Choose a subset `G` of coordinates and an ordered list of sign inferences covering every coordinate outside `G`. Each inference names an existing residual and one previously unproved coordinate `x_v`. Up to multiplication of the residual by `-1`, it must be the exact polynomial `c*x_v-F`, with fixed integer `c>0`, and have one of these two certificates.

1. `F` is a sum of monomials with nonnegative coefficients. Every coordinate occurring to odd exponent in such a monomial has already been proved nonnegative. Coordinates occurring only to even exponent require no sign premise.
2. `F=L^2` for an explicitly supplied affine polynomial `L` with integer coefficients. Its square is expanded and compared to the literal right side. It requires no sign premise.

Replace the natural domain by the integer domain and append, only for `v in G`, three private integer coordinates `a_v,b_v,c_v` and the quadratic residual

`x_v-a_v^2-b_v^2-c_v(c_v+1)`.

Then the augmented integer system is soluble if and only if the original natural system is soluble.

### Soundness

At an integer zero every appended guard implies `x_v>=0`, because squares and `c_v(c_v+1)` are nonnegative for every integer. Traverse the supplied ordered inference list. In case 1 each monomial is nonnegative: factors of even exponent are nonnegative independently, and factors of odd exponent have an already established sign. In case 2 a square is nonnegative. Thus `c*x_v=F>=0`, and `c>0` gives `x_v>=0`. No source-semantic theorem and no bounded search is needed for this induction. Every original coordinate is eventually nonnegative, and every original residual was retained verbatim. Projection therefore gives a zero of the natural source.

### Completeness

For every natural `x`, Legendre's three-square theorem gives an integer representation

`x=a^2+b^2+c(c+1)`.

Indeed `4x+1` is not of the excluded form `4^a(8b+7)` and so is a sum of three squares. Modulo four exactly one square is odd and two are even. Write the three squares `(2c+1)^2,(2a)^2,(2b)^2`, subtract one, and divide by four. Apply this to each guarded coordinate of any natural zero. The added witnesses are private, hence all representations can be chosen simultaneously.

## Subsequent signed coordinate elimination

Only after proving the integer conversion do we eliminate coordinates. A defining row `v-f=0` or its negative, with `f` an integer polynomial not involving `v`, permits exact substitution. Every target integer zero lifts uniquely by `v=f`; positivity of the restoring polynomial is unnecessary because the target domain is now all integers. Each retained residual remains quadratic. This is checked by exact substitution, not an asymptotic estimate. The certificate stores the elimination order and exact restoring polynomials. Reverse traversal proves the integer existence equivalence. Composing with the preceding guard theorem returns a natural source zero, even when individual intermediate restorations have negative coefficients.

## Projected source checkpoint

The frozen parent in `equations/source690/equation.json` has 690 natural variables and 606 quadratic rows. The sign certificate uses 167 guards and proves the other 523 coordinates nonnegative, including 17 exact affine-square outputs. The augmented system has 1,191 integer variables and 773 rows. Its primary monic elimination certificate deletes 303 coordinates (188 affine and 115 quadratic), leaving a quartic in 888 unrestricted integers, with 470 squared residuals and 10,156 collected monomials. Its coefficient height is 2,445,790,974,704.

A separate smaller-support contraction, in `equations/integer917`, has 917 integer variables, 499 squared residuals, 6,986 monomials and coefficient height 63,906,036. It retains more coordinates while reducing polynomial support and coefficient size.

The incoming direct-integer baseline has 1,690 variables and 21,381 monomials. The primary new variable count is 47.46% smaller and its collected support is 52.50% smaller within the direct C222 architecture. The native-coefficient family has far fewer variables and remains a different tradeoff.

The support cap is a search heuristic, not a truncation. Every selected restoring polynomial is substituted exactly, and the complete target is independently compared. A larger cap does not guarantee fewer final coordinates: changing the greedy elimination path can retain more variables. The delivered primary uses cap 16; the smaller-coefficient companion uses cap 4.

## Proof boundary

The new conversion/projection equivalence is an ordinary elementary algebra and number theory theorem formalizable in ZFC. Its application preserves the pinned natural source's already stated C222/refutation equivalence; it does not independently rebuild that arithmetic/calculus calibration. There is no consistency decision, no new Lean proof, and no global minimality claim. The exact JSON verification supplements the universal proof by checking that every inference and substitution has the literal form used in the proof.
