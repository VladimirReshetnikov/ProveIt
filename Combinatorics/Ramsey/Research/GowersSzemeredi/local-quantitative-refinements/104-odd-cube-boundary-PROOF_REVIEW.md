# Proof review and non-claims

This is a drafting-stage internal audit, not an independent referee report or a
proof-assistant certificate. The general arguments are in `article.tex`.

## 1. Optimal deficit comparison

Every cube is parametrized by k+1 star values in A. Failed cubes are partitioned
by their first failed nonbasic subset, ordered by cardinality. Its predecessor
is in A. The bad ternary triple and k-2 original star values determine the one
missing star value with coefficient one. This is an injection, not an assumption
that all tested vertices are independent. It works without torsion restrictions.
Punctured cyclic groups show optimality of 2^k-k-1.

## 2. Odd-order complement identity

The finite census distinguishes 12 rank-three parallelograms, 56 unimodular
four-tuples, and two determinant-two parity tetrahedra. Odd order is used only
to invert the determinant-two maps. The exact fourth-order occupancy correction
is N5 + 5 N6 + 15 N7 + 35 N8; N8 is C3(R). Replacing the entire correction by zero
would lose the crucial cancellation.

The signed energy identity is exact. The inequality
r^4-C3(R) <= 4r(r^3-E(R)) has the direction needed to turn its negative coefficient
into the remainder (12h-140r)(r^3-E(R)). This coefficient is positive when
r/h < 3/35. For coset holes, a unimodular basis among any five labelled vertices
forces the entire cube into the coset, so all intermediate occupancy corrections
vanish. At the endpoint r/h=3/35 only the inequality, not its equality
classification, is claimed.

## 3. Odd-quotient boundary

For an outside difference t with quotient q, the cross count is d_q+d_-q.
The fact q != -q gives c_t <= s. The capacity c_t+2z_t <= 2s does not require
odd order. Their combination proves the secant bound.

Induction is legitimate because the sufficient radii alpha_k decrease and the
intersection outside sets are no larger than D; an empty intersection is trivial.
The quotient-fiber pair sum gives P. The inside and outside correlation sums are
retained until their cancellation; replacing both prematurely by s^2 loses the
sharp coefficient. The joint J remainder yields the energy remainder without
assuming E(D) is supported inside H.

Equality classification uses a_k > 0, hence a strict ratio. It first forces P=0,
then the exact one-fiber formula forces maximal energy/cube count for D. The
coefficient is sharp already in the previously known singleton ternary family;
the new result is the matching general upper bound and its quantitative inverse.

## 4. Cubic profile

The exact normalized mixed polynomial was expanded symbolically. The bound
F(delta-y,y)-F(delta,0) <= -(7/2) delta y holds on the entire interval
0 <= y <= delta <= 1/50. Here h/n = 1+x-y, not 1+delta, except in the pure-hole
case. The nearby subgroup alone needs odd order; the ambient quotient may have
two-torsion because the unrestricted exterior bound is used in this proof.
The coefficient (12h-140r)/n exceeds 9 in the interval.

The quantitative nested-coset conclusion requires g <= delta^3/100. It makes
r/n >= delta/2 and the hole energy deficit small enough to apply rounding inside
H. The final approximation is to C minus an actual subcoset of C.

## 5. Higher-dimensional profiles

The second-Bonferroni hole bound uses pairwise independence only. The explicit
eta_k includes alpha_k/2 to keep all equality arguments strictly within the
boundary radius. The normalized expression m-r = n(1-delta) is exact.
The boundary polynomial is increasing in the outside fraction y on the stated
interval. Its maximum occurs at pure addition, while the positive hole penalty
rules out deletions in an equality case.

For k=4 the improved interval r/m <= 1/49 is verified by an exact polynomial
and an exact rational endpoint comparison, not floating-point sampling.

## 6. Rounding

The appendix reproves the 3/2 difference-set argument and the exact local energy
comparison. The coarse distance is <3/5, which excludes the larger root of
delta(1-delta)=epsilon. The resulting <1/50 distance implies uniqueness via the
n/3 two-coset argument. The inverse boundary theorem uses majority intersection
to put the rounded coset inside the original occupied outside fiber.

## 7. Scope and remaining obligations

Historical priority beyond the compared source is not certified. The radius
endpoints are sufficient, not asserted optimal. Sharpness means exact equality
along realizable distances tending to zero, not an exact answer at every real
or fixed-cardinality distance. No general complex-function phase theorem, mixed-
torsion boundary inverse theorem, or improved global progression bound is claimed.

No new result is Lean-checked. General mathematical proofs do not rely on the
finite tests. Exact test receipts, clean compilation, and rendered-page inspection
are additional safeguards, not substitutes for independent review.
