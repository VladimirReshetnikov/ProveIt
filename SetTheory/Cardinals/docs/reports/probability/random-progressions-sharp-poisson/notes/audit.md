# Proof-audit notes

The following points were checked during development. This records an
internal audit, not independent refereeing or formal verification.

## Event reduction and parameter

The count is of progression heads, not all sliding windows. A run can
supply many raw windows but only one head for its start and difference.
Zero heads is exactly equivalent to no r-term progression. Interior head
indices are in bijection with (r+1)-APs, giving the exact mean. No
out-of-range Bernoulli coordinate is used in the case-defined event.

## Local avoidance expansion

The conditional bounds are proved by induction under maximum closed-
neighborhood probability mass delta <= 1/8. An auxiliary-event bound
controls intersections without assuming positive correlation. The
second-order statement is obtained from a finite Bonferroni quotient
expansion and explicit summation of each error. In particular:

- Ordered pair sums and unordered triple sums are distinguished.
- Products over independent pairs are charged to delta*b1.
- Weighted adjacent-pair terms are charged to delta*b2.
- Conditional pair deficits are charged to connected distinct triples.
- The diagonal term -sum(pi_i^2)/2 is retained in the factorial cumulant.

Higher connected clusters are not silently discarded by a formal power
series. The finite conditional argument bounds their aggregate effect
through the displayed remainder.

## Overlap geometry and variance

Two-site overlaps determine a bounded rational ratio of differences.
Same-difference intersecting distinct heads are incompatible. The ratio-
two pairs have O(n^2), rather than the general O(n^2 r^3), possibilities.
In a compatible triple with three distinct differences at least one pair
has reduced maximum ratio >= 3; three distinct differences cannot all be
pairwise in ratio two. This gives the power saving in the triple remainder.

The one-coordinate covariance identity is exact and uses signed
influences, including predecessor zeros. The squared aggregate projection
is corrected for its individual diagonal and for all multi-site pairs.
The incidence limit uses the bounded-variation Riemann-sum estimate
uniformly, including endpoint sites. All error powers are displayed before
being absorbed into O(r^(3/2)/n) on r = Theta(log n).

## Uniformity and optimality

The logarithmic middle band is handled before taking a supremum, preserving
exponential damping in the mean. Low thresholds use monotonicity and a
local logarithmic upper bound; high thresholds use Markov's inequality.
The exponential *quadratic* correction is not extended into the low-r
region: the global approximation uses a polynomial correction times
exp(-lambda). Mean replacement is smaller-order after damping.

The lattice maximum is first confined to a fixed compact interval of
means. Its two neighboring candidates straddle 2. Their crossing gives the
minimum periodic amplitude. The phase has all points of the unit circle
as accumulation points because its increments tend to zero while it
increases without bound.

## Remaining review burden

The proofs are written arguments. Constants in O-notation are not
numerically optimized, and an effective practical n threshold is not
claimed. The corrected remainder is not proved optimal. The global and
critical results fix p; neither a p_n-uniform statement nor a cyclic or
fixed-cardinality variant should be inferred from them.
