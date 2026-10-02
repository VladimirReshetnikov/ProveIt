# Rank-four two-attachment sector: complete exact certificate

Status: **fully proved and independently audited**. The standalone positivity
verifier passed all 89,863 inputs and 179,726 gap instances. Separate independent
audits regenerated the complete polynomial set using Hall tests, checked every
stored representative, and verified all exact SOS identities, positive weights,
and population-face coverage without importing the producer/verifier code.

## Family and coverage

Let K be a preorder core with at most eight vertices and A={a,b} a distinguished
pair such that the ordinary comparability graph of K−A has matching number at most
two. Add arbitrarily many independent vertices adjacent only to A. For each a∈A,
all incident exterior edges have one common strict orientation; otherwise two
exterior vertices become comparable by transitivity. Three nonempty neighborhood
types are possible: {a}, {b}, and {a,b}. Type populations are x1,x2,x3.

Every matching uses at most two edges incident with A and at most two edges wholly
inside K−A. Thus every resulting preorder has gamma degree at most four, whatever
the populations. The canonical Gallai–Edmonds a=2 branch of rank four has exactly
this bounded-core form (the reduction is an external input established previously).

`enumerate.cpp` enumerates every canonical quotient poset up to size eight and
all positive block-size compositions of eight. It tries every unordered marked
pair and all four common exterior orientations. Smaller cores occur after padding
with isolated vertices, which does not affect gamma. A pair is retained precisely
when its remaining six vertices have no perfect matching, equivalent to the
required matching-number bound. Every exterior type is checked for transitivity
with two independent identical copies, and the union of all legal types is also
checked. Population zero covers absence of any legal type. No legal types reduces
to the already checked finite core. Identically zero gamma4 reduces to the already
proved degree-at-most-three theorem.

Counts:

- 40,877 weighted core cases
- 32,236 cores admitting a relevant attachment specification
- 802,333 legal marked/oriented specifications
- 667,508 specifications with nonzero gamma4 polynomial
- 89,863 distinct gamma polynomials after swapping x1 and x2

The enumeration includes harmless isomorphic/weighted repetitions.

## Exact support kernel

Every gamma coefficient counts ordered **disjoint** endpoint subsets on the same
ground set, once per feasible directed matching support.

The binomial expansion has only ten columns:

`1, x1, x2, x3, C(x1,2), C(x2,2), C(x3,2), x1*x2, x1*x3, x2*x3`.

A matching support cannot contain more than two exterior vertices.

- Zero exterior vertices gives gamma(K)
- One exterior vertex adjacent only to a forces the matching edge to a, giving
  gamma(K−a), shifted by one coefficient; similarly for b
- One exterior vertex of type {a,b} gives the union of these two possibilities
  If the two orientations agree, the overlap is counted explicitly by checking
  the two possible core residual matchings; if orientations differ, the exterior
  endpoint has opposite roles in the two possibilities, so the supports are disjoint
- Two exterior vertices force both attachment vertices to be matched to them
  The coefficient is the number of feasible endpoint-role patterns on these four
  vertices, multiplied by gamma(K−A), shifted by two coefficients

`a2_polynomials.jsonl` stores a representative relation and the 5×10 coefficient
array. Orientation bit 1 means attachment→exterior; bit 0 means exterior→attachment.
`legal_types` uses bits numbered 1,2,3. The representative relation is not modified
when the coefficient array is minimized lexicographically against x1↔x2; an
independent reconstruction should make that final polynomial normalization.

## Positivity certification

The remaining ULC gaps are

`4 gamma2² − 9 gamma1 gamma3` and `3 gamma3² − 8 gamma2 gamma4`.

The universal first inequality is already known. We work with 2*gamma to obtain
integer ordinary coefficients; this multiplies each gap by the positive factor four.

Nonnegative binomial coefficients certify a polynomial on every nonnegative integer
population. For remaining cases, split each coordinate into x_i=0 or x_i=1+y_i,
y_i≥0. The eight faces cover every nonnegative integer triple. A face is certified
by nonnegative ordinary coefficients or an exact sum of nonnegative monomials and
nonnegative monomial multiples of polynomial squares.

Initial coefficient certificates settle 71,446 second-gap and 86,265 third-gap
polynomials. Remaining faces deduplicate, after positive integer scaling and variable
permutation, to 29,215 normalized quartics. Of these, 28,881 use a fixed library of
monomial-weighted binomial squares. Another 334 use general polynomial squares.

The only numerically degenerate exception has this exact identity:

`4P(y,z) = (2yz−y−z−40)² + 27(y+z−10)² + 216(y−z)²`,

where

`P=y²z²−yz(y+z)+61(y²+z²)−134yz−115(y+z)+1075`.

This polynomial vanishes at (5,5), explaining the boundary numerical reconstruction.
The identity is added by `finish_exception.py` and checked independently.

## Files and reproduction

- `enumerate.cpp`, `canonical.inc`: complete exact enumeration and support kernel
- `a2_polynomials.jsonl`: coefficient data and relation representatives
- `classify_quartics.py`: integer binomial and shifted-face classification
- `certify_quartics.py`: numerical LP search, followed by exact rational checks
- `certify_exceptions.py`: general-square search; currently imports the preexisting
  degree-three square-search helper from the sibling degree-three directory
- `finish_exception.py`: explicit final identity
- `verify_quartic_certificates.py`: standalone standard-library verification of every
  gap identity, every nonnegative weight/square, and coverage of every population face

The searches use numerical optimization only to find candidate decompositions.
The standalone verifier uses exact integer and rational arithmetic and does not
import NumPy, SymPy, any numerical solver, or any producer module. The final proof
rests on exact replay, not floating-point solver status.

Compile the enumerator with `g++ -O3 -std=c++17 enumerate.cpp -o enumerate`.
Run the Python programs in the order listed. The certificate files are replayable
without rerunning the numerical searches.
