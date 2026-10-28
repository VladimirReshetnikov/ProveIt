# Independent review of the streamed and projective coefficient kernels

## Verdict and scope

The inspected anisotropic antipodal implementation is mathematically correct for the inherited input contract: a finite product of affine forms over the finite free monic/truncated coefficient rings implemented by `RingSpec`, with nonnegative integral target exponents and positive integral precision. It preserves the creation-time representatives and uses sufficient precision for every nonunit division. The full and paired Gray variants return the same target residue as direct coefficient multiplication.

This is an independent mathematical/code review with targeted executable checks. It is not a proof-assistant certificate, a review of a complete SAT engine, or a claim of universal wall-clock dominance over all coefficient algorithms.

The reviewed implementation at this stage has SHA-256
`bee1acd235d7f657566d0c496a51faaa93540ae19af3a7556de03a22e7da786b`.
The baseline copy is byte-identical to the pinned repository's
`eth_contraction_improvements/code/packet_extraction.py`; both have SHA-256
`ef0a7cab05bd4e8271a9c79eea4e70a717eb5df9d74a424a2b16a0d03b8bdadc`.

## 1. Exact identity and the anisotropic precision improvement

Homogenization gives a degree-`R` polynomial `H` and nonnegative exponents
`b=(R-sum(beta), beta_1,...,beta_k)` with `sum(b)=R`. Variables whose target
exponent is zero may be set to zero and omitted before evaluation.

For each active exponent define `h_j=1` if `b_j` is even and `h_j=2` if it is
odd. The implemented centered coordinates are

`x_j(gamma_j) = h_j gamma_j - h_j b_j/2`.

They are integers in both cases. Finite differences, followed by homogeneity,
give the identity over any commutative integral coefficient algebra:

`sum_(0<=gamma<=b) (-1)^(R-|gamma|) product_j binom(b_j,gamma_j) H(x(gamma))`

`= 2^O product_j b_j! [X^b]H`,

where `O=sum_(b_j odd) b_j`. Only the target monomial survives: a different
monomial of total degree `R` must have degree below `b_j` in some coordinate,
so its corresponding difference vanishes. The target contributes exactly
`product_j h_j^(b_j) b_j!`.

Under the involution `gamma -> b-gamma`, the grid point changes to `-x`.
The difference sign changes by `(-1)^R`, and homogeneity changes the value by
the same factor. Thus the two summands agree. If a fixed point exists, every
`b_j` is even and `x=0`. Since `R>0`, its contribution vanishes. The sum over
one representative from each pair therefore equals

`2^(O-1) product_j b_j! [X^b]H`.

Let `nu=sum_j v_2(b_j!)`. The required binary denominator valuation is

`v = nu+O-1`.

This is nonnegative. If an odd exponent is present then `O>=1`. Otherwise
`R>0` implies a positive even exponent and hence `nu>=1`. Consequently
`p+v>=p` always, including the all-even case `v=nu-1`. The all-even grid really
saves one working-precision bit relative to the earlier full differences.

The program evaluates the representative sum modulo `2^(p+v)`, checks
coordinatewise divisibility by `2^v`, divides the canonical integer residue,
and inverts only the remaining odd factorial factor modulo `2^p`. This gives
the correct residue. It never tries to invert an even residue.

The monic quotient and nilpotent truncation give a finite free integral
module, so reduction and coordinatewise exact division are valid. Nothing in
this proof requires a field or a reduced ring. In particular the tested
nilpotent and non-irreducible examples are within the proof's scope.

## 2. The all-even box decomposition is complete

If some exponent is odd, choose the first such coordinate `j` and retain its
lower half `0<=gamma_j<=(b_j-1)/2`, with all other coordinates unrestricted.
Every antipodal pair has exactly one member there.

If every exponent is even, classify a noncentral point by its first
noncentral coordinate `j`. Retain the member for which `gamma_j<b_j/2`.
The corresponding disjoint box fixes earlier coordinates at their centers,
puts `gamma_j` in `[0,b_j/2-1]`, and leaves later coordinates unrestricted.
These are exactly the boxes yielded by `_antipodal_boxes`. They omit only the
all-center point, whose homogeneous value is zero. Hence their total size is
`(G-1)/2` when `G=product_j(b_j+1)` is odd, and is `G/2` in the odd-exponent
case. Both are `floor(G/2)`.

The Gray generator uses offsets within each box, while the binomial updates
use absolute `gamma=start+offset`. This distinction is handled correctly.

## 3. Gray updates and the precise complexity claim

`gray_changes` implements a reflected mixed-radix traversal. Each yielded
step changes one coordinate by exactly one. A row value is therefore updated
by adding the fixed row coefficient times `h_j*step`; all other row
contributions remain unchanged. The binomial product updates use the exact
integer ratios

`binom(b,g+1)/binom(b,g)=(b-g)/(g+1)`

and

`binom(b,g-1)/binom(b,g)=g/(b-g+1)`.

The code performs these divisions in integers with a remainder check, before
passing the weight to the coefficient ring. Every step flips the sign.

There is no worst-case constant-delay claim for the public generator: one
transition can scan all axes, particularly with singleton axes. The relevant
aggregate bound is sufficient. Zero-target axes are removed in production.
For a full grid whose active radices are all at least two, scanning carries
has total `O(G)` cost. An odd-exponent half-grid introduces at most one
singleton axis and still has total `O(G)` scan cost.

For all-even exponents, every active radix is at least three. Box `j` has
size

`G_j=(b_j/2) product_(k>j)(b_k+1)`.

Its fixed prefix of length `j-1` may be rescanned on every transition, but
`G_j/G <= (1/2)3^{-(j-1)}`. Therefore
`sum_j j G_j = O(G)`. The cost of all end-of-box scans and box starts is
`O(q^2)`, where `q` is the number of active axes; because `q^2<=3^q<=G`, it
is absorbed. Row initialization across all boxes costs `O(R q^2)` ring
operations and is similarly absorbed by `O(RG)`.

After the unavoidable input-reading/canonicalization work, the new routines
therefore use `O(RG)` ring operations instead of the baseline's worst-case
`O(RqG)` row-formation operations. They still multiply `R` row values at
every retained point. The paired routine performs exactly
`R floor(G/2)` such ring multiplications for `R>0`, at its specified working
precision. Integer weights have `O(R)` bits and the factorial denominator
has `O(R log(R+1))` bits; their computation introduces polynomial overhead,
not a hidden grid-size table.

This is an arithmetic-operation improvement, with explicit precision costs.
It is not automatically a factor-`q` bit-time improvement when coefficient
ring multiplication already dominates addition.

## 4. Creation-time canonical representatives and boundary cases

`_validate` first reduces every input coordinate modulo `2^p`. Those tuples
are retained unchanged as integer lifts while only temporary row values and
accumulators use the enlarged modulus. The routine never redefines an old
tensor at a new creation precision. Inputs differing by multiples of `2^p`
produce identical full result records in the independent checks.

The implementation separately handles impossible degree (`sum(beta)>R`)
and `R=0`. In the latter case, only the constant target survives and returns
the multiplicative identity. An empty list of target variables with `R>0`
is handled by the single homogenizing axis. Zero target coordinates are
removed correctly. The centered construction is not applied to the degree
zero case, where its division-by-two argument would not hold.

## 5. Tests reviewed and independently added

The author test suite uses a direct coefficient dictionary as an independent
oracle, compares against the unmodified shipped finite-difference routine,
and tests scalar rings, a quadratic unramified extension, nilpotent
truncations, their combination, and another monic quotient. Its exception
checks remain enabled under optimized Python.

The additional `check_independent_review.py` constructs involution classes
without using the box rule, checks one-and-only-one representatives, and
uses a separate integer polynomial oracle for scalar extraction. It passed
normally and with `python -O`:

- 741 exponent profiles and 20,860 antipodal orbits;
- 280 comparisons with integer polynomial multiplication;
- 280 invariance checks under input shifts by multiples of `2^p`;
- three explicit nonzero, low-precision, all-even fixtures.

The author's validation was also rerun under optimized Python: 340 Gray
grids, 1,392 exhaustive scalar cases, and 900 seeded comparisons across the
five ring choices. Results are recorded in `results/independent_review.json`
and `results/independent_optimized_validation/verification.json`.

## 6. Benchmark interpretation

The benchmark compares identical generated forms, target exponents, rings,
and target precision. All methods are checked against the direct coefficient
oracle before accepting timing samples. The baseline file is unchanged.
Execution order rotates between repetitions, the seed is recorded, and raw
timings accompany the medians. The varied profiles include squarefree,
all-even, mixed odd/even, zero-heavy, extension, nilpotent and precision
cases.

These are modest synthetic microbenchmarks on one machine. Three timings
per case justify reporting the observed median ratios, not a universal
speedup, a statistical confidence interval, or end-to-end SAT performance.
The extra precision for large odd exponent mass is fully paid in the
timings. The removal of zero-target axes is a legitimate contribution to
the zero-heavy case, but that result should not stand in for all profiles.

## 7. Projective root-of-unity extension: mathematical criterion

For a homogeneous degree-`R` polynomial with positive target exponents
`b_j` summing to `R`, choose a minimum exponent `b_k` and set `X_k=1`.
For every other axis use a cyclic filter of length `d_j=b_j+1`. Provided the
chosen roots satisfy the full orthogonality identity, the filtered average
extracts the target coefficient exactly.

Indeed the filter admits only powers `alpha_j=b_j+t_j d_j`, with `t_j>=0`.
Homogeneity forces `alpha_k=b_k-sum_(j!=k)t_j d_j`. If any `t_j>0`, then
`d_j>b_k`, so the pivot exponent would be negative. Thus only the target
monomial survives. The pivot must have minimum exponent; an arbitrary pivot
can allow aliases.

For exponents in `{1,2}`, use signs and a cubic root. Over the finite free
algebra `A[U]/(U^2+U+1)`, the exact identities `U^3=1` and
`1+U+U^2=0` imply cubic orthogonality, without a field assumption. Sign
orthogonality is exact over the integers. If `s` nonpivot exponents equal
one and `c` equal two, the denominator is `2^s 3^c`; work modulo `2^(p+s)`,
divide the canonical coordinate numerator by `2^s`, and invert `3^c`.
All-two targets need `G/3` evaluations at target precision `p`, with no
factorial denominator.

In an upstream coefficient ring whose residue field has even degree,
cubic roots exist modulo two and lift uniquely modulo `2^P` because
`2U+1` is a unit. Finite-precision lifts are sufficient; one should not
claim that the uncompleted rational ring necessarily contains an exact
cubic root. Merely having an element of a given order in an arbitrary ring
does not by itself prove general cyclic orthogonality. For the explicit
quadratic relation here, orthogonality is established algebraically.

Generalized Glynn formulas and roots-of-unity coefficient filters are
classical; novelty must be scoped to the exact implementation and integration
relative to the reviewed packet corpus.

## 8. Final projective implementation review

The complete `projective_coefficients.py` implementation was subsequently
read independently. The reviewed file has SHA-256
`31f004f325f5bb988b026a7c1873b01d4091ae5cb769e343efda865bba1d4291`.
No coefficient-correctness blocker was found.

The code first fixes the input coefficients modulo `2^p`, homogenizes,
removes zero target axes, and selects a minimum positive target exponent as
the pivot. It explicitly rejects positive exponents other than one or two.
The empty product, impossible degree, and one-active-axis cases are handled
separately or reduce correctly to one evaluation. With `s` nonpivot ones,
the temporary working modulus is exactly `2^(p+s)`.

When a cubic axis is present, the root is checked using
`omega^2+omega+1=0` at that enlarged modulus. The default root exists only
for the already selected ring with defining polynomial `(1,1,1)`;
otherwise the caller must supply a valid root. No extension or additional
coefficient dimensions are silently introduced. A root that is valid only
at target precision is insufficient and is rejected when its relation fails
at working precision. Nilpotent truncation in the other variable does not
affect the algebraic identity.

The streamed reflected Gray traversal uses the correct adjacent root
differences for row updates. Its character weight is the product of the
current roots, since `omega_j^(-b_j)=omega_j` for a root of order `b_j+1`.
Binary steps change its sign; upward and downward cubic steps multiply it
by `omega` and `omega^2`, respectively. The numerator is checked for exact
coordinate divisibility by `2^s`, then divided and multiplied by the inverse
of the odd factor `3^c` at target precision. The recorded evaluation count
is checked against `product(b_j+1)/(1+min(b_j))`.

The projective author's tests and ten-case benchmark were independently
tested by another team member; this final review did not duplicate that
large test suite. The algebra and implementation inspection close the
earlier review's implementation gap. One minor instrumentation issue is
that the `ring_multiplications` counter does not include the single
`omega^2` multiplication used during root validation. It includes the
adjacent-delta precomputation and evaluation multiplications. This has no
effect on results, evaluation counts, measured timings, or asymptotic bounds;
the counter should either document that exclusion or count that validation
operation if it is intended to represent every call.

## 9. Closing report comparison review

The final report's fifteen-packet inventory and source pin
`6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a` agree with the closing repository
snapshot. The explicit compatible polynomial-space coefficient
`66.6051434076`, fixed-alphabet boundary `66.1927236936`, and numerically
optimized two-stage boundary `66.12047546` are distinguished correctly in
the body. The latter is a schedule-model value, not a globally optimal bound
or a completed implementation theorem. The cached coefficient
`44.5375718550` uses exponential space coefficient `39.4959495337`, so it
belongs to a different resource regime.

The abstract initially described `66.6051` as the strongest compatible
polynomial-space construction. A correction to describe it as one strong
explicit compatible construction was recommended, because the body already
displays smaller schedule boundaries. The report correctly limits the new
measured gains to local coefficient kernels and does not claim a better
unrestricted SAT logarithmic exponent, a full SAT implementation, or a proof
of the complete upstream argument. Classical Smith forms, Gray codes,
finite-difference identities, and projective/permanent methods are credited
as classical; the integration and explicit precision and resource accounting
are the scoped contributions.
