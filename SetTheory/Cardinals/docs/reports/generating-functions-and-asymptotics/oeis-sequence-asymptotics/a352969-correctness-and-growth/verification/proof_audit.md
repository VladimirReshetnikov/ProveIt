# Proof audit and scope

This is a human-readable proof audit, not a proof-assistant certificate.
The numbered references below refer to sections of `article.pdf`.

## Algorithm

The unordered iterator enumerates index pairs i <= j, including i = j.
Commutativity supplies the omitted reversals, while set insertion removes
only multiplicity, not membership. Induction gives the exact simultaneous
set recurrence. Cached mutable objects in the original program must not
be externally altered. The replacement returns frozensets and validates
input before the cache and before deduplication; in particular, bool/1
hash equality cannot mask an invalid input element.

## Structural and counting dependencies

1. **Persistence and height (Section 3).** Multiplication by 1 gives
   S_n subset S_(n+1). Thus minimum formula height <= n, rather than
   exactly n, characterizes membership. Proper decomposition in the
   independent depth oracle uses strictly smaller integers.
2. **Maxima (Section 3).** M_(n+1) = max(2*M_n, M_n**2); stage 0 is the
   exceptional initial step. For n >= 1, M_n = 2**(2**(n-1)).
3. **Square cardinality bound (Section 3).** It applies only for n >= 1,
   when 2 is present. The m distinct values 2*x belong to both output
   sets, improving the crude m*(m+1) upper bound to m**2.
4. **Prime amplification (Section 4).** Exactly R = 2**(n-k) factors
   are used. Each prime has height <= k; the balanced product adds n-k.
   Unique factorization counts multisets, not ordered tuples. A repeated
   prime is legal because equal operands are allowed.
5. **Prime supply (Section 5).** Each p-adic valuation of the central
   binomial coefficient has at most floor(log_p X) nonzero unit terms.
   Hence the full p-power is <= X. This proves the needed prime lower
   bound without assuming the prime number theorem.
6. **Radix construction (Section 7).** For t >= 1, r is the least
   triangular index and q = t-r >= 0. Then r(q) <= r-1. Every nonzero
   block coefficient has height <= t+1 by induction. The shift factor
   2**(j*2**q) has height <= t+1. Product height is <= t+2, and a balanced
   sum adds <= r. Zero digits are omitted; no zero leaf or free integer
   constant is admitted. The t=0 base consists solely of the value 1.
7. **Finite lower bound (Section 8).** For n >= 16, k=t+r+2 <= n. All
   primes <= 2**(2*n) are strictly below 2**(2**t), even in the endpoint
   equality case, because 2**(2*n) is composite. Prime supply yields
   P/R >= 2**n; t=ceil(lg(2*n)) gives 2**t < 4*n. Consequently
   lg(a_n) > 2**(n-r-4).
8. **One-step growth (Section 9).** Ordered product fibers have size at
   most tau(z), for z <= M_(n+1). The elementary uniform divisor bound
   loses at most (ln(2)+o(1))*2**n/n in the logarithm. The constructive
   lower bound for ln(a_n) makes the relative loss <= n**(-1+o(1)).

## What has and has not been verified computationally

- S_0 through S_6 were explicitly enumerated.
- a_7 is quoted from OEIS, not independently enumerated.
- The proper-decomposition oracle checked height/membership equivalence
  for every integer from 1 through 2000 against stages 0 through 6.
- Constructive witnesses were checked on consecutive small integers and
  fixed-seed arbitrary-looking, all-one, and single-bit integers through
  16,384 bits. The shipped witness has 256 bits and height 14.
- Integer parameter and triangular-recursion inequalities were tested on
  broad finite ranges. The all-input justification is the written proof.
- All 16 tests passed; actual transcripts and runtime metadata are
  included. Python 3.9 compatibility is the implementation target, not a
  claim that the suite was executed on every supported Python version.

## Scope and numerical interpretation

The main limits and explicit inequalities are unconditional. The limit
of lg(a_n)/2**n exists, but its strict positivity and value are not proved.
In particular, the article does not conclude a_n ~ C**(2**n).

The candidate count is a deterministic mathematical quantity. Hash-based
time bounds use a bounded-average-probe model; they are not worst-case
claims about adversarial Python integer hashes. A sorting-based analysis
is described, but that alternative is not implemented in the package.

Floating-point logarithms in the data table are descriptive numerical
values. Exact integer counts and inequalities, not floating-point fits,
are the basis of the proofs. Rounded upper bounds for theta in the
article are rounded upward.
