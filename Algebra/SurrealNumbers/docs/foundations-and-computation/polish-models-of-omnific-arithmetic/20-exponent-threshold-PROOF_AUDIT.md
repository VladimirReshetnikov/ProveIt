# Proof and hypothesis audit

Date: 4 October 2026.

## Status

The article contains complete written arguments relative to its explicitly
stated standard descriptive-set-theoretic inputs. It has received an
in-session mathematical and layout review, not an independent referee report
or proof-assistant verification. No Lean or Rocq proof of the new results was
compiled. No historical priority is claimed.

## Proposed contribution versus reused material

1. **Exponent-group threshold (Theorem 1.1).** The cyclic positive construction
   is already recorded in ProveIt. The proposed extension is the
   presentation-independent obstruction for every dense subgroup of R and
   its combination with the elementary subgroup dichotomy.
2. **One-root obstruction (Theorem 1.2).** The proof uses DIV and Root_k for
   one fixed standard k >= 2, not an induction scheme. A dyadic-exponent
   countermodel to open induction establishes a strict weakening within the
   ordered-ring-cone framework.
3. **Separated-grid interface (Theorem 4.4).** The proof strategy is adapted
   from Glazer. The manuscript states an explicit abstract interface and
   supplies metric-tail, finite-flip, and measurability details.
4. **Cofinal translation obstruction (Corollary 4.6).** The fusion can be
   shifted above any parameter. Its one-root and dense-exponent applications
   use the same interface. Cofinal discontinuity phenomena under other
   hypotheses already appear in the repository catalogue.
5. **Algebraic companion results.** The cutoff-series field and integer-part
   mechanism are standard constructions. The exact root-spectrum statement
   and root-tower consequences are proved here; separate historical novelty
   for these results has not been established.

## Imported mathematical inputs

- Uncountable Borel subsets of Polish spaces contain Cantor copies.
- An injective Borel map between standard Borel spaces has a Borel image and
  Borel inverse onto that image.
- A relation that is both analytic and coanalytic is Borel.
- Galvin's perfect-set theorem for Borel colorings of pairs, as discussed in
  Blass's partition theorem.
- Ordinary product probability on binary sequences. The final zero-one step
  is explained in the article using independence of finite cylinders.
- The classical Z-group characterization of Presburger arithmetic, used only
  to identify additive reducts, not to prove either main obstruction.
- The usual finite Conway normal-form laws, used only for the surreal
  interpretation, not for the abstract ring classification.

## Critical proof checks

### No hidden topological group assumption

The topology is placed on the nonnegative cone, not on the signed ring.
Subtraction is used algebraically only. In the fusion step, the convergence
m + h_(n,j) -> m is obtained by translating a continuous Cantor map by the
fixed nonnegative element m - x_n. It is not inferred by cancelling a
continuous translation. Finite-flip identities are passed to the limit after
adding fixed positive finite sums to the two sides, and only then cancelled
in the ring.

For the cofinal-translation corollary the prefix base is C + d. To pass an
identity with corrections A and B to the limit, one uses the continuous
translations by A + d and B + d and cancels d only algebraically.

### Complete-metric fusion

At level n the finite prefix separation d_n is strictly positive. The move
budget is delta_n = 2^(-n-3) min_(j<=n) d_j. Every later tail is bounded by
2^(-n-2) d_n, at most d_n/8 for n >= 1. The limiting map is uniformly
convergent and injective. No compactness of an arithmetic interval is assumed.

### Borel events and finite-bit changes

The signed expression D(r) = F(r) - F(complement r) need not be a Borel map
to a topological signed ring: no such topology is used. Its comparison events
are rewritten using Borel order and Borel addition on the cone. The finite
perturbation identity is exact in the ambient ring. Lacunarity shows that at
most one assignment on a k-bit block can place D(r) in (0, y_n], giving the
2^(-k) bound. The event D(r) > y_n for all n is unchanged by every finite bit
modification, not merely almost invariant.

### Bounded grids for dense exponents

Choose alpha_n increasing below a fixed gamma_* and beta_n positive with
alpha_n + beta_n < alpha_(n+1). The grid uses a_n = T^alpha_n and
u_n = T^beta_n. Its index interval contains all positive real multiples of
T^eta_n for 0 < eta_n < beta_n, making it uncountable regardless of the
proposed topology. Only the selected monomial scalar maps must be Borel.

### The external countability cut

I = {a : [0,a] is countable} is not asserted to be internally definable.
Closure under multiplication uses DIV: each element of [0,ab] is determined
by a quotient in [0,a] and a remainder in [0,b]. Properness follows from an
increasing Cantor copy. No internal sequence of nonstandard length is used.

Two successive integer kth roots yield
r_(n+1)^(k^2) <= r_n < (r_(n+1)+1)^(k^2).
If a_(n+1) <= 5 a_n r_(n+1), quotient bounds imply both
c >= a_n r_(n+1)^(k^2) and c < 6 a_n r_(n+1)^2, impossible for the
infinite root element. The code checks finite instances where the lower
root is sufficiently large; it does not check external uncountability.

### Integer part and root spectrum

The auxiliary series field has support finite above EVERY real cutoff.
Consequently its positive part is finite. Geometric and binomial
substitutions are justified by a strictly positive drop in the greatest
exponent of the negative tail. No analytic convergence is asserted.

The floor constant must be reduced by one when the constant coefficient is
an integer and the remaining infinitesimal tail is negative. The test suite
includes this boundary both in division and in square-root truncation.

Necessity of Gamma = k Gamma follows from the leading exponent of an integer
root of T^gamma. Sufficiency follows from binomial substitution and the
restricted floor. The failure of cube induction in the dyadic example is
shown by the explicit successor-closed predicate x^3 < T.

## Finite checks

The distributed `verification_results.json` records 13,034 successful exact
assertions, seed 20261004. Checked groups include signs, degree laws, division,
root intervals, quotient-grid estimates, finite-bit separation, fusion budget
inequalities, and rational-exponent sample grids. These are diagnostics of
finite formulas, not proof certificates for infinite mathematics.

## Limitations that must accompany reuse

- All theorems concern set-sized cones, not the class of all surreal numbers.
- The dense-exponent obstruction assumes Borel multiplication, or at least
  the needed countably many Borel scalar maps.
- It does not exclude a presentation with continuous multiplication and
  merely Borel addition.
- The positive construction does not give a topological group on the signed
  ring and does not make truncated subtraction continuous.
- Finite generation as an exponent GROUP is not finite generation as a
  nonnegative exponent MONOID; the irrational-adjunction discussion explicitly
  distinguishes them.
- ZFC proofs here do not automatically establish reverse-mathematical bounds.
- The full ProveIt report was not independently audited, and an unsuccessful
  keyword search is not evidence of priority.
