# Independent audit of the growing-branching routing extension

## Verdict

The fixed-sequence extension of the geometric routing construction is valid under
the following hypotheses (after discarding finitely many initial terms):

1. `0 < a_(n+1)/a_n <= mu < 1`;
2. `Delta_n = log(a_n/a_(n+1)) = o(log log n)`.

More generally it is enough that, for `G_N = max_{n0 <= j < N} Delta_j`,

`liminf_{N -> infinity} G_N / log log N = 0`.

The latter assertion is a direct finite-budget consequence, not an average-gap
claim. The conclusions are the usual ones: for every epsilon > 0 there is a
compact subset of [0,1] of measure > 1-epsilon containing no nontrivial affine
copy of the given fixed sequence.

This is a strict extension of fixed two-sided bounded ratios. In particular,
`a_n = exp(-n (log log n)^alpha)`, `0 < alpha < 1`, is covered although its
consecutive ratios tend to zero. Appropriate finite index shifts make the
formula defined and positive at every starting index.

## The inherited finite routing estimates

Fix p in (0,1), mu in (0,1), and put c = 4/(1-mu). Normalize the sequence so
that a_(n0) <= 1/8. For a budget N, define G = G_N and choose dyadic grids

`N_b = 2^ceil(log_2(c/a_b))`,  n0 <= b <= N.

Then `c/a_b <= N_b < 2c/a_b`. The geometric proof's stable-key and distinct-key
arguments remain valid with these grids. For any window edge e of length r,
its edge-plus-child-subtree span is at most 2r, so the local scale count is

`D(r) = 4 + 2 (M-1) r (1 + 2c exp(2 G r))`.

The fixed-scale conditional miss probability is exactly
`(1-p/2)^((M-1)r)`, hence at most `exp(-alpha r)` with
`alpha = p(M-1)/2`. Earlier-grid instability has total density at most
`4 K c mu^(g+1)`, where K is the number of tree edges.

These are the only quantitative estimates needed below. The center-exposure
conditioning remains sound: successful selector tests use mutually distinct
unexposed entries; after fixing all selectors their terminal addresses are
distinct because nested grid resolution preserves separation. The finite set
of representative dilation parameters depends only on the center, deterministic
grids and exposed default vertex; it is fixed before the remaining bits are
revealed. Open enlargement and exceptional-center repair are unchanged.

## Quantified parameter choice

Let `L = log log N` (natural logarithms throughout), and take

`M = floor(L / (2 log 2))`;

`d = ceil(2^(M-1) log(2/p))`;

`K = sum_{h=1}^d M^h`;

`g = max(1, ceil(log(8 K c/p)/log(1/mu)))`;

`r_1 = r_0 = 1`,

`sigma_1 = M + (M-1)g`,

`r_h = g + sigma_(h-1)` and
`sigma_h = 2 M sigma_(h-1) + (3M-1)g` for h >= 2.

Here sigma_h is the exact span including gaps. For sufficiently large N on a
subsequence with G_N/L -> 0, M >= 2. Then:

* No-default probability is at most `exp(-d 2^(1-M)) <= p/2`.
* Stability loss is at most `4Kc mu^(g+1) < p/2`.
* Uniform scale failure is less than p for every positive integer r.
* The windows fit within the prefix n0,...,N.

The third assertion deserves an explicit bound. Since G >= 0 and c >= 4,

`D(r) <= A_c M r exp(2 G r)`, where `A_c = 6 + 4c` suffices.

Let `beta = p(M-1)/2 - 2G`. Since G/L -> 0 and M is asymptotic to a positive
constant times L, `beta ~ p L/(4 log 2)`, in particular beta >= 1 eventually.
The function `r exp(-beta r)` is decreasing for real r >= 1 when beta >= 1.
Consequently

`sup_{r>=1} D(r) exp(-p(M-1)r/2) <= A_c M exp(-beta) -> 0`.

This justifies r0 = 1 simultaneously for every height; merely proving the
estimate at a single r would not be enough.

For the fourth assertion, `2^M <= sqrt(log N)`, hence

`d = O_p(sqrt(log N))`,

`log K = O(d log M)`,

`g = O_(p,mu)(1 + d log M)`.

Solving or bounding the exact span recurrence gives

`sigma_d <= C (g+1) (2M)^d`

with an absolute C. Therefore

`log sigma_d <= d log(2M) + O(log(g+1))`

`= O_(p,mu)(sqrt(log N) log log log N) = o(log N)`.

Thus `n0 + sigma_d - 1 <= N` eventually. All uses of the finite maximum G_N
are legitimate; there is no circular dependence on indices beyond N.

With these estimates, the original finite random construction, open enlargement,
and exceptional-center repair yield a periodic normalized-scale blocker of
density <= 6p. Summable signed dyadic dilations of such blockers produce the
claimed compact avoidance set.

## Finite-block version

The same proof works if the given positive null sequence contains, for
arbitrarily large N, finite subsequences b_1 > ... > b_N with

`b_(j+1)/b_j <= mu < 1`,

and maximal logarithmic gap `G_N` satisfying `G_N/log log N -> 0` along a
sequence of such blocks. Normalize the whole sequence once to make b_1 <= 1/8.
Use indices of the finite subsequence for windows and use any original null
tail in the open repair step. The original-index positions are irrelevant.

This subsumes arbitrarily long finite blocks with fixed two-sided ratio bounds,
even when no infinite subsequence has a positive lower consecutive ratio.

## What has not been proved

The weaker global condition `log(1/a_n)=O(n)` does not imply any uniformly
bounded consecutive-ratio block criterion used above. For example, set

`t_n = sum_{k=1}^n (1 + v_2(k))` and `a_n = exp(-t_n)`.

Then `t_n <= 2n`, while any 2^m consecutive gap indices include a multiple of
2^m, whose logarithmic gap is at least m+1. Thus, for any fixed lower ratio
lambda > 0, finite ratio chains have bounded lengths. This example does not
disprove nonuniversality; it disproves that proposed extraction shortcut.

The present max-gap estimate also excludes `exp(-n log log n)`, `1/n!`, and
`exp(-n^2)` by itself. No claim about their universality follows.

No simultaneous blocker for all arbitrary bounded-ratio sequences is claimed.
Lebesgue density points can be used to choose a bounded-ratio sequence inside
any positive-measure set, so such a uniform conclusion is false.

## Literature check performed

The primary 2025 survey of Jung--Lai--Mooroogen (arXiv:2412.11062v2) states
the earlier subexponential normalized finite-gap criterion and the geometric
bottleneck. The OpenAI October 5, 2026 geometric preprint gives the routing
method but its title, theorem and proof specialize to exact geometric
progressions. Searches for Erdos similarity with 'superexponential', 'log log',
'loglog', and 'fast decreasing' did not find the theorem above. These searches
do not certify exhaustive novelty. The source comparison confirms that ProveIt's polynomial
family theorem already subsumes the simpler fixed bounded-ratio extension,
which therefore should not be advertised as new.

## Final audit of assembled sections 02, 03, and 07

The assembled article files `02_finite_routing.tex`,
`03_growing_budgets.tex`, and `07_quantitative_budget.tex` were independently
read in full, together with the main theorem statements needed to check their
quantifiers. No substantive mathematical defect was found.

### Finite routing and globalization

* The short proof of `sigma_d <= (g+1)(2M)^d` is valid: adding 2g makes the
  recurrence bounded by multiplication by 2M, and its displayed base estimate
  holds for all M>=2 and g>=1.
* The active gate/terminal conditioning is valid on every default-admitting
  center atom. The scale representative set is determined before unexposed
  bits, and the lattice-point count includes endpoints correctly.
* The closed residual set, open repair, and density budgets give at most 6p.
* The main theorem's sequence is positive and null, hence bounded. A bounded
  head deletion of each decreasing block excludes any fixed finite prefix of
  the original sequence, even if original indices are not ordered in a block
  or the original sequence repeats values.
* Scaling the input patterns by 2^k keeps each constructed blocker 1-periodic.
  The budgets p_(k,J)=(epsilon/72)2^(-|k|-J) sum to epsilon/24, and the signed
  blockers consequently cost at most epsilon/2. Tail quantifiers and infinitely
  many distinct hits follow exactly as claimed.

### Refined normalized budget

The Bernoulli-theta gates give exact conditional failure
`(1-p theta)^((M-1)r)`, while the random-set mean density remains p. The
modified window lengths bound the descendant span by `(1+xi)r`. Their ceiling
error is covered by

`sigma_h <= (2M/xi)sigma_(h-1) + (4M/xi)g`.

The looser asserted bound `sigma_d <= (g+1)(4M/xi)^d` follows, including its
base case. No-default error <=tau/2, local error <tau, instability <tau,
and the two open-enlargement costs each <=tau give density <=p+5tau (indeed
the stated intermediate estimates have a little slack).

For theta=1/G, xi=G^(-1/4), and the displayed M, the local exponent is at
least G^(3/4). Also

`log(delta^(-1)) <= G/p + (2/p)G^(3/4) + O_p(1)`.

Taking two logarithms of the span gives precisely the stated sufficient
finite budget, with a constant C depending only on p,tau,mu. The restricted
lower comparison is valid as well: convexity gives
`-log(1-p theta) <= p[-log(1-theta)]`; the imposed entropy balance therefore
forces `log(delta^(-1)) > G/p`. A complete tree with no-default probability
bounded below one then requires depth of order at least delta^(-1), giving
the claimed double-logarithmic lower comparison within that parameter scheme.
This is not a lower bound on arbitrary blockers.

The two-point periodic-interval example correctly shows why a fixed-density
obstruction only for normalized scales does not establish all-scale
nonuniversality. It supports the appendix's stated limitation.

### Minor precision edits identified during review

1. For J=1 in the deletion proof, avoid a minimum of the empty prefix: say
   choose delta smaller than every one of the first J-1 values.
2. In the separated-block example, the statement that the largest logarithmic
   gap is one applies for j>=2; the one-point block has no adjacent gap.
3. In the quantitative appendix explicitly retain
   `sigma_1=M+(M-1)g`, and apply the modified sigma_h formula for h>=2.
4. Optionally mark the conditional all-scale bound as applying on atoms with
   a default, where its local length r is defined.


## Final integration status

All four precision edits listed above were incorporated in the delivered manuscript.
