# Prospective formalization interfaces

No Lean module in this package is claimed to compile; no Lean build was run.
The names below are suggestions for future work, not references to existing
files. The mathematical results and executable Python tests have distinct
verification status.

## Repository boundary

Inspected snapshot: `0b4890a1cd1b5417bcf0724db27e35b77bfa96bc`.
Existing inspected file:
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs09Restriction.lean`.
It imports the moment and general arrangement restriction developments and
identifies height-zero arrangements with ordinary additive sixteen-tuples.
Use the shared-label graph/domain convention; do not remove repeated entries
from the source predicate to simplify an algorithmic proof.

## Suggested layers

### 1. `RestrictionTupleInventory`

Define ordered partial tuples with a label set, two position counts, and one
abelian-group difference. Distinct labels are independent Bernoulli variables;
multiple occurrences of a label are not. The key identity is expectation as
a finite sum of products over distinct supports. Allow noninjective images.

Define the array insertion recurrence directly using binomial coefficients.
Prove it by splitting the positions occupied by the newly inserted label.
This avoids analytic exponentials and division by factorials in Lean.

### 2. `RestrictionStirlingResponse`

Define Stirling numbers of the second kind using their recurrence. Prove the
truncated coefficient identity for
`(1 + p*(exp(t)-1))*H_p(t) = exp(t)-1`, where exp is a finite coefficient
sequence. Show `h_k(p) = sum_j (-p)^(j-1) * j! * S(k,j)`.

Derive exact local replacement, including p=0 and p=1. The formal inverse
has constant coefficient one; there is no division by p or by 1-p. Prove the
zero-difference top-coefficient derivative formula separately.

### 3. `RestrictionExactRounding`

Package a finite family of inventories on the same labels with rational
signed coefficients. Prove the two-child weighted-average identity and the
endpoint-selection inequality. Induct over undecided labels to obtain the
shared-subset theorem. Do not infer individual bounds for every statistic
from a bound on their signed sum.

A graph/domain instantiation gives the positive-surplus implication:
R - (1-eta)T >= J > 0 implies R >= (1-eta)T and T >= J/eta.

### 4. `RestrictionSupportProfile`

Use integer coefficients indexed by distinct undecided support size. Prove
its degree is at most the number of tuple positions, independently of quota.
Count uniform r-subsets containing a given j-subset to obtain
binom(r,j)/binom(N,j), with explicit zero cases and the (N,r,j)=(0,0,0) case.

Prove exclusion and inclusion replacements and the correct child evaluators:
(N-1,r) for exclusion, (N-1,r-1) for inclusion. The size invariant is a separate
statement from the objective invariant. Test the forced branches r=0 and r=N.

### 5. `RestrictionSystems`

Define coefficients indexed by position subsets. Show that the replacement
sum has exactly 3^t source/target subset pairs. Generalize to position types
using multi-indices and products of binomial coefficients. No coefficient
invertibility is necessary in this finite algebraic layer.

### 6. `RestrictionArrayRefinement`

Refine abstract coefficient functions to executable dense arrays. Prove that
descending total degree (or subset cardinality) reads only pre-update source
rows. Include the group-index translation bijection. The arithmetic cost
proof counts weighted translations, not general group convolutions.

Rational arithmetic must be exact. The recorded finite output trace is not
by itself a formal proof: a checker must verify the initial expectation and
the local transitions. The article supplies independent tuple/subset
references for small regression instances.

### 7. `RestrictionRationalFilter`

Separate the analytic existence certificate from the finite engine. Prove the
support-based probability perturbation bound, rational pi/cosine intervals,
and the normalized Fejer approximation. The analytic theorem preserves enough
surplus to retain the companion constant after rationalization. A future
filter can replace this layer without changing the rounding layers.

## Formalization order and non-goals

The first four layers already give a reusable theorem independent of the
later Gowers machinery. An initial kernel-checked deliverable should be the
finite inventory and conditional-expectation invariant, not a claimed global
Szemeredi improvement. Formalize runtime, rational bit bounds, array execution,
and analytic filters as separate follow-on obligations.
