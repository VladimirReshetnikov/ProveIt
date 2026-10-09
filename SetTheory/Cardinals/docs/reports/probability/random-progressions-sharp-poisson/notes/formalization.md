# Proposed formalization roadmap

**No Lean source or kernel-checked proof is claimed in this package.**
The suggested units below are a plan, not statements about which current
Mathlib APIs already exist. Verify API names and prerequisites against the
actual ProveIt toolchain when implementing them.

## Stage 1: finite progression geometry

Define positive-step AP indices with endpoints in Fin n, positive cores,
predecessor masks, and supports. Prove the head/no-AP equivalence and the
interior-head/(r+1)-AP bijection. Derive the exact finite count formula.
Then prove same-step exclusion and the rational-ratio overlap lemma.

Suggested independent targets are:

```text
head_zero_iff_no_progression
interior_head_equiv_longer_progression
ap_index_card
same_step_heads_disjoint_events
support_intersection_bound_reduced_ratio
```

## Stage 2: finite product probability and influences

For product Bernoulli measures, establish the probability of a consistent
positive/negative cylinder. Formalize the one-shared-coordinate covariance
identity and the exact aggregate signed-influence decomposition. Keep the
boundary and predecessor terms explicit until a separate bound is applied.

## Stage 3: abstract conditional avoidance

Formalize positivity and conditional control by induction on the finite
conditioning set. This precedes all divisions by avoidance probabilities.
Formalize the auxiliary-event excess/deficit inequalities and the
Bonferroni quotient estimate. Use the proof's finite combinatorial
multiplicity bounds to obtain a concrete universal constant in the local
second-order proposition.

## Stage 4: combinatorial dependency sums

Prove the ordered pair counts and the connected-triple classification.
It is acceptable to use the deliberately loose polynomial powers in the
paper; tightening these powers is not necessary for the fixed-p main
results. Avoid identifying executable enumeration with a universal theorem
without a proved checker.

## Stage 5: analytic degree profile

Separate the elementary incidence count from bounded-variation integration.
Formalize the entropy integral and its squared moment, then evaluate the
latter using the displayed partial-fraction series. This is independent
of the probability-space formalization.

## Stage 6: asymptotic assembly and lattice optimization

Use named deterministic big-O constants depending on fixed p, rather than
probabilistic O_p notation. Establish the weighted logarithmic band result,
the three-range global bound, smooth-mean transfer, and the compactness
reduction of the lattice maximization. The final liminf/limsup proof needs
a separate phase-accumulation lemma.

Suggested high-level dependency labels are also recorded in `claims.json`.
Finite Python tests are useful regression vectors at stages 1, 2, and 4;
they are not trusted proof dependencies.
