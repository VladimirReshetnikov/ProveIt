# Continuous-layer audit

## Deliverables

- `analytic_topology.tex`: complete human arguments, definitions, constants,
  hypotheses, source-status distinctions, and object-iPRA formalization plan.
- `AnalyticTopologyBlueprint.lean`: semantic definitions and exact propositions
  named `...Goal`. These define remaining proof targets; they are not theorem
  proofs and were not compiled in the authoring environment.
- `validate_continuous.py`: standard-library exact-rational implementation and
  finite verification of gluing and the singular cubic inverse.
- `continuous_validation.json`: observed output; 13,710 exact-rational checks
  passed. These checks are not universal proofs or iPRA derivations.
- `analytic_sources.json`: exact pinned source paths, blob SHAs and download hashes.

## What is reused, what is added

1. `CoherentMinimizer.cauchy` already proves the core quantitative-uniqueness
   reindexing estimate. Its source explicitly omits canonical evaluation and
   uniqueness of the completed point. The residual theorem here adds those
   two steps through a general completion interface. Do not advertise the
   Cauchy reindexing as a new discovery.
2. `FiniteGluing` glues finite tables by a first applicable patch under exact
   agreement. The new weighted theorem concerns continuously varying data,
   sample errors, positive denominator bounds and completed domains.
3. `StrongMinimizer` is a strong-convexity instance. The residual theorem
   abstracts its diameter principle beyond convex optimization.
4. `StableCubicRoot` and `CubicInverse` concern y^3+y. The worked y^3 inverse
   is distinct: derivative separation fails at zero, but an explicit Hölder
   diameter modulus still produces a coherent root name.
5. `ContractionIterates` already has deep finite contraction estimates. The
   completed fixed-point identity is the interface extension described here.
6. Earlier Cauchy/residue and calculus reports already contain rich analytic
   constructions. This chapter does not pretend to newly prove their results.

## Critical assumptions retained

- Every code, vector, rational and metric operation has a fixed PR evaluator.
  A family indexed by i means a fixed indexed evaluator or a fixed finite
  family, not a universal interpreter for arbitrary PR programs.
- A regular input name to gluing has every sample in the certified subdomain
  D0. Knowing only that its semantic limit lies in D0 is insufficient.
- Diagonal completion requires every row to be a regular name in addition
  to the four-index distance bound. The latter bound alone does not imply
  row regularity. This was found and corrected during independent review.
- Completeness concerns represented Cauchy sequences with a supplied joint
  family of names. No countable choice of quotient representatives is used.
- S >= delta > 0 is an explicit cover certificate. A finite net with margin
  can establish it; an unspecified open cover cannot supply it automatically.
- Local functions are used only under a positive support guard. The weighted
  proof treats active/inactive pairs explicitly and never assumes correctness
  of an inactive local value.
- Approximate overlap agreement yields approximate gluing. Exact gluing needs
  coherence of the fixed local routines and agreement to all precisions.
- Residual recovery needs both explicit approximate witnesses and a PR
  diameter modulus. Neither semantic uniqueness nor mere nonemptiness gives
  those data automatically.
- The semantic small-error argument for nonrational metrics is implemented
  through rational distance tests, not a hidden real-order decision.

## Constants checked

- Extension index h(n) = mu(n+2)+2 for monotone mu. Regularity uses a 1/2
  input slack; continuity uses 3/4 of the input threshold.
- Gluing Lipschitz C = L + 2*N*M/delta. The output coefficient error term is
  eps(p)+eps(q), without a factor N, because the weights sum to one.
- Name gluing b_n = U_(n+2)(x_(n+c)), C <= 2^(c-2), has pairwise error at
  most (eps(m)+eps(n))/2.
- Safe inner weights from named distances differ from true weights by at
  most 2*eps(t). If 2*N*eps(t) <= delta/2, their normalized value error is
  at most 8*M*N*eps(t)/delta.
- Cubic mesh J=2^(n+5), sample p=n+4: 6/J + eps(p) = eps(n+2).
- Global cubic separation |u-v|^3 <= 4|u^3-v^3|; the constant four is needed
  for opposite signs. Residual diameter kappa(k)=3k+3 is valid.
- Cube-root name z_k=a_(3k+9) is regular, and the inverse modulus is 3k+2.

## Formalization status

No new deep iPRA formal theorem is claimed by this chapter. Human proofs
have finite rational kernels and explicit QF induction invariants. The Lean
file records semantic interface definitions and exact remaining goals; the
root package must label these separately from any independently compiled
Lean core or existing upstream proofs. The pinned upstream build was not
rerun by this subtask.
