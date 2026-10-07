# Set Theory

This topic contains set theory; the `Cardinals` package below also holds a
collection of research reports on other subjects.

- [`ZF/`](ZF/) supplies reusable first-order ZF syntax/axioms, semantic
  bridges, internal set algebra, and the finite-recursion theorem needed by
  the Closure result. The research report
  [`Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings`](Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/)
  (batch 89) continues this interface semantically: it computes exactly when
  naming elementary self-embeddings of urelement kernel models keeps
  Replacement, Collection and reflection in the expanded language, and
  proposes a formalization route; its Part II (batch 93) reads `Zf.lean`
  again for commuting named actions and proposes further milestones. It is
  unrefereed and not formalized; this project's `Form` has no atom
  predicate or function symbols.
- [`ClosureAxiomatization/`](ClosureAxiomatization/) proves that replacing
  Pairing, Union, Infinity, and Replacement by the set-like-relation Closure
  schema is semantically and deductively equivalent to ordinary ZF.
- [`Cardinals/`](Cardinals/) studies exacting, ultraexacting and
  cover-exacting cardinals: research reports, a synthesis stating each result
  once in its strongest form (in ZFC, a cover-exacting cardinal cannot lie
  between two strongly compact cardinals), and a Lean formalization of the
  synthesis's ZFC theorems about a single witness in Mathlib's `ZFSet`. The
  Lean library closes nineteen published results with `admit`, which no
  other ProveIt set-theory project does; `Cardinals/Cardinals/README.md`
  lists them and its audit exposes them. The directory also holds 247
  research reports without Lean counterparts, on ordinals and
  well-quasi-orders, Hankel determinants, supercongruences, tetration,
  log-concavity, graphs, automata, enumerative combinatorics,
  generating-function asymptotics, quaternionic analysis, the Jacobian
  conjecture, radicals, and Diophantine representations of computation.
  It is a Lake package that requires this repository's root by path
  (`lake --dir SetTheory/Cardinals build`).

Generic first-order logic lives under [`../Logic/FirstOrder/`](../Logic/FirstOrder/);
PA/HF interpretability under [`../Logic/Interpretability/PAHF/`](../Logic/Interpretability/PAHF/);
Busy Beaver under [`../Computability/BusyBeaver/`](../Computability/BusyBeaver/);
and the arithmetic RH sentence under
[`../NumberTheory/RiemannHypothesis/PAStatement/`](../NumberTheory/RiemannHypothesis/PAStatement/).
