# Set Theory

This topic contains set theory; the merged Cardinals package below also carries
one computability project and unrelated research reports.

- [`ZF/`](ZF/) supplies reusable first-order ZF syntax/axioms, semantic
  bridges, internal set algebra, and the finite-recursion theorem needed by
  the Closure result.
- [`ClosureAxiomatization/`](ClosureAxiomatization/) proves that replacing
  Pairing, Union, Infinity, and Replacement by the set-like-relation Closure
  schema is semantically and deductively equivalent to ordinary ZF.
- [`Cardinals/`](Cardinals/) is the former
  [VladimirReshetnikov/Cardinals](https://github.com/VladimirReshetnikov/Cardinals)
  repository, merged here with its full history. Its lead project formalizes
  a synthesis of research reports on exacting, ultraexacting and
  cover-exacting cardinals (in ZFC, a cover-exacting cardinal cannot lie
  between two strongly compact cardinals). The same Lake package also holds
  the coarse-Turing-degrees project (`CoarseDegrees/`, which disproves C1)
  and 104 further research reports without Lean counterparts; they were kept
  together with the cardinal work so the package and history stay whole. It
  requires this repository's root by path
  (`lake --dir SetTheory/Cardinals build`).

Generic first-order logic lives under [`../Logic/FirstOrder/`](../Logic/FirstOrder/);
PA/HF interpretability under [`../Logic/Interpretability/PAHF/`](../Logic/Interpretability/PAHF/);
Busy Beaver under [`../Computability/BusyBeaver/`](../Computability/BusyBeaver/);
coarse Turing degrees, a computability project, under
[`Cardinals/CoarseDegrees/`](Cardinals/CoarseDegrees/) for the reason above;
and the arithmetic RH sentence under
[`../NumberTheory/RiemannHypothesis/PAStatement/`](../NumberTheory/RiemannHypothesis/PAStatement/).
