# Q theorem translation into candidate PRA

`PRAQProofTranslation.PRA_proves_qTheorem` proves that every theorem of
Foundation Robinson Q has a candidate-PRA proof of the sentence mapped
through the concrete language embedding. It combines the all-Q axiom images
with first-order soundness, the actual reduct semantics, and completeness.
This is an existence result; no effective proof transformer, standard-PRA
comparison, or Parsons conservation theorem is claimed.

The independent replay `/tmp/pra-q-translation-root-19v3ra2v` passed both
files without warnings and matched the author object hashes; the axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. It
uses the independently replayed Q-order and reconstruction providers and
checks source and object hashes of the refreshed order prerequisites.
Foundation, Mathlib, PRATheory and earlier code providers remain inherited
cache boundaries. The [evidence packet](pra-q-translation-root-replay/)
preserves the author attempts, including an initial namespace failure.
