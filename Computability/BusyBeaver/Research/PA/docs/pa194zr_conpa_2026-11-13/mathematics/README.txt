Auxiliary antecedent-exchange experiment
========================================

exchange_template.py checks the finite pure-implication derivation
(P -> (Q -> R)) -> (Q -> (P -> R)) from K, S and modus ponens.
It contains 161 distinct proof DAG nodes: 42 K instances, 39 S instances,
and 80 modus-ponens nodes, with no remaining assumptions.

The unchanged restricted rho8 basis supplies K and S through the inherited
PA196 implication-basis theorem. This script checks only the displayed
exchange template; it is not a new proof of that basis theorem.
It supports exploration of exchanging h3/h6 antecedents in the decoder
search. PA194ZR itself keeps the original axiom heads and does not use
this auxiliary certificate.

Run from the package root:
  python3 -B mathematics/exchange_template.py

The 27 numerical alias checks are sanity checks in addition to the complete
symbolic schema derivation; they are not the universal proof by themselves.
