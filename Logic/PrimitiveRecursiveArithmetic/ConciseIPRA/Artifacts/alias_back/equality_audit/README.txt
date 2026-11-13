ALIAS AND BACKWARD SUBSTITUTION: INDEPENDENT EQUALITY-FRAGMENT AUDIT

This directory supports the new raw equality basis. It is not the complete
iPRA checker, and it is not a Lean/Rocq formalization.

Read alias_back_theorem.tex for the written derivations, all-context
comparison with the native kernel, exact freshness conditions, variable-only
QE lemma, and the distinction between unrestricted and newest-only Back.

The independent checker has only Hyp, Alias and Back. There is no primitive
reflexivity, computation, normalization, or induction rule. It validates
raw iterator and Q/D syntax. A unary pred constructor is included solely to
check a finite schematic formula-transport derivation.

Free numerical parameters are named, while bound numerical variables use
de Bruijn indices. Thus substitution of a locally closed term for a free
parameter is capture-free even beneath iterator or logical binders. Alias
checks its replacement term in the parent scope, before adding the fresh
parameter. Back can select any current parameter, and its replacement may
contain that parameter.

Run:
  python3 verify.py
  python3 checker.py < certificates/schematic_formula_transport.json

The build_certificates.py producer is untrusted. Its weaken function shifts
local hypothesis indices when a new assumption is inserted after the old
retained context. The independent checker rechecks the produced proof tree.

Observed evidence: seven positive certificate files and twelve targeted
negative controls, each checked normally and with -O, yield 38 process
executions and zero failed expected outcomes. Finite checks supplement the
written general proofs. No complete-checker size record is assigned to this
auxiliary verifier.
