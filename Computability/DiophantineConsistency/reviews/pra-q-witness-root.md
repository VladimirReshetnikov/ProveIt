# Explicit order witness in candidate PRA

`PRAQOrderWitness.PRA_proves_orderWitness` gives an actual candidate-PRA
proof that `x<y` implies `x+succ(pred(y-x))=y`, with the witness expressed
as a fixed term in the candidate primitive-recursive language. It uses the
order characterization, subtraction reconstruction, and successor
exhaustion in arbitrary equality models. This is one concrete witness, not
a general Σ₁ witnessing theorem or PRA conservation.

The independent replay `/tmp/pra-q-witness-root-sefrxwpg` passed both
modules without warnings, matched the author object hashes, and reported
only `propext`, `Classical.choice`, and `Quot.sound`. The driver checks
current source/object hashes for the rebuilt subtraction-to-Q chain after
the upstream subtraction merge. Foundation, Mathlib, PRATheory and earlier
code providers remain inherited cache boundaries. The
[evidence packet](pra-q-witness-root-replay/) preserves prior exploratory
attempts including admitted probes 1, 2 and 5; none is used in the final
source or successful replay.
