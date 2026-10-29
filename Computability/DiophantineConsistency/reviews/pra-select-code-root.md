# Primitive-recursive selection in candidate PRA

`PRASelectCode` defines a finite PR recursion code that selects its third
argument when the test is zero and its second argument at any successor.
Both defining equations are closed candidate-PRA theorems; the composition
interface works in arbitrary equality models. This is a bounded-search
building block, not a completed search invariant or universal presentation.

The independent replay `/tmp/pra-select-code-root-z4iggwkd` passed both
modules without warnings and matched author object hashes; three axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`. It
used the independently replayed characteristic-bit provider and checked
current arithmetic source/object hashes. Foundation, Mathlib, PRATheory
and earlier code providers remain inherited cache boundaries. The
[evidence packet](pra-select-code-root-replay/) preserves both builds.
