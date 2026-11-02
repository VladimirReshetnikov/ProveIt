# Conditional multiplier bound from a rank population estimate

[`Model69Growth.lean`](Model69Growth.lean) proves in any `IΣ₁` model that
`3*u+2≤count≤R` implies `2*u≤R`. It then proves `q≤w` when, additionally,
`q=Exp.exp u` and `w*q=Exp.exp R`.

This is a **conditional model lemma**. It does not prove that `count` is the
population of the actual 2011 carrier rank, derive the inequalities or
exponential equations from a positive parent zero, prove the rank phase, or
establish a graph bridge or iPRA equivalence. A possible caller is
`ArithmeticHalfBinomial2011.current_population_lower`, combined with
`ArithmeticBinaryPopulation.population_le` and
`ArithmeticCarrierRadix2011.current_power`; their actual-zero interfaces and
coherent imports still need to be linked. The bound `q≤w` is one hypothesis
of the separate [positive divisible transport](../thirteen-model-parent-transport/README.md).
The 2011 tuple and the previously materialized phase-split2471 tuple are
separate fixed instances.

## Paired replay

[`replay.py`](replay.py) compiles this source separately with both sides of
the [audited 70-source parent](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md),
checks direct imports and fixed inputs, and reruns the parent comparator before
and after. Session 55261 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_PARENT_GROWTH 5276d8d1ee367ce6ea079a710cfe6873dcfa4ff587be1a838a460acdc0237660`.
The [receipt](replay-receipt.json) records both compiler exits and direct
imports with matching object hashes, and the [terminal observation](terminal-observation.json)
records the actual wrapper exit. Both reports list `[propext, Classical.choice,
Quot.sound]`, with no warnings or `sorryAx`. An independent audit of this
suffix is pending. Lean metatheory axioms are not object-level iPRA axioms;
package-transitive/dynamic ancestry and the original Foundation wrapper's
unobserved exit retain the parent audit's qualifications.
