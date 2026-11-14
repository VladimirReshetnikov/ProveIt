# Internal bounded-comprehension successor template

`PA194ComprehensionStep.step_body` works for every arithmetic model of IΣ₁, arbitrary internally well-formed one-variable formula `P` and model labels `a,u,v`, including nonstandard ones. Inside PA it proves that if `u` codes exactly the elements `x<a` satisfying `P(x)`, and `v` extends `u` by `a` precisely when `P(a)` holds, then `v` codes exactly the elements `x<a+1` satisfying `P(x)`. The hypotheses and conclusion are explicit universally quantified formulas using the fixed bit and order templates.

The proof uses a model-uniform pointwise propositional derivation, lifts it beneath the universal quantifier, derives equality substitution for arbitrary internal `P`, and supplies the fixed successor-order identity. It proves the successor relationship conditional on concrete old and new set witnesses. Constructing the existential witnesses and completing the induction, the distinct-label gate, an iPRA implication, and the machine equivalence remain open.

The author focused replay rebuilt the four new modules in order against separately checked prerequisite overlays, with no `sorryAx`; the replayable entry point is `check-comprehension-step-suffix.sh`. The full nested dependency rebuild has not been repeated for this suffix.
