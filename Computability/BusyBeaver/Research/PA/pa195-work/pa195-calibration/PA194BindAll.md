# Binding all internal free labels

The `PA194BindAllTerm` and `PA194BindAllFormula` modules construct a uniform Foundation recursion in every IΣ₁ arithmetic model. At binder depth `d`, it replaces each free label `x` by bound index `d+x` and preserves existing bound indices. The code handles arbitrary internally well-formed terms and formulas, including nonstandard codes. `PA194BindAllFormula.bindAll_wf_fixed` proves that the resulting formula is internally well formed and shift-fixed, i.e. a prospective closure body. No free-label bound is assumed in that construction.

`PA194BindAllTerm.bindAll_decode` proves the corresponding term-level inverse when the output is well formed at a supplied target bound and the supplied substitution vector maps the local bound slots to themselves and the new slots back to their free labels. `PA194BindAllMap` gives the vector invariant, proves it survives a binder via `qVec`, and proves that `fvarVec N` satisfies it at depth zero.

The formula-level decoding theorem and its application with `N = bv` of the resulting body are still open. Thus this package does not yet construct all induction-axiom recognizer witnesses, prove arbitrary-formula PA induction, bounded comprehension, the distinct-label gate, or an iPRA implication.

The author replay ran `check-bind-all.sh` against the pinned Foundation overlay, rebuilding the local prerequisite and three new modules. Printed axioms are `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
