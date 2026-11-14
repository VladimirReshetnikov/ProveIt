# PAeq source-syntax rewriting

`PA194PAeq.formula_rew` proves that the standard source-syntax translation
into the PAeq language commutes with arbitrary syntactic rewriting, including
under quantifiers and the extra existential binder used by the less-than
translation. The companion lemmas cover terms and atomic formulas. These are
Lean theorems about standard syntax; they do not replace the separate
all-model theorem for numeric codes or supply a PA-axiom proof on their own.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited
Foundation object directory and run `check.sh`. An independent build of the
PAeq syntax and rewriting modules passed without `sorryAx`.
