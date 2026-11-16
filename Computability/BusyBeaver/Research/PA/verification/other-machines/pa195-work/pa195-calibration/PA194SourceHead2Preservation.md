# Numerical source head2 preservation

`PA194SourceHead2Preservation.head2` proves that every numerical head2
instance translates to an internally PA-provable formula. Writing
`I(p,q) = 4·cantor(p,q)` and `U(x,p) = 4·cantor(p,x)+2`, the source code is
`I(U(d,U(a,h)),U(a,U(d,h)))`. It covers arbitrary model-valued `d`, `a`, and
`h`, including nonstandard values. The outer implication has a nonzero
antecedent because it is a universal code, so the code-zero implication alias
cannot occur.

The model assumptions are a nonempty model of the candidate PRA language,
with equality, satisfying the candidate PRA axioms, whose arithmetic reduct
satisfies IΣ₁. The conclusion is Foundation's internal PA provability
predicate in that model. This is not an iPRA theorem about PA194, a finite
proof transformer, or preservation of the remaining seed families.

For distinct labels, `PA194SourceHead2Syntax.close_swap_formula` proves that
reversing the capture-avoiding closings is the same as exchanging their two
bound variables. Its induction applies to arbitrary internally well-formed
formulas and depths, including nonstandard ones. `PA194SourceHead2Logic`
constructs the corresponding internal PA derivation exchanging the two
universal binders. Equal labels give the identity implication directly.

The full `check-source-head2-preservation.sh` rebuilds the dependencies and
three new modules in a fresh temporary directory and rejects `sorryAx`; it
requires the matching audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY`. The full nested rebuild is deferred because of
disk I/O pressure; the focused ordered suffix replay uses retained
prerequisite objects and does not independently rebuild them.

The author's focused ordered suffix replay passed without `sorryAx`. An
independent ordered suffix replay also rebuilt the three new modules without
`sorryAx`, using separately checked head1/head5 and retained prerequisite
objects.
