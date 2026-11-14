# Numerical source diagonal preservation

`PA194SourceDiagonalPreservation.diagonal` proves that every separate
numerical diagonal seed translates to an internally PA-provable formula.
Writing `I(p,q) = 4·cantor(p,q)` and `U(x,p) = 4·cantor(p,x)+2`, the source
code is `I(c,U(c,c))`. It covers every model-valued `c`, including nonstandard
values and `c=0`. Even when `c=0`, the implication is nonzero because its
consequent is a universal code, so the zero alias does not apply.

The model assumptions are a nonempty model of the candidate PRA language,
with equality, satisfying candidate PRA, whose arithmetic reduct satisfies
IΣ₁. The conclusion is Foundation's internal PA provability predicate in
that model. It does not establish an iPRA theorem about PA194, a finite proof
transformer, or preservation of the guarded gate.

The key invariant `source_bounded_fresh` is proved by IΣ₁ strong induction
on arbitrary internal source codes: a label greater than or equal to the
source code can be renamed to its successor without changing the positive
arithmetic translation. It handles zero, all four constructor tags, and
both children of an implication. `PA194SourceFreshClose` proves, for
arbitrary internally well-formed arithmetic syntax, that this renaming
invariance is preserved by closing any label and entails that closing the
fresh label has no effect. Thus the proof does not rely on checking only
standard source formulas or on a semantic truth predicate for nonstandard
formulas.

The full `check-source-diagonal-preservation.sh` rebuilds the dependencies
and the two new modules in a fresh temporary directory and rejects `sorryAx`;
it requires the matching audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY`. A full nested rebuild is deferred because of disk
I/O pressure; the focused ordered suffix replay uses retained prerequisite
objects and does not independently rebuild them.

The author's focused ordered suffix replay passed without `sorryAx`. An
independent ordered suffix replay also rebuilt the two new modules without
`sorryAx`, using separately checked head2/head1/head5 and retained
prerequisite objects.
