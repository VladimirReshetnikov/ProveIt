# Numerical source head1 preservation

`PA194SourceHead1Preservation.head1` proves that every numerical head1
instance translates to an internally PA-provable formula. Writing
`I(a,b) = 4·cantor(a,b)`, `U(x,p) = 4·cantor(p,x)+2`, and
`ex(x,p) = I(U(x,I(p,1)),1)`, its source code is
`I(ex(label,U(label,h)),h)`. The theorem covers arbitrary model-valued
`label` and `h`, including nonstandard values. Every implication expanded in
the proof has a nonzero left argument, including the outer one, so the
code-zero implication alias does not apply.

The model assumptions are a nonempty model of the candidate PRA language,
with its equality structure, satisfying the candidate PRA axioms, whose
arithmetic reduct satisfies IΣ₁. The conclusion is Foundation's internal PA
provability predicate in that model. This does not establish an iPRA theorem
about PA194, a finite proof transformer, or soundness of the remaining seeds.

`PA194SourceHead1Syntax` proves the internal syntax facts used in the
argument: closing then reopening with the same label recovers any internally
well-formed formula, and a second closing of the same label at the next depth
has no effect. It also proves that substitution ignores an extra vector entry
when the input formula has no corresponding bound variable. These facts apply
to nonstandard internal formulas, not just quotations of standard syntax.
`PA194SourceHead1Logic` uses them to derive the required quantifier
implication in internal PA. The source code `1` is handled as a diagonal bit
formula and the head5 package supplies an internal PA proof of its negation;
it is not assumed to be syntactic falsity.

The full check `check-source-head1-preservation.sh` builds the dependencies and
three new modules in a fresh temporary directory and rejects `sorryAx`. It
requires the matching audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY`. A full nested rebuild is deferred because of disk
I/O pressure; the focused ordered suffix replay uses retained prerequisite
objects, and does not independently rebuild them.

The author's focused ordered suffix replay passed without `sorryAx`. An
independent ordered suffix replay also rebuilt the three new modules without
`sorryAx`, using separately checked head5 and retained prerequisite objects.
