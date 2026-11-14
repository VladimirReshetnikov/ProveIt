Optional negative-vacuity Gamma witness PA195N
=============================================

This is an optional 195-state source variant found at proposal 7,103,587
of the corrected dual-Gamma search. It is not a result below 195 and is
not the primary PA195DC deliverable.

The exact logical change is to replace the diagonal gate formula

    Gamma(A) = A -> U(A,A)

by

    Gamma_minus(A) = (A -> 1) -> U(A, A -> 1).

All first 121 macro tokens, the six ordinary heads, their order, the
restricted rho8 head, and the outer controller remain unchanged. The
complete emitter has 197 tokens. This candidate has 134 fixed states plus
71 AX reader nodes minus 10 compatible history folds, giving 195 working
states. The intended logical calibration uses the equivalence of positive
and negative vacuity in the retained classical calculus; that additional
mathematical argument is not newly kernel-checked by this optional folder.

Finite checks passed: 40 complete two-cell fold cases; 4937 symbolic source
contracts for both raw and folded tables; the complete free-algebra emitter
identity with Gamma_minus; unchanged arithmetic-box rows; exact 58154-step
blank initialization; and agreement of independent source CFG resolvers
for all 3794 source sites. These checks are reproducible with the primary
packet's inherited baseline directory:

    python3 verify.py ../../../machine/baseline195

The executable receipt certifies those finite implementation obligations.
It does not by itself prove the full arithmetic consistency biconditional,
and this optional witness is not used to justify the report's main result.
