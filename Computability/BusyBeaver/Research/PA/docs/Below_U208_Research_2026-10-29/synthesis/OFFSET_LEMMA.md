# Head-offset quotient lemma and scope of the search

Let M have initial control0, haltH and a binary two-way tape. Choose a deleted
working control q, surviving representative r, and nonzero offset k. At an old
configuration (s,h,T), define the proposed new boundary configuration as
(r,h+k,T) if s=q, otherwise (s,h,T). Identifying controls does not identify the
logical old role: the proof follows a definite old computation.

For every retained ordinary row (s,b)->(w,d,z), use the row
(s,b)->(w,d+k*[z=q], rho(z)). This is a legal unit move precisely when that
new displacement is ±1. Since k=±2, all entrances to q must have the opposite
sign. The deleted q rows are not emitted. One optional helper row may instead
be modified; it then requires a separate checked macro obligation.

Assume an invariant I of all old reachable configurations. For each old q row
(and each optional modified helper row), require that the candidate, begun
at the proposed boundary, takes a positive finite number of steps to the
proposed boundary of the old one-step successor, changing exactly the same
tape cells. It must not halt in the interior. These requirements cover every
binary tape satisfying I, not just sample tapes. Ordinary rows commute with
the boundary map by direct inspection. The special requirements complete a
stepwise simulation.

By induction on old time, each old computation prefix has a corresponding new
prefix. Positive lengths ensure that an infinite old run gives an infinite new
run; the finite-block condition excludes a new halt between boundaries. An
old halt maps to the same halt. Determinism then proves halting equivalence.
If q is noninitial, both initial configurations agree. If q=0 and the tape is
all-zero, the proposed initial new head is k; translation invariance of a
homogeneous blank tape permits presenting the candidate with initial head0
and initial control r. This does NOT authorize deletion of runtime occurrences
of q without checking their macro obligations.

The implemented checker uses finite-history guards for noninitial controls.
For q=0 it uses the finite-window least fixed point starting at the all-zero
nine-cell window. Moving the window admits both newly exposed exterior bits;
therefore every actual blank-run window is included. This overapproximation
may include impossible windows and may prevent useful compressions.

The finite first-divergence filter is sound for its bounded contract: fix one
concrete input tape admitted by the old entry guard. If a proposed one-row edit
is not encountered along the unedited candidate's failing trace, the edited
candidate has exactly the same trace up to the same bound. Thus the edit
cannot repair that witness within the bound. This conclusion is intentionally
weaker than failure of blank-tape halting equivalence.

These elementary finite simulation arguments can be arithmetized in PA. No
formal PA derivation was exported, and no successful new machine is asserted.
