SCALAR NAMES WITHOUT A SCOPE FLOOR -- COMPLETION WITH WRITTEN PROOFS
====================================================================

This directory contains a complete standalone checker under its stated
compact input contract, an untrusted finite-fixture translator, executable
positive and negative cases, and a verification receipt. It does not improve
the current source-size frontier and does not delete a logical or arithmetic
axiom. The scalar native calculus and sorted raw-tree interpretation are
inherited from ConciseIPRA.

The mathematical implementation change removes the global parameter floor.
All negative integer leaves are fixed free parameter names. On a nonterminal
call with current context g, goal a, and input packet r, the checker chooses

    fresh = -10 ** len(str([g, a, r])).

The bound is calculated before changing the goal and before checking the
major subproof. It exceeds in magnitude every integer occurring anywhere
in the current context, goal, and packet. Thus it cannot already occur in
any expression for which that inference requires an eigenvariable condition.
The same plain integer/list term representation is retained.

PRIOR ART AND CLAIM STATUS

The repository already describes an uncertified long_names.py experiment in
Artifacts/selfseed_scalar/evidence/kernel_research_notes.txt. That note says
it removes the floor and chooses a negative name larger than a decimal
encoding of the present sequent; it lacked a full alias audit and producer,
and was not selected. Therefore decimal-dominating names are NOT claimed as
a new idea here. The current contribution is a concrete early-allocation
implementation, precise freshness argument, executable name compilation,
an actual induction subderivation, and a scalar capture counterexample to
the fixed-name shortcut. It is a completion/composition of an earlier idea.

The main report carries the inherited sorted-reading soundness argument.
The finite receipt here is corroboration, not a substitute for that proof.
There is no Lean or Rocq verification of this particular Python module.

CONTRACT

Input is a finite stream of JSON lines. The first line is a canonical closed
guarded Eq/D formula in the repository's unshifted arity codec. Every consumed
later line is a three-field packet [s,u,t]. Numerical/formula data are exact
integers and lists. The compact program does not separately validate this
public grammar or the exact input alphabet. Internal auxiliary Q formulas
and raw aliases have the inherited sorted reading. Unused trailing lines
are permitted. Acceptance is normal exit with exactly ACCEPT and one LF.

Exceptions reject. Ideal unbounded resources are understood, as for the
baseline recursive Python checker. In practice use

    python3 -X int_max_str_digits=0 checker.py < fixtures/induction.jsonl

The runtime option removes Python's decimal conversion resource cap. It
does not add an arithmetic or logical axiom. Recursion and memory limits
remain practical limits; no real finite-resource runtime proves mathematical
completeness merely by running a finite suite.

REPRODUCE

    python3 verify.py

CPython 3.12.14, normalized by ast.unparse plus one LF:

                          tokens   AST   normalized bytes
    checker.py               249   272                549
    control239.py            239   261                549

Thus the construction ties its matched control in bytes and loses in the
other two coordinates. It is larger than the compact byte record. It must
not be represented as satisfying the user's global size target.

The receipt records 47 isolated CLI expectations, ordinary and optimized
Python, with zero failed expectations. Seven positive cases include both
computation clauses, inferred equality elimination, shared computation,
and an induction subderivation using its hypothesis. Every positive stream
is also tested after replacing its displayed conclusion by 0=1. Five
negative cases cover false equations, wrong computation, context leakage,
and attempted witness capture. A temporary deliberately unsound control
that fixes fresh=-1 accepts the false capture theorem, while checker.py
rejects exactly that stream.

THE INDUCTION FILES

fixtures/induction.jsonl is a canonical public arithmetic theorem, proved
through an intermediate derivation of the closure of

    E(y): I(y,0;u.u)=0.

The progress subproof checks I(S z,0;u.u)=I(z,0;u.u) by computation, then
uses the retained E(z) to infer E(S z) by transport. That closure is opened
and discharged before finishing the public computation theorem. The
induction is therefore genuinely traversed and its hypothesis consumed,
although the final arithmetic theorem also has a shorter direct proof.

fixtures/closure.jsonl exposes the corresponding auxiliary Q closure as
its output. It is a diagnostic of the internal raw language; it is not a
canonical Eq/D public-root example. Both source fixtures have seven packets.

fixtures/specialization.jsonl uses that proved Q closure by elimination
with its zero base, obtaining the canonical public conclusion
I(S(0),0;u.u)=0. Its closure is consumed rather than merely discharged.

The forced-induction arithmetic certificate is 209 bytes; the closure
diagnostic is 229 bytes. The largest fresh name allocated in this small example has
214 decimal digits (not every allocated name has to appear in the stream).

PRACTICAL LIMITATION

Names can grow extremely quickly because a fresh name's digit count exceeds
the entire displayed old state. Translating the larger inherited guarded
induction fixture exceeded a diagnostic producer cap of 2,000,000 decimal
digits. The producer stopped without claiming that fixture had been run.
That cap belongs only to untrusted tooling, not to the checker. The example
shows why this simpler scope invariant does not by itself yield a better
practical proof format.

ATTRIBUTION

Baseline checker, five inherited rejection fixtures, and four inherited
computation/elimination fixtures were obtained from the structural_parameters
incoming archive in VladimirReshetnikov/ProveIt at commit
65c32fbe4730bfe5a064502b0b95ebc798c732fa. Its translator, adapted here, was
itself built for the fused_blocks_and_checkers 239-token stream protocol.
The three small induction source streams were constructed in this investigation.
The scalar fixed-name attack is adapted from the upstream opaque-name attack
by replacing its opaque atom [0,0,0,0] with the scalar parameter -1.
