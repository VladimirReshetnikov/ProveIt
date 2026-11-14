Additional PA194 state-reduction experiments
===========================================

This directory contains unsuccessful searches performed on PA194N6 and a
new, logically motivated formula-code experiment. It contains no accepted
machine smaller than 194 states. These negative results are finite and do
not imply a lower bound on arbitrary consistency machines.

The exact N6 input is the existing 194-state machine with native start 74,
halt 254, and SHA256
63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a.

1. Longer local windows and a halting-aware equivalence
------------------------------------------------------

The generic collector covers every source outcome, the interiors of all
accelerated unary scans, four independently derived generic list lemmas,
and the full 58,320-step blank startup. It extends the prior radius 5 screen
to radius 8 (17 cells). The local search allows any final tape/head effects
when the old transition halts; its other endpoints must match exactly.

The common-action merger seeks a single replacement control for two old
controls, while ensuring the replacement traces avoid changes to the other
control. The per-edge bypass removes a non-self-looping control and allows
each incoming row a different replacement action. Every proposed local
trace is bounded by 300 steps and by the supplied window. No accepted
candidate was found in the completed screens recorded in RESULTS.json.

2. Reachability invariants at source sites
----------------------------------------

check_invariants.py checks the finite inductive closure of a product
abstract domain with three classes: zero, one, and at least two. The seed
is source site 25 with logical registers (2,0,0,0,0,0,0,0,0).

The certificate establishes 3,775 reachable sites in the overapproximation,
one unreachable jump(site 8), and a zero-only decrement at site 7. It reduces
the primitive outcomes that need consideration from 4,877 to 4,875. It also
specializes 3,361 source/register coordinates to zero and 6,167 to positive
values. The specialized literal collector remains conservative and obtains
29,262 radius 5 windows over all 194 controls. Both local operators find no
candidate with a 300-step bound, even allowing arbitrary halting effects.

python3 -B replay.py

repeats the invariant check and all frozen-context local screens. Add
--collect to regenerate the symbolic contexts, which takes several minutes.
Python 3.10+ and a C++17 compiler suffice; no network or checkout is needed.

3. Nested tags with a binary implication constructor
----------------------------------------------------

The new proposed encoding uses J(a,b)=2*p(a,b), where p is Cantor pairing:

    I(A,B)=J(A,B)
    U(a,B)=J(B,a+1)+1
    M(a,b)=J(J(a,b),0)+1
    E(a,b)=J(J(a,b)+1,0)+1.

Even codes encode implications. For an odd code, unpair(n-1)/2 as(r,s).
If s>0 it denotes U(s-1,r). If s=0, parity of r distinguishes membership
from equality, followed by unpairing floor(r/2). The special truth code 0
and false code 1 are retained. This is a total syntax recoding; its separate
logical argument is not an assertion that this search produced a small TM.

The primitive multiplication-by-four control can be removed, giving a
133-control fixed scaffold. The exact emitter suffix rewrites are

    Cons;inc       -> Cons;Push;Cons;inc
    Cons;inc;inc   -> inc;Cons;inc
    Cons;inc^3     -> Cons;inc;Push;Cons;inc.

The AX word grows from 190 to 213 tokens: 10 membership and 3 equality
constructors contribute 23 extra tokens;15 universal and 31 implication
constructors incur no additional token count. A bounded grammar experiment
made 633,781 proposals and accepted 124,495 within 180 seconds. The best
scored grammar had 81 raw readers, 11 nominal folds, and 4 scanner penalties,
for score 74. It is not a validated machine or an optimality certificate.
In particular, incompatible folds and scanner penalties may increase the
real implementation cost. No 193- or 194-state candidate resulted.

From nested2_experiment, run python3 nested2_prepare.py to regenerate the
frozen grammar input. Compile nested2/search.cpp using C++17 and replay the
command recorded in nested2_experiment/REPLAY.txt. The search is stochastic
and time limited; proposal counts depend on the machine. Its input word,
seed, source code, saved best grammar and observed log are preserved.

Provenance and proof scope
--------------------------

All baseline data derive from ProveIt commit
317b07268681b44ff352d173a162e2a8c241b2fe, notably the primary PA194 packet
and the PA194N6 packet. Original notices are retained in licenses and
beside runtime code. The new work here is the longer-window search,
halting-aware endpoint rule, source invariant specialization, and nested
tag experiment. Executable symbolic evidence is not a new Lean/Rocq theorem.
