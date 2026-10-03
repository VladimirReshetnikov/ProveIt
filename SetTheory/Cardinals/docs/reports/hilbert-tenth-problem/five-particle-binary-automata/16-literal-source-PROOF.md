# Literal universal reversible two-counter source: theorem and composition

Date: 3 October 2026. This is a mathematical construction with executable
checks, not a proof-assistant formalization. No novelty, smallest-machine,
resource-record, or efficient simulation claim is made.

## 1. Exact theorem and domains

Let U be the Neary–Woods 15-state, two-symbol universal Turing machine in
Table 16 of *Four Small Universal Turing Machines*, Fundamenta Informaticae
91 (2009), 105–126, DOI
[10.3233/FI-2009-0008](https://doi.org/10.3233/FI-2009-0008).
Let M be exactly `source.json`, with SHA-256
`38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`.
Its step relation is an injective partial function on all
`Q × N × N`, not only on encoded or reachable configurations.
It has 122,622 controls and 141,561 literal branches. `START` has no incoming
branch at all. `HALT` has no outgoing branch at all.

For all natural L,R,T and all positive C coprime to 2310, M started at

    (START, C·2^L·3^R·5^T, 0)

reaches `HALT` if and only if U, started in state A (u1), scanning 0 (c),
with the left and right half tapes encoded by L,R, reaches its undefined
J1 (u10,b) transition. The redundant initial scratch exponent T is cleared
by the simulated three-counter prologue, without losing its history in M.
In particular, set T=0,C=1 to obtain a finite computable input family.
Neary–Woods’ finite program/data encoding is contained in this input family,
so this one fixed literal M is computation-universal.

The universal-input promise is not “all positive integers in the first
counter, arbitrary second counter.” A clean loader has H=W=0 at the
five-counter level, so no initial 7 or 11 exponent is supplied. The proof
can accommodate arbitrary initial history H, but the advertised loader uses
H=0; arbitrary work W is not covered by the simulation theorem.
This restriction does not limit the global partial-injection statement.
Invalid encodings are still governed by the same globally injective partial
transition table, but can get stuck.

## 2. Primary machine and finite-input loader

The author-hosted primary article is
[Neary–Woods PDF](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf).
The locally available primary PDF was rendered and visually inspected at
printed pp.112 and121 (PDF pages8 and17). Table16’s 30 entries agree with
`dependency/tm_table.json`; the compact table bytes are pinned in
`dependency/UniversalTM15x2.tm.txt`. A separate primary comparison receipt
records every entry. The undefined cell is u10,b, not u10,c. The known
prose/display discrepancy on printed123 is not resolved by changing the
literal table.

Definition3.1, equations(3)–(4), Tables1–3, and Section3.5 describe the finite
program/data encoding. In Table1 the U15,2 separator G is bc and the initial
head is over G’s rightmost symbol, namely c. Thus fixing the scanned bit to0
and starting in A0 does not omit the universal input family. Both infinite
tails are blank c, not nonblank periodic backgrounds. The dependency’s old
bibliographic comment has inaccurate page numbers; the citation above is
the corrected one without altering that pinned dependency file.

Here is the complete loader from an already specified finite binary tape.
The head is at coordinate0 with bit0; let `left[i]` be the bit at
coordinate−i−1 and `right[i]` the bit at coordinate i+1. Both strings are
finite and nearest-head-first. Omitted symbols are0. Compute

    L = sum_i left[i]·2^i,   R = sum_i right[i]·2^i,
    A = 2^L·3^R,            B = 0.

Return `(START,A,B)`. `loader.py:from_tape` implements precisely these finite
sums and powers, with exact type/alphabet checks. It does not simulate U,
solve a halting problem, consult a callback, or decode an infinite object.
Every input yields finite natural numbers. Practical memory grows very fast;
no efficient conversion claim is made. `from_counters` provides the optional
T,C interface above and rejects a non-coprime cofactor.

Starting from any TM or bi-tag program/data pair, first use the finite
encoding of the cited primary theorem, then split that finite tape at its
head and apply this loader. The program-to-universal-tape theorem is the
published universality dependency; the loader thereafter is completely
specified and implemented here. No unimplemented interpreter is hidden in
the literal transition rows.

## 3. U to three natural counters

The pinned 528-row program stores the scanned bit in control, half tapes in
L,R (low bit nearest the head), and scratch in T. At a TM cut T=0. Its
prologue decrements arbitrary initial T to0, costing T+1 combined instructions.
All its non-halt instructions are enabled on every natural input.

For a TM move, let X be the half tape in the movement direction, let Y be
the other half tape, and write X=2Q+r with r∈{0,1}. The pop loop removes
two X units and adds one T unit per full iteration. At iteration k it has
X=2(Q−k)+r,T=k. Its rank is Q−k. The zero exit identifies r in finite
control. A transfer loop preserves X+T=Q and decreases T until X=Q,T=0.
This costs 5Q+r+2 combined instructions.

The push loop consumes Y one unit at a time and adds two T units; after k
iterations Y=Yold−k,T=2k. Its rank is Y. A restoration loop transfers all
T back to Y and decreases T, giving Y=2Yold,T=0. Add the written bit w
(0 or1), if necessary, and enter control (next state,r). This costs
7Yold+2+w. Overall the exact TM-step clock at this layer is

    5Q+r+7Yold+w+4.

The resulting half tapes and scanned bit are exactly those of U. Every loop
terminates by the stated rank and has no internal halt. `verify_virtual3.py`
checks the literal saved rows through437 affine paths covering every one of
the528 rows, all29 defined TM cases, and their destinations. The underlying
all-input proof is also pinned in `dependency/PROOF.md`, Section3. TM cuts
require the control AND T=0; the pop loop may revisit a cut label with T>0.

Induction on TM steps gives equality of every finite simulated prefix and
halting equivalence for arbitrary natural L,R. Infinite TM runs give infinite
counter runs since each enabled macro has finite positive duration.

## 4. Separate primitives, fresh start, and bounded indegree

Combined SUB is not used as a reversible primitive. Each combined SUB is
split into a zero test directly to its zero destination and a positive test
to a private state followed by one decrement. A positive SUB costs2 and a
zero SUB costs1; ADD costs1. A fresh START identity edge is inserted at this
irreversible stage, BEFORE reversibilization. The old `init_clear_T` has a
self-loop and is not falsely declared predecessor-free.

For each target with k>2 incoming edges, ordered e1,...,ek, introduce k−2
fresh merge controls and connect them into a one-way identity chain. The
first two edges enter the first merge, e_j enters merge j−1 for3≤j<k,
and e_k enters the original target. The chain ranks down its remaining
length. This preserves every edge’s operation and reaches its original
target after k−max(2,j) additional identity steps. State-by-state canonical
reconstruction is checked independently. This gives995 rows/763 controls
before normalization and1024 rows/792 controls afterward. Sixteen targets
require29 new merge states.

The start still has no incoming edge, and the halt has no outgoing edge.
No reversible edge is prepended later. No source row or infinite-input
promise is substituted from the old nonreversible8408-row table.

## 5. Reversible history and prime encoding

The conversion follows the constructions in Morita,
*Universality of a reversible two-counter machine*, TCS168 (1996),303–320,
[DOI](https://doi.org/10.1016/S0304-3975(96)00081-3), Theorem3.1 and
Theorem4.1, printed308–309 and314–316.
Primary text extraction was read. Its visual scan could not be retrieved:
PDF screenshots failed and a live fetch returned HTML. We therefore do not
claim a pixel-perfect transcription of ambiguous OCR. Instead, every graph
used here is explicitly enumerated, independently reconstructed, and proved
by its own invariants. None of the theorem below depends on guessing an OCR
symbol correctly.

`independent-macro-audit.md` contains the complete macro proofs, not merely a
reference to Morita. They establish:

- History boundaries satisfy `(data,H=h,W=0)`. A noncolliding source edge
  costs1 and leaves H,W. Each colliding pair branch b∈{0,1} executes its
  source operation then maps `(h,0)` to `(2h+b,0)` in exactly10h+4+2b steps
- History transfer invariant: `(H,W)=(h−j,j)`; decreasing rank H
- History doubling invariant: `(H,W)=(b+2j,h−j)`; decreasing rank W
- Prime boundaries encode the five counters by
  `A=C·2^L·3^R·5^T·7^H·11^W,B=0`
- A prime multiplication at N has common-transfer invariant `(A,B)=(N−j,j)`
  and multiply invariant `(A,B)=(pj,N−j)`; both ranks decrease
- Enabled prime division, N=pQ, has division invariant
  `(A,B)=(j,p(Q−j))`, so every required decrement is enabled; rank Q−j
- A prime test records the remainder r in bounded finite control, obtains
  `(0,Q)` for N=pQ+r, and a destination-shared restorer returns `(N,0)`
  with invariant `(A,B)=(r+pj,Q−j)` and decreasing rank B

Restorers are shared by destination, as required for global reversibility.
Per-edge copies would give overlapping final B=0 ranges at a shared target.
The five-counter table has233 recording pairs,5451 rows,4520 controls.
The two-counter graph has4519 source macros and2330 shared restorers.
All these macros are FULLY EXPANDED in `source.json`; certificates and Python
functions are verification aids, not operations available to the machine.

The exact cost for each enabled five-counter edge, with encoded N before it,
is1 for identity; `(p+7)N+3` for increment; `4N+(p+3)(N/p)+3` for decrement;
and `4N+4 floor(N/p)+3` for either test. Each cost is finite and positive.
False singleton tests or nondivisible decrements may get stuck internally;
they cannot occur in the promised simulation and cannot reach a false source
boundary. No claim of termination of those invalid cases is needed.

`verify_affine.py` traverses literal saved rows with independent arbitrary
natural variables. Every test along each path is identically zero or
provably positive, and every result is an exact affine identity. Its54,084
paths cover every row of the reversible-five and two-counter tables.
The ranks above turn those bodies into arbitrary-length terminating macros.
This is not finite-grid extrapolation.

Composition induction now gives the theorem in Section1: each enabled
normalized source edge returns after finite time to exactly the intended
five-counter boundary; each five-counter edge returns after finite time to
exactly its prime-encoded boundary. Internal controls of a macro are disjoint
from boundary controls of that layer. HALT is a boundary control and has no
outgoing edge. Therefore a valid simulation cannot halt early internally,
reach a false HALT, or perform infinitely many internal steps for one source
edge. A finite halting source computation is equivalent to a finite halting
literal run; an infinite source computation is equivalent to an infinite
literal run. Initializing history/work to0 supplies the base invariant.

## 6. Partial injection on every natural pair

Global injection is separate from promised-input correctness. The independent
checker groups edges by source and by target. Every multiple-edge group in
each reversible table consists only of complementary Z/P tests on the SAME
counter. Each primitive is individually injective; those pairs have disjoint
domains or ranges at every natural vector. Thus the whole relation is a
partial injection on all natural vectors, including malformed encodings.

The strict serialized guard is true for `+` and identity, equality to0 for Z,
and positivity for P or decrement. A decrement’s image is all naturals;
an increment’s image is the positive naturals; zero-update images equal their
guards. `validate_source.py` independently derives the exact image guards by
substituting the pre-counter and checking nonnegativity. With J=0, every
predicate is constant on0 or>0 in each counter. Its indexed check of the four
product classes is therefore an exhaustive all-natural proof, not a test of
only four chosen configurations. It also checks exact keys/types, reference
integrity, guard syntax, nonnegative post-counters, distinct branch names,
no incoming START, and no outgoing HALT. Its checks remain active under−O.

The generated JSON’s classes are sufficient for the strict audited compiler
schema. No unchecked image predicates, arbitrary functions, callbacks,
macros, hidden registers, or infinite lists occur in it.

## 7. Exact clocks, practical limits, and binary compiler compatibility

An exact overall forward clock is obtained by composing the layer costs:
1. TM macro costs and scratch prologue from Section3
2. separate-test splitting and merge-chain costs from Section4
3. history costs using the actual h at every recording edge
4. prime costs using the actual encoded N at every five-counter edge

For the binary-five compiler, sum its exact source-branch costs over the
literal run:1 for a zero update and
`3+2(Z+c)+delta−4S` for a moving branch using pre-update selected counter c.
The compiler proof supplies this formula. No uniform slowdown is claimed.

Even empty-tape initialization is enormous with this unoptimized ordering:
the142-step five-counter prologue reaches H=15 and has a theorem-derived
physical clock79,936,151,060,302. `prologue-predicted-clocks.json` labels these
as predicted exact clocks, not traversed traces. A literal trial was stopped
at a5,000,000-step budget; no full prologue or universal computation is claimed
to have been executed. Supplementary tests execute only small macro examples
and the fresh-entry path. These limitations do not affect the induction proof.

The strict compiler parameters are m=122622,p=66066,a=75495,J=0. Its finite
indexed gate construction therefore has269,291,358,255 factors and the explicit
(not optimized) radius upper bound3,292,955,588,459,274,804. The full ledger is
`target-ledger.json`. Alphabet size remains2 and valid configurations have
exactly5 particles. `loader.py:five_particle_input` implements the audited
coordinate formula without allocating gates. For the empty tape it yields
`{-20380381,0,1019018,1019019,20380380}`.

The old eager `compile_source` was NOT run on this source. Its quadratic
validation and hundreds of billions of object allocations are impractical.
Compatibility here means exact strict schema/semantic compatibility, verified
independently, plus the symbolic indexed finite gate definition in the pinned
compiler proof. A lazy executable compiler would be new work requiring its
own audit. No astronomical truth table or full factor array is claimed to be
materialized, and this source package does not alter an existing delivered
or frozen binary compiler/report.

## 8. Periodicity, positive return, and the sharp mass threshold

For inputs from the clean tape loader, the literal source has an enabled
continuation at every non-HALT simulated boundary, and each intermediate
macro terminates by the ranks already proved. Thus a nonhalting U computation
produces an infinite admissible binary-CA micro-path, not a premature stuck
path. This explicitly supplies the extra premise needed by Section10 of the
unchanged binary compiler proof.

Let Theta be the total number of CA microedges along the finite forward
literal run if it reaches HALT, computed using the BASE-source constants in
`target-ledger.json`. Theta is not the number of TM steps, five-counter
steps, or literal two-counter steps; and it does not use the enlarged
clean-target wrapper’s constants. The signed CA orbit on a halting input is

    x0+, x1+, ..., xTheta+, xTheta−, ..., x1−, x0−, x0+, ...

and has least period exactly `2Theta+2`. A forward unsigned path cannot
repeat a node: partial injection would propagate the repetition backward to
give the initial node a predecessor, contradicting the no-incoming START
property. The compiler’s admissible-state encoding distinguishes unsigned
path states and signs. Hence the displayed cycle has no shorter period.
For an infinite forward path, all its plus states remain distinct and the
initial configuration never returns.

Consequently, on this computable clean-loader family, the five-particle
initial configuration is periodic (equivalently has a positive-time return)
if and only if U halts. This is an unconditional consequence of the present
nonblocking source proof plus the audited compiler, not a claim about every
arbitrary five-particle configuration’s simulation interpretation.
The decision problem for all finite five-particle inputs of this one fixed
CA is nevertheless recursively enumerable: simply simulate and test exact
finite-support equality with the initial configuration. The clean-loader
reduction from universal halting establishes many-one r.e.-hardness. Thus
that fixed-CA five-particle periodicity/positive-return problem is
r.e.-complete.

For the lower threshold, use Report12, *Four mass units and exact
reachability*, Theorem1.1 (the Four-mass decision theorem), as a separate
proved dependency. Its exact scope is fixed one-dimensional deterministic
finite-alphabet conservative CAs, unique zero-weight vacuum, positive
integer non-vacuum weights, and at most one weight-one symbol, on finite
initial configurations of mass at most4. It supplies nonnegative-time exact
finite-configuration reachability. Binary number-conserving CAs satisfy these
hypotheses; reversibility is not needed for that lower theorem.

The reduction is exact:

    exists t>0: F^t(x)=x
        iff exists n>=0: F^n(F(x))=x.

F(x) is effectively computable and has the same mass as x. Applying the
Report12 reachability procedure to initial F(x) and target x therefore
decides positive return at mass at most4. Combining this lower dependency
with the literal upper construction makes5 the sharp mass threshold for
undecidability of binary reversible periodicity/positive return in this
fixed-rule, one-dimensional, finite-zero-background model. This does not
claim an independent new proof of Report12 or speak about unrelated meanings
of “universality.”

The original Report12 TeX and PDF bytes were verified respectively against
SHA-256 `803bf0c4194bb9d0f1942e6ad3eb762c79d7a811bd785742ee63f0c46a775595`
and `0d1280e962e64e8e13486aaac0fae2498ac908f37feeeffba0d682df865f3f5e`.
The claim is sourced to those authored theorem/proof files, not inferred from
a literature abstract or an open-problem status. `periodicity-audit.md`
records a separate verification of this corollary.
