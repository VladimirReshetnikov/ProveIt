PA194AX11HMP: A NEW 194-STATE MP SOURCE REASSOCIATION
=================================================

Result
------
The machine has 194 working states and 388 binary transition rows, a
bidirectional tape, blank symbol 0, and L/R moves. In the canonical table,
state 0 is initial and 194 is the halt control, excluded from the working
state count. Their native labels are 74 and 254.

The relative mathematical theorem is

    iPRA proves Halt(AX11H,blank) <-> Halt(PA194AX11HMP,blank).

Composing it with the exact revised AX11H packet's written iPRA calibration
gives nonhalting iff Con(PA). This is an ordinary mathematical proof with
explicit primitive-recursive clocks. It is not a claim of a newly completed
Lean endpoint, and it inherits the explicitly identified parent calibration.
No result below 194 states or global lower bound is claimed.

Construction
------------
At the MP source block, with A=node75, B=node37, C=node6, D=node54, replace

    ((A,B),(C,D))  by  (A,(B,(C,D))).

All 3,671 opcode/register/guarded-successor instructions remain byte-identical.
The source addresses change at 87 sites, ordinals 3572 through 3658. Four
retained native rows change, preserving their writes and directions:

    100/0: 0 R174 -> 0 R213
    100/1: 1 R164 -> 1 R174
    174/0: 0 R213 -> 0 R28
    174/1: 1 R28  -> 1 R164

The seven existing AX reader folds remain simultaneously valid. Blank startup
reaches the same calibrated seed after 58,066 steps, against the parent's
57,922. The recurring MP dispatcher and its source encodings change; the
construction is not just a state renaming.

Literal identities
------------------
Candidate canonical SHA-256:
b634f75f4969a68513c5460a2e6bf8fd9bb0a72ab1f3dd03ec88b348ce2c6272

Candidate native SHA-256:
e8e22523ae12c9b3ee1fe33a0b1697602584f58bfdf55b88b7a7f3c6e7ea9dfd

Exact parent's native SHA-256:
6022711dcc0a025eb4b7a5a8f690d6b52f45f3d963a0868afef10962ccc49bd3

Revised parent calibration archive SHA-256:
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075

The comparison snapshot is ProveIt commit
793c68737d94bffa4e32a75bce6cc8058d6d22f0. reference/manifest.json binds all
baseline sources and the five included calibration fragments to the exact
retained archive. The enclosing deliverable retains the complete calibration
archive separately, avoiding a duplicate copy in this component.

Evidence and proof
------------------
The direct final-table check covers all 4,778 arbitrary-natural primitive
outcomes and rederives four arbitrary finite-list traversal lemmas. Its
certificate has 1,101,511 symbolic operations and minimum positive duration
constant 3. It uses the byte-identical symbolic runtime covered by the
identified parent's mathematical audit; no arithmetic-box oracle is imported.

An independent literal replay checks every transition of the 58,066-step blank
prefix and the entire final finite-support tape, head, source address, register
file, 26 unit spares, and zero exterior. A separate source-closure checker
checks all 4,777 nonhalting outcomes for each machine, with zero address
overflow in every case. Finite coefficient comparison yields exact positive
primitive-recursive source clocks and the common bounded-halting transfer

    Theta(t) = 58066 + 9*t*t + 685*t.

The proof in relative_proof.tex includes cofinality and an absorbing terminal
code. It uses no unbounded least-boundary search. The successful executable
checks certify the finite instances; the uniform rule-soundness argument is
an identified mathematical dependency, not a theorem inferred solely from a
Python success message. The parent's full arithmetic calibration is inherited.

Reproduction
------------
Python 3's standard library is sufficient. Run

    python reproduce.py --output /absolute/path/to/a/new/rebuild-directory

The wrapper copies this packet, checks frozen input identities, reconstructs
the exact table and source, checks the four row edits and seven local folds,
replays complete startup, freshly checks all 4,778 physical outcomes, and
checks the clock bound. The output directory must not already exist. The
optional --quick flag reuses the supplied direct-runtime certificate while
rerunning the other finite checks. A full physical replay takes a few minutes
in the recorded environment.

proof.tex is the standalone TeX entry point. The enclosing main report contains
the full canonical transition table and the comparison against the supplied
design corpus. Novelty receipts are retained with the verification artifacts.

Credit and scope
----------------
The PA calculus, AX11H emitter, binary engine and seven reader folds are the
supplied predecessors. support.py comes from the original AX11H construction;
the unchanged symbolic runtime, minimal helpers and legacy mapping are copied
from its verification/reference directory. Their notices and byte identities
are preserved. This component contributes the MP source association, four-row
allocation, source and physical verification, and relative time-transfer proof.
No priority claim is made.
