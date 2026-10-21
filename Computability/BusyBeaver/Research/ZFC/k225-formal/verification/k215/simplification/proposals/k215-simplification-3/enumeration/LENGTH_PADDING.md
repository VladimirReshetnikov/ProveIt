# A generic length bound replaces candidate-specific cofinal padding

Date: 2026-10-21. Status: ordinary mathematical proof and source-grounded
assessment. No sealed machine/proof packet or upstream source is modified.
The accompanying Lean adapter is explicitly uncompiled.

## Result and limits

For a positive-continuation command codec, the natural number encoding a
nonempty word is at least its command length minus one. Consequently a finite
word halting from **every natural command-boundary work-store** can be placed
beyond any enumerator cutoff simply by prefixing enough commands. No neutral
padding instruction, unchanged work-store, growing AX parameter, or special
Cantor calculation is needed.

For the already constructed common-NIP compiler the fixed universal word has
length at least22, hence its one code is at least21. The literal next-candidate
cutoff is1. Thus that actual completeness proof needs neither length padding
nor a varying-parameter cofinal family: a single fixed successful candidate
suffices. This is a simplification of the ordinary proof presentation, not a
new machine, a smaller state count, or a newly checked kernel endpoint.

The upstream phase-four EnumPerm proof is a DIFFERENT four-command enumerator.
Its general arbitrary-cutoff theorem already uses a four-line specialized bound
and a nine-line completeness proof. Replacing that code with the generic
library result below is a reusable abstraction, but is not presently a measured
source-length, dependency, kernel-term-size, or compilation-time improvement.

## 1. The codec hypotheses

Let Cmd be a command type and let

    pack : Cmd x Nat -> Nat,
    decode : Nat -> Cmd x Nat

satisfy, for every c,r,z,

    decode(pack(c,r)) = (c,r),                  (round trip)
    snd(decode(z)) <= z.                        (residual bound)

Each encoded command includes its fixed opcode and all its fixed arguments.
Its arity may depend on the opcode. There is no assumption that all commands
consume the same number of fields.

For a nonempty word define its fresh-candidate code E by

    E([c]) = pack(c,0),
    E(c :: v) = pack(c,1+E(v))    when v is nonempty.

This is exactly EnumPerm.encL, with a separate head and tail argument. The
empty word has no fresh-candidate encoding in this theorem. In particular,
E([zero-opcode]) may be0; zero is not an empty candidate.

The actual scheduler uses a different convention for a positive residual:
residual0 means the candidate has finished; residual r>0 fetches code r-1.
The +1 in E is therefore mandatory at EVERY nonfinal command boundary.
The final residual is0, and its final command still executes before the next
fetch advances to a new candidate.

### Residual domination

For every command c and residual r,

    r <= pack(c,r).

Apply the residual bound to z=pack(c,r), then rewrite by round trip. This is
strictly more generic than reproving the inequality by nested Cantor pairing.
For Cantor codes it is also immediate from P(a,b)>=b at every right-nested
argument field. No monotonicity, left-coordinate inequality, or distinct-zero
encoding assumption is needed.

## 2. The length theorem

For every nonempty command word v,

    length(v)-1 <= E(v).

Equivalently, for the head/tail representation,

    length(cs) <= encL(c,cs).

Proof is induction on cs. For cs=[] the left side is0. For cs=c'::ds,
the induction hypothesis gives length(ds)<=encL(c',ds), and residual
domination gives

    1+encL(c',ds) <= pack(c,1+encL(c',ds)).

Combining these is precisely the successor case. This proof does not inspect
any opcode, any argument, or the internal pairing nesting.

### Zero check

For a zero-opcode command R with pack(R,r)=P(0,r):

    E([R])=0,  E([R,R])=2,  E([R,R,R])=9.

The stored positive suffix codes are1 and3 respectively. A plain zero-ended
fold without the +1 would collapse all these words to0 and invalidate both
the length theorem and execution lemma. That is not the codec used here.

## 3. Universal halting survives arbitrary finite prefixes

Let a command act on a work-store W by a TOTAL function

    step : Cmd x W -> Option W,

where none denotes halting and some(w') denotes normal termination. Extend
this by finite list execution, stopping on none. Suppose a nonempty finite
word U satisfies

    for every w, execute(U,w)=none.

Then for every finite prefix p and every w,

    execute(p ++ U,w)=none.

Indeed execution of p either halts, or returns a work-store w' to which the
universal property of U applies. The prefix need not be an identity, preserve
a theorem invariant, leave a stack sentinel, or even avoid an early halt.

The totality premise must not be weakened to 'each instruction is partially
computable': a prefix could diverge forever before reaching U. At the abstract
EnumPerm level, step=cstep is already a total function into Option. At the
physical machine level, the existing all-natural command/primitive runtime
contracts supply the corresponding finite normal-exit-or-halt guarantee.
This does not claim U halts from arbitrary binary tapes or source interiors.
The state is a canonical command-boundary store; scratch, tape-frame, and
control conventions remain separate implementation premises.

## 4. Generic cutoff completeness

Assume the scheduler, starting between candidates at cutoff N, reaches every
candidate code n>=N unless it halts earlier. Assume also the usual execution
lemma: a candidate encoding U faithfully executes U, or has already halted.
Choose any command q and let

    V_N = q repeated N times, followed by U.

Since U is nonempty,

    E(V_N) >= length(V_N)-1
           = N+length(U)-1 >= N.

Section3 makes V_N universally halting. Hence the enumerator eventually halts.
If one wants an unbounded family, {E(V_N):N in Nat} is unbounded by this same
inequality. Strict monotonicity or a distinct code for each N is unnecessary.

The hypotheses on the scheduler are essential. Mere unbounded growth of its
candidate counter, or strides restricted to1/2, does NOT imply it visits an
arbitrary unbounded set of successful codes. This theorem does not repair the
old scratch-biased skipping-scheduler gap or replace its adjacent-success
argument. It applies to the ordinary increment-by-one reach theorem.

The residual-bound hypothesis also proves finite candidate draining: if the
current positive residual is r, the next residual is at most r-1. Thus the
usual reach proof already has the needed finite continuation property.
Commands must act on work-store registers while this decoder retains control
of the candidate counter and residual; arbitrary interference with those
parser registers is not allowed by the abstract interface.

## 5. Fixed-code completeness for the delivered common-NIP interface

Use the established word notation

    D = A(0;0,0),
    STORE_0 = D;R^8;M(0).

STORE_0 has exactly10 commands. The saved compiler proof establishes that
STORE_0;STORE_0 halts or gives a clean sentinel state

    (top,stack,counter,cache)=(0,[0;v],0,0)

from every natural work-store. For a derivation of1, its compiled B_1 then
halts or returns (1,[0;v],0,k), k!=1. R;R detects the returned1 before
reading v. Therefore

    U = STORE_0;STORE_0;B_1;R;R

is universally halting, with length(U)=22+length(B_1), so E(U)>=21.
The independently matched startup has next candidate1 and residual0.
The ordinary reach theorem therefore eventually visits E(U), unless it
already halted. The work-store encountered there is irrelevant because U
is universal. Protected credit and theoremhood remain necessary for the
opposite, soundness direction; this argument does not replace them.

### Shortest reuse of already established facts

The existing common_nip_CREDIT_PROOF.md Section2 already proves that the
syntactically decoded candidate W(n) has length at most n+1. The exact codec
round trip identifies W(E(U)) with U (or its command-tag word, which has the
same length). Hence |U|<=E(U)+1, immediately giving E(U)>=21. No NEW encoding-
length induction is required for this application.

For the literal cutoff1 there is an even shorter positivity argument:
U starts with D=A(0;0,0), whose opcode is2. Its code is P(2,r) for a natural
residual r, so P(2,r)>=2>=1. Equivalently, code0 decodes as R, not as A, so
this AX-first code cannot be0. This uses only the first command and the
already established Cantor/decoder facts; the length theorem is unnecessary
for this PARTICULAR cutoff. The length proof is the opcode-independent
alternative and supplies arbitrary-cutoff padding for reuse.

This removes only the varying-Y shell and its special numerical lower-bound
calculation from a future presentation of that command-level completeness
proof. The sealed delivered proof remains unchanged and correct.

## 6. Source-grounded relevance to phase-four EnumPerm

Pinned source: commit e0b8f9cb8c496ff2d6e43f478021fc14d42bbfad,
EnumPerm.lean SHA256
ad5ad3357ae811827a1661b2b671c0cf61da4ade6fe7615b4655a2a4c38f93cd.
The full local snapshot and published targeted status are copied under inputs/.

Relevant existing declarations:

- pack, lines80-84: NIP/DROP have no argument, MP one, AX three fields with
  y read before x. These are not the common-NIP command tags.
- decode_pack, lines94-95, and decode_le, lines99-103: exactly the two codec
  hypotheses above. They already discharge every variable-arity complication.
- encL, lines106-108: exactly the positive continuation wrapper used here.
- cexec_append, lines236-246: the prefix preservation proof is one case split
  after this existing theorem.
- exec_list, lines260-276: candidate execution already respects encL and guards.
- drain and reach, lines300-335: ordinary later-candidate reach is already done.
- program_none, lines514-522: START_Y plus compiled refutation and final
  DROP;NIP;NIP halts from every work-store. Taking Y=0 gives the fixed U needed
  by the generic theorem; this is not a fresh compiler construction.
- encL_ge, lines524-527: its specialized Y bound is just four source lines.
- complete, lines530-538: nine source lines already handle every cutoff.
- halts_iff, lines542-543: the general seed theorem is already implemented.

A generic residual-domination/length/prefix lemma is a useful shared library
boundary if multiple command variants are to reuse enumeration completeness.
It removes calculus-specific AX arithmetic from that shared theorem. But for
this one current file, replacing four short lines with an induction, padding
construction, nonempty-list handling, and a prefix lemma is not an honest
local compression claim. The existing xrun/shared-command changes and general
halts_iff must not be advertised as new work.

No Lean executable is available in the inspected task environment, so the
companion adapter is labeled uncompiled and no kernel-performance claim is
made. check_length_padding.py supplies only finite codec corroboration and
source/hash checks; Sections1-5 are the all-natural mathematical proof.
