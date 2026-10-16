# Ordinary correctness proof for the four-row 253-state variant

Let U be the pinned 253-state machine and V the literal table
`grammar_search/candidate/faster253.tm`. Let p be the accepted register
program, and let p' be its single closed-region reassociation. Under the
same two-way infinite tape with finite support, two-symbol, blank-start
convention as U, the construction
has the following ordinary mathematical consequence:

**Theorem.** ZFC proves `V halts <-> U halts`, and hence proves
`V does not halt <-> U does not halt`. This theorem requires no consistency
assumption. Composing it with a chosen, established internal calibration of
U gives exactly the same `Con(ZFC)` equivalence for V.

The final composition must use the baseline's exact arithmetized proof
predicate and object-theory syntax. The finite external Coq endpoint by
itself is not being silently substituted for an internal proof compiler.
That issue is inherited from the baseline and is distinct from the
arithmetical machine-to-machine theorem proved here.

## 1. Literal change and complete initial configurations

The files have exactly 506 transitions, working labels 0,...,252, blank
symbol 0, start state 0, and terminal label 253. The four changed rows are
listed in README.md; all others are byte-level equal after parsing. The
state map used in the symbolic proof is a bijection, with old dispatcher 96
mapped to compact state 33. Fresh old labels 255,256,257 replace old labels
12,128,110; they are not extra physical states.

Direct recursion on the literal transition function gives

`run(V,312935,blank) = run(U,312975,blank) = c*`.

The checker compares the entire sparse tape, including all spare data,
along with the head and compact state. Thus no prepared tape or omitted
initializer enters the state count. Both finite prefixes consist of
nonhalting configurations, as the literal interpreter would reject an
undefined/terminal transition before the required endpoint.

## 2. The four register-file contracts

For a finite list `vs` of at least nine naturals, encode it as the finite
word obtained by concatenating `0 1^(v+1)` for each entry, with blanks
beyond. A marked file erases the first one of a selected register block.
The four contracts are:

1. A skip-entry state marks its selected register and returns at state 2
   for the first register, or state 6 otherwise.
2. State 73 at a marked file increments that register and returns at state
   48, shifting the remaining file as prescribed.
3. State 43 at a marked zero register restores the mark and returns at
   state 3, leaving the file unchanged.
4. State 43 at a marked positive register decrements it, appends one zero
   spare block, and returns at state 63 for register zero or state 48
   otherwise.

These are `box_mark`, `box_inc`, `box_dec0`, and `box_decp` in the included
pinned `upstream253/ZF/m253/coq/tm/Box.v`. The proofs are elementary finite
word inductions and scans. They hold for arbitrary remaining register and
spare data, not just the initial file. Every transition used by these
proofs is preserved. The checker enforces the conservative set of 55
protected state/read pairs; the exterior transition at old state 3/read 0
is deliberately excluded, because the zero-decrement contract returns
before executing it.

## 3. Soundness of the strict symbolic checker

A symbolic configuration consists of a control state, a flag saying
whether the head is on the first cell of the left or right list, and two
lists of segments. A segment is one concrete bit, a uniform run of
`a*n+c` bits for nonnegative integers a,c and the free parameter n>=0, or
the register file in one of the states `plain`, `marked r`,
`incremented r`, or `decremented r`. Only the last right segment can be a
register file. The left exterior is the infinite blank tape.

Every rule in `strict_affine.py` has a direct execution justification:

- A concrete bit uses exactly the table's literal transition. This is the
  only rule, together with the corresponding known-zero box-boundary
  transition, that sets the positive-progress witness.
- Recentring the head, exposing one exterior blank, deleting an empty
  run, and peeling one cell from a run with c>0 leave the denoted tape and
  head unchanged.
- A self-loop scan applies the same transition exactly `a*n+c` times.
  This can be zero, so the rule does not assert positive progress.
- Register-file rules use precisely the four contracts above. Marking is
  allowed only for an unchanged plain file. Incrementing requires a
  valid marked index. Decrementing additionally requires a named branch
  guard on that same register and cannot occur under a guard for another
  register or under no guard.
- Normalization combines adjacent uniform runs by adding their
  coefficients and constants, deletes zero-length runs, and removes
  exterior zero padding. Each operation preserves the denotation for
  every n and every valid register list.

Induction on the finite symbolic execution therefore proves that each
accepted case is a concrete finite execution for **all** n>=0 and all
register files satisfying its stated zero/nonzero guard. No probabilistic
testing or finite bound on the numerical register contents occurs in this
argument. The explicit positive-progress witness excludes a spurious
zero-time simulation step. The smallest witness among the 8,391 accepted
cases contains 13 literal transitions.

The port follows the proof-bearing rules in the included `SymExec.v`,
including its stricter oracle and progress conditions. It is not necessary
to assume the earlier Python design prototype is a verified compiler.

## 4. From all sites to register-machine halting

The decoder has 6,460 leaves, maximum depth 34, and a closed root: no
break/continue escapes its enclosing program. The checker enumerates the
entire finite tree and tests each increment, control, and halt leaf, and
both outcomes of every decrement leaf, giving 8,391 cases. The return
program counter is checked using the same bit-string increment, break,
and continue operations as the register semantics. Cases include the
instruction-pointer overflow that moves the left marker and increases the
gap by one. Writing the gap as `40+n`, the overflow output has gap
`40+(n+1)`; the next instruction case is instantiated with the newly bound
parameter `n+1`. Every next case is likewise instantiated with the entire
updated register list `vs`, including the appended spare zero block after
a positive decrement. The universal quantification over `n>=0` and all
valid register lists therefore supports arbitrary finite concatenations
of the verified cases.

The dispatch invariant is a leading marker, the current program counter
padded with zeroes to a gap at least 40, a header, and an encoded register
file with arbitrary spare blocks. The encoded physical register order is
`[2,4,3,7,6,8,0,1,5]` in source-register indices. There is enough gap for
every decoded leaf. The usual no-stray-bits invariant is proved by
induction from the empty counter for any closed register program; the
reassociated program has the same required closure condition.

Each accepted site gives a positive finite machine path to the next
dispatch invariant, or reaches the terminal state for a halt instruction.
Consequently register halting implies machine halting by concatenation.
Conversely, if a dispatch configuration has a halting computation and the
current register instruction is nonhalting, the positive simulated path
reduces its remaining halting time. Strong induction on that time forces
a register halt. This proves both halting directions without a fairness
assumption or an assertion that an observed nonhalting prefix runs forever.

The exact endpoint c* is the invariant for the 330th configuration of p'
from the standard initial vector `[2,0,...,0]`. This finite register prefix
is computed and checked. Finite-prefix transport therefore relates V's
blank-start halting to p' from its standard initial configuration.

## 5. The 2,981-pair register certificate

The baseline DAG is checked to unfold to the pinned literal `Prog254.v`.
The candidate DAG is the specified reassociation. For each related pair
of decrement-test locations, the certificate requires the same tested
register, follows both zero and positive exits, and compares the exact
multisets of increments before the next related test. Halt locations must
match. The initial segments from both roots are checked as well. The
maximum segment contains five instructions.

Increment-only segments preserve equality of the entire register vector
when their increment multisets agree. Matching decrement tests then take
the same branch for every register vector. Induction along any finite
halting register computation, followed by the mirrored certificate,
proves `p halts <-> p' halts`. The checker verifies all 2,981 entries in
both directions and rejects a deliberately corrupted initial path.

The independently written `independent_rm_check.py` repeats both directions
using tuple-valued bit prefixes and a recursive carry operation. It does
not import the generator's string/integer interpreter. Its canonical
removal of trailing zeroes is sound because the decoder supplies zeroes
beyond the recorded counter and every successor is computed from the full
decoded leaf path. This provides a second execution semantics check on
the same finite relation.

Combining the finite prefix, universal site simulation, and this finite
bisimulation gives `V halts <-> U halts`. All objects and proofs in this
machine-to-machine argument are arithmetical: finite words, lists, literal
table lookup, primitive-recursive runs, and ordinary induction. They can
therefore be formalized in ZFC without a new set-theoretic hypothesis.
The delivered evidence establishes the ordinary proof with computational
certificates; it does not include a newly serialized and kernel-checked
Coq derivation of the final theorem.
