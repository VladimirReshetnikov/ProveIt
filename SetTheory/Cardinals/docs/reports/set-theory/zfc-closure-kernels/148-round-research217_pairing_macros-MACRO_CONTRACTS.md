# Three concrete 2-adic pairing macros

These are source-level arithmetic contracts, not a217-state construction.
The full literal ASTs and occurrence maps are in MACRO_INVENTORY.json.
The one complete source replacement has217 distinct source nodes and5352
primitive leaves, versus205 and4744 in the audited baseline. Its raw machine
allocator did not complete, so no physical state count is asserted.

Write Di for decrement registeri, Ii for increment registeri, and Ck for
continuek. A zero decrement emits one break; a pair consumes a one-break
from its left child, skipping its right. A pair consumes a one-continue
from its right child by repeating the pair. These are the usual literal
structured-control semantics.

Let T(i,j)=(Di,(Ij,C2)), and D(i,j)=(Di,(Ij,(Ij,C3))).
For arbitrary natural inputx inRi, T clearsRi and addsx toRj; D clearsRi
and adds2x toRj. Other registers are unchanged. The strictly decreasing
source counter proves termination.

## Pair, thirteen leaves

Let A=(I7,(D1,C2)). It incrementsR7 once before testingR1, then repeats
while that decrement succeeds. Thus A clearsR1 and adds its old value+1
toR7, preserving every other register.

The new pair macro is

    (D(1,7), (D6, (D(7,1), (A,C3))))

Input condition: R1=b, R6=a, R7=0. Initially D(1,7) givesR1=0,R7=2b.
Each positive outerD6 iteration clearsR7 intoR1 with a factor of two, then
A clearsR1 and producesR7=2(oldR7)+1. The finalC3 returns to the outerD6,
not to the doubling subloop. The decreasingR6 proves termination.
Aftera iterations, R7=2^a(2b+1)−1, R1=R6=0. Every other register is
unchanged, and the macro returns normally.

## Unpair, nine leaves per input register

For r=2 or8, use

    (Dr, ((Dr,(I7,C3)), (I6,(T(7,r),C4))))

Input condition: Rr=n, R6=R7=0. While two units are available inRr,
the first two decrements consume them and I7 adds one quotient unit;
C3 returns to the first decrement. An even input2q therefore eventually
fails the first decrement and returns normally withRr=0,R7=q. An odd
input2q+1 consumes its last unit at the first decrement and fails the
second. That failure exits just its local pair, allowing I6 to increment
the exponent. T(7,r) restoresq toRr and clearsR7; C4 repeats the whole
macro. Thus the outer phase updatesn to floor(n/2) exactly whenn is odd,
and incrementsR6 once. The odd phase decreasesn strictly, including
n=1 to0, so the macro terminates.

The arithmetic recurrence S(a+1,b)=2S(a,b)+1 and S(0,b)=2b shows that
the final(R6,R7) is the unique inverse of S(a,b)=2^a(2b+1)−1. The input
register is zero, all other registers are preserved, and the macro returns
normally. Raw input0 gives(0,0), with no exceptional branch or increment.

## Reachability and proof boundaries

The literal old pairing macro occurs174 times; the R8 and R2 inverse
macros occur4 and82 times. The existing checked inductive invariant,
combined with the guard on every incoming edge from outside a macro,
provesR7=0 at every old pair entry andR6=R7=0 at every old inverse entry.
The internal loop-head invariant alone cannot show this, because it joins
iterations carrying intermediate values. The receipt explicitly records
the external entry edges and their guard-refined scratch masks.

These old-source entry facts do not automatically prove the new-source
entry facts after the codec changes. The separate owned ZERO_FLOW_PROOF.json
now closes that particular gap. Replacing each exact macro by an opaque,
normally returning call collapses the old and new sources to the identical
2576-vertex control tree with260 calls. A two-class zero/positive invariant
includes the seed, is inductive across all3215 enabled edges, and proves
every call precondition. The macro summaries fix only their cleared
registers and treat both codec outputs as arbitrary naturals. Consequently
this proof applies to the new codec, without transporting any Cantor-specific
value facts or assuming consistency. Simultaneous induction on finite
source prefixes uses the entry invariant and the proved terminating macro
contracts to justify every summarized call.

Source scratch contracts do not supply parser, stack, scheduler fairness,
formula-calculus calibration, runtime decoder or blank-initializer proofs.
The separate codec isomorphism supplies only the numerical theorem-system
layer and explicitly does not conjugate raw lists or cache addition.

An owned direct structured-semantics diagnostic passed153 pair inputs
(a=0..8,b=0..16) and2049 inputs per inverse (n=0..2048), preserving nonzero
unrelated registers. Those finite runs are checks on the AST/control depth,
not the proof of the all-natural arithmetic contracts above.

## One exact allocation pilot

The complete three-macro replacement has source SHA256
`1d70966a0b1a6bd9f36c30cbee78ac34a0c520db38a2463c6daaf3eb8213f76f`.
It introduces primitiveCC4. The owned allocator stops at the unsupported
leaf interface(('CC',3),1). Therefore THREE_MACRO_PRICE.json correctly says
ALLOCATOR_FAILURE_NOT_A_STATE_PRICE. No partial or guessed physical count
is reported, and no new helper allocation has been synthesized.
