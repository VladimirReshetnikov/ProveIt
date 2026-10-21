# Exact source-binding defect and unconditional termination

The scratch-biased source has SHA-256
`2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a`.
Its published intended state-dependent scheduler does not match its exact control-flow graph.
The complete owned source audit is `audit_biased_source.py`, with result
`BIASED_SOURCE_AUDIT.json`. It imports only existing owned source readers.

## Exact defect

The context-root predecessor has a CC3 return at path10011. Replacing that leaf
by `(CI6,CC3)` adds a right ancestor to the CC3 occurrence, so its target changes.
In the resulting source:

- ordinal4696, CI6 at100110, goes to4697;
- ordinal4697, CC3 at100111, goes to23, not0;
- ordinal23 is CD3, with zero branch4698 and positive branch24.

Deleting the new CI6 and contracting its edge yields the ordinary short-transfer
source CFG at every row EXCEPT that return: expected0, actual23. Thus this is
not merely a possible interpretation ambiguity. Exact finite CFG equality fails
at one known edge. The owned reader uses continuation stacks independently of
the supplied reconstruction program. The README's stated root-return semantics
is false for the literal source.

## Universal post-AX halting theorem

At the end of the unchanged AX body, registers A,H,X,Y are zero. Top T may be
an arbitrary gate value; N,W,D need not be restricted for the following argument.
Starting at ordinal4696 with `(A,H,X,Y)=(0,0,0,0)`:

1. CI6 sets X=1. CC3 goes to23; A=0 selects the clear-top block at4698.
2. The two-instruction loop CD1;CC1 reduces arbitrary T to0 and terminates.
3. The load-H-to-T block starts with H=T=0 and X=1. Its drain-H loop is empty;
   its restore-X loop executes once, setting H=1 and X=0.
4. The unchanged NIP block tests H=1 and takes its CH leaf at ordinal4718.

For arbitrary initial T, the exact source-step count from4696 to CH is15+2T
(counting executed non-CH primitive instructions). N,W,D are untouched. A simple
owned literal trace for T=0 verifies the fifteen fixed instructions; arbitrary T
is handled by induction on the clear-top loop. No formula decoding, theoremhood,
or consistency assumption is needed.

Consequently, given the separately verified partial-AX blank startup, terminating
AX macro contract and complete primitive-to-binary simulation, this particular
scratch-biased binary machine halts unconditionally. It is not an uncalibrated
promising ZFC-consistency candidate. The result does not impugn the runtime
certificate: that certificate correctly implements the wrong source graph.

## Parser facts that remain valid but are inapplicable to the claimed schedule

The standalone Schedule and Read blocks are byte-identical source subtrees to
the parent. With X=b and L=n, Read iterates the Cantor successor map starting
from `(b,0)`, so for b=0 or1 it decodes unpair(n+b), clears X,Y and puts the left
projection into initially-zero A. Each successor is `(x-1,y+1)` when x>0, and
`(y+1,0)` when x=0; both increase P(x,y) by one. This proves the assertion for
all n by induction. Schedule on positive L decrements it; on L=0 it copies N
to L and restores N to N+b+1, clearing X. These correct isolated statements do
not justify pretending that ordinal4697 returns to Schedule.

No received code was executed. Source subtrees, literal operations, and all CFG
edges were independently compared. This note does not claim an exact number of
binary steps through the huge pending AX computation.
