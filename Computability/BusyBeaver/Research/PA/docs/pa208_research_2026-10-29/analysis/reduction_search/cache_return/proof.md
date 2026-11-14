# Cache-return MP source alternative

This is an already documented alternative in the retained final U213
three-command compiler, not a new historical discovery. The success body
[3847,3873) is replaced by `(CD4,(CI5,CC2))`, which transfers D=z into the
known-zero cache H and clears D. T remains zero and the stack is unchanged.
An induction on z proves its all-natural result `(0,w,0,z)` and termination.
Failure is unchanged.

The retained source compiler reserves a disposable zero and uses

`DISCARD; PUSH; B_M; PUSH; B_A; PUSH; S; S; MP(Y); S`,

where M=I(A,Y). Immediately before MP the tuple is `(A,[0;w],0,M)`;
MP returns `(0,[0;w],0,Y)`. The final S halts if Y=1 and otherwise returns
`(Y,w,0,0)`. The helpers use only forced-failing MP calls, and all other rule
blocks remain unchanged. Soundness, startup credit, and cofinal scheduling
are as in the retained U213 compiler proof.

The exact source generator verifies both CFG resolvers, the unchanged
retained control edges, and the protected startup address. The new source
has 3,886 primitives and 197 DAG nodes. A newly allocated literal table still
requires its own full tape-frame proof; no sub-208 result is claimed.
