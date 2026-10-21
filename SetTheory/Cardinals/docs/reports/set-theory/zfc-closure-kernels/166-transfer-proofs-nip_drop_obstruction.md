# Why NIP;DROP is not a replacement for transfer-pop

Date: 2026-10-21. Command-level obstruction for the unchanged numerical AX/MP calculus. This is not a statement about an unverified physical bootstrap.

Let ND be old NIP followed by old DROP. From (t,[x;w],d,h), it halts if incoming h=1, and otherwise returns

    (x,[t;w],d,x).

Thus it swaps top with the immediate stack head. It does not remove that head's stack level or expose a deeper entry.

## The cache invariant kills nontrivial MP

At command boundaries, h is either 0 or equal to t. This holds at the zero seed. AX and MP set h=0; ND makes top/cache equal to the same x. Therefore it is inductive.

A successful MP with proposed conclusion y requires I(t,y)=h. If h=0, I(t,y)=0 forces t=y=0. If h=t, then

    4P(t,y)=t.

Cantor domination P(t,y)>=t implies t=0, since otherwise 4P(t,y)>=4t>t. Then P(0,y)=0 forces y=0 as well. Hence every successful MP in this invariant produces only truth 0. Failed MP also produces 0.

## The reachable front cannot contain falsity

Track that top, cache, and the immediate stack head are all different from 1. This holds at the zero seed.

- ND preserves this property by swapping top and the immediate head, and sets cache to the new top.
- MP makes top/cache 0. A failure preserves the immediate head; its only possible success pushes 0.
- AX makes top either 0 or the original implication-coded bundle, cache 0, and the new immediate head R1, which is also implication-coded and not 1.

No command reveals a previously buried second head: ND replaces the first head, MP preserves it or pushes 0, and AX pushes a new block. Consequently this weaker front invariant is sufficient even if deeper initial entries were arbitrary, provided the initial top/cache/head avoid 1 and the cache invariant already holds.

The only halt is old NIP's test of cache 1. The invariant excludes it. Thus the unchanged source with ND in place of transfer-pop is provably nonhalting from the clean zero seed. It cannot supply the intended nontrivial consistency-sensitive compiler. A numerical subtree/state saving alone does not repair this loss of inference power.

## Bootstrap caveat

The proof does not establish nonhalting of any particular 213-state binary table on blank input. Its literal bootstrap must first be identified with an appropriate source frame.

A dirty initial cache equal to 1 may halt immediately at ND. A dirty accessible first head or top equal to 1 can move into cache. If h is initially neither 0 nor t, an MP before the invariant is established can also perform a nontrivial inference. A partial AX bootstrap must be matched and completed separately before applying the invariant.

Accordingly the unconditional nonhalting conclusion is exact for the specified clean source seed (and the generalized safe-front seeds above), not for an unverified machine or arbitrary intermediate register store.
