# A cancellation-and-reset equality routine with only left-child decrements

This is a source-language theorem, **not a 218-state construction**. Its
physical entry and helper costs are assessed separately.

Write `Di = CD i`, `Ii = CI i`, `Cj = CC j`, and `B = CB 1`. A binary node
`(X,Y)` executes X and then Y. A Break1 from X is consumed and skips Y;
a Continue1 from Y repeats the node. Other outward control depths are
adjusted by the same inherited source-language semantics.

The new routine is

```
P = (D6,C2)
U = (P,B)
V = (D5,(P,I6))
J = (V,U)
E = (V,(D6,J)).
```

Every decrement is a left child. V is used twice. The expanded tree has
12 primitive occurrences and 12 distinct nodes (including its primitive
leaves). Its standalone maximum depth is 6 and maximum zero run is 2.
This counts source nodes, not physical Turing-machine states.

## Theorem

For every pair of natural counter values `(r5,r6)=(a,b)`, E terminates,
clears both counters, preserves every other register, and returns normally
if and only if a=b. When a differs from b, it returns Break1.

## Proof

First, P returns normally at b=0, leaving b unchanged. At b>0 it decrements
b and returns Continue1. Consequently U returns Break1 at b=0 and,
otherwise, decrements b and returns Continue1. Neither changes r5.

For V there are three cases. If a=0, its left decrement returns Break1,
which V consumes, so V terminates normally at `(0,b)`. If a>0 and b=0,
the left decrement produces `(a-1,0)`, P returns normally, and I6 produces
`(a-1,1)`, after which V returns normally. If both are positive, D5 and P
reduce both by one, P's Continue1 passes through the left branch of
`(P,I6)` and is consumed by the right branch of V, so V repeats. Induction
on `min(a,b)` therefore proves the exact normal-exit function

```
V(a,b) = (0,b-a)       if a<=b;
         (a-b-1,1)    if a>b.
```

In particular, V always terminates normally, and its output has second
counter zero exactly when its input counters were equal. In that case
both output counters are zero.

Next consider J=(V,U) on arbitrary naturals. If V leaves second counter
zero, U returns Break1 and J returns Break1 at `(0,0)`. Otherwise U
decrements that counter and returns Continue1, causing J to repeat.
When the input to V has a<=b and b>a, one repetition leaves
`(0,b-a-1)`. When the input to V has a>b, one repetition leaves
`(a-b-1,0)`. In either case the sum of the counters strictly decreases.
This is a natural-number termination measure for all repetitions of J.
On termination U has second counter zero, and the displayed V contract
then forces its first counter to be zero as well. Thus J always returns
Break1, clears both counters, and preserves all other registers.

Finally E first executes V. For a=b, V produces `(0,0)`; D6 returns
Break1, consumed by `(D6,J)`, so E returns normally at `(0,0)`. For a!=b,
V produces a positive second counter. D6 decrements it and J executes,
clears both counters, and returns Break1. That Break1 propagates through
the right branches of `(D6,J)` and E. These cases prove the theorem.

All individual register operations preserve registers other than 5 and 6,
so the preservation claim follows compositionally. Both induction
arguments and the source-semantics deductions are formalizable in PA and
therefore in ZFC. No assertion about Con(ZFC) is needed for this local
equivalence.

## Discovery and verification boundaries

The tree is hit 9 of `eq_dag6_hits.trees.json` and hit 0 of
`eq_dag6_left_hits.trees.json`. The search uses finite semantic signatures
and representative-based deduplication, so its negative results are not
lower bounds. `audit_eq_dag_hits.py` checks the recovered literal tree
using an independently compiled control-flow graph on 1,750 pairs,
including unrelated nonzero registers and pairs through 10,000. Those
finite diagnostics check the transcription; the argument above supplies
the unbounded mathematical contract.
