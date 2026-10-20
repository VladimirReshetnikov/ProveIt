# Source contracts and the scope of the search

These are ordinary mathematical source proofs. No Lean/Rocq theorem or new
binary runtime certificate is claimed. Registers range over **all natural
numbers**. The current K219 source is the reference, not the superseded K221
source. The five alternate equality trees themselves come from Source140's
submitted finite synthesis; the all-natural arguments below and the
whole-program measurements are this continuation's work.

## 1. An open-sided association rule

For a binary source pair `(L,R)`, normal return from L enters R; a break1
from L exits the pair normally; higher left breaks lose one level. Left
continues pass unchanged. From R, continue1 restarts the pair and higher
continues lose one level; right breaks pass unchanged. A halt always halts.

Let `br(T)` and `co(T)` bound the levels of escaping break and continue.
For primitives they are `(0,0)` for increment/halt, `(1,0)` for decrement,
`(k,0)` for break k, and `(0,k)` for continue k. For a pair:

```
br((L,R)) = max(br(L)-1, br(R), 0)
co((L,R)) = max(co(L), co(R)-1, 0).
```

Then

```
((A,B),C)  <->  (A,(B,C))
```

preserves the complete primitive control-flow graph if `br(A)=0` and
`co(C)=0`. **B may be open.** Normal flow remains A then B then C. B's
break loses one level and its continue loses one level in either syntax;
continue1 from B restarts A in both. A's continues and C's breaks pass
unchanged. The excluded cases are precisely the exits that would jump over
C or restart at B instead of A. Internal successors and primitive effects
are unchanged. This gives a one-step bisimulation at equal leaf ordinals,
with equal complete register vectors, in every surrounding context. It
includes divergence and halts, not only terminating evaluations.

The side conditions matter. With A=break1, B=inc0, C=inc1, the left shape
increments register1 while the right shape does not. For the other side,
put A=inc0, B=inc1, C=(dec0,continue2), with register0 initially zero.
The left shape increments then decrements register0 on every iteration and
loops forever; the right shape increments register0 once, then its inner
loop exhausts it and returns. Thus unrestricted association is unsound.

The exact source audit tries both directions at every eligible distinct DAG
node, without relying on this rule to decide equality: it independently
resolves every leaf successor in the whole program. All210 exact rotations
coincide with this syntactic criterion among295 attempts. None immediately
reduces the206-node source. The finite beam walks test compositions; they
are not exhaustive and do not establish a lower bound.

## 2. Affine block commutation

`model.affine` recognizes increments, serial compositions of recognized
blocks, and a simple decrement loop. A recognized loop has a single tested
register r: zero exits normally; positive decrements r, runs an acyclic
sequence of increments and unconditional jumps, and returns to the test.
The body never increments r, reads another register, halts, or escapes.

If c_j is the body's number of increments of register j, induction on the
initial natural r shows termination and the exact transformer

```
r := 0;  j := old(j) + c_j * old(r)  (j != r).
```

This is a total affine function on the entire register vector. Serial
composition uses ordinary affine-matrix multiplication. Two recognized
blocks whose matrices commute may be swapped in a pair: both always
terminate normally, preserve the same complete vector, and have positive
finite duration. Consequently they are interchangeable in an arbitrary
context even if their durations differ. No finite numerical sample is used
to justify this rule. The initial program has35 recognized blocks with35
distinct transformers; four available commuting swaps preserve206 nodes,
and none immediately reduces it.

## 3. Five left-decrement equality alternatives

Write a=register5 and b=register6. Every displayed primitive decrement is a
left child. Define

```
P  = (dec6, continue2)
A5 = (dec5, (P, inc5))
A6 = (dec5, (P, inc6))
Z  = (dec5, continue1)
T  = (dec6, (inc5, continue2))
X  = (dec5, (Z, break1))
U  = (P, break1).
```

All unmentioned registers are preserved throughout.

A5 and A6 implement cancellation. While both counters are positive, one
pair is removed and the continue restarts the enclosing A block. This
strictly decreases min(a,b). When a=0, the first decrement exits normally.
When a>0 and b=0, dec5 has already consumed one and the last increment
restores it in A5 or stores a one in b in A6. Hence both terminate normally:

| Condition | A5 output | A6 output |
| --- | --- | --- |
| a <= b | (0,b-a) | (0,b-a) |
| a > b | (a-b,0) | (a-b-1,1) |

Z clears register5 and returns normally by induction on its input. T moves
all of register6 into register5 and returns normally, again by induction on
register6. X returns normally iff its input register5 is zero; otherwise it
clears register5 and returns break1. It leaves register6 unchanged.

The submitted trees are exactly:

```
hit0  = (A5, (T, X))
hit1  = (A6, (dec6, (T, (Z, break1))))
hit2  = (A6, (dec6, (Z, U)))
hit3  = (A6, (T, X))
hit12 = ((A5, T), X).
```

For hit0/12, A5 followed by T leaves `(abs(a-b),0)`, so X gives the required
result. Hit3 leaves register5 zero exactly on equality after A6 followed by
T; otherwise it is positive. X again clears it and distinguishes equality.

For hit1/2, the register6 produced by A6 is zero **exactly** when a=b, in
which case register5 is also zero. The following zero decrement exits its
pair normally, preserving both zeros. On inequality that decrement is
positive. Hit1 then transfers the remaining register6 into register5,
clears register5 and returns break1. In hit2, `(Z,U)` first clears5; whenever
6 is positive U decrements it and returns continue1, repeating `(Z,U)`.
Once6 is zero U returns break1. This strictly decreases6 and clears both
registers, returning break1 after finitely many steps.

Thus all five trees terminate for every natural input, clear5/6, preserve
every other register, and return normally iff a=b, otherwise break1. Their
four global replacements of accepted hit10 are therefore valid under any
register inputs, without a reachable-state hypothesis. Each source has207
DAG nodes and maximum zero-run6. Hit2 retains4744 leaves; the others have4748.
These proofs do **not** certify the candidate Turing tables or show that
state302 disappears: its break-return role must be checked separately.

## 4. Reachability-restricted specializations

A fresh Cartesian abstraction with exact buckets0..7 and bucket8 meaning
all naturals>=8 is forward-closed from the current seed. Increment saturates
at8; decrement maps8 to{7,8}. Induction on concrete primitive steps proves
that every reachable configuration belongs to its corresponding abstract
state. No upper bound on actual register values is assumed.

It recovers precisely the known no-op opportunities, at their K219 ordinals:
4606 is dec6 with6=0,4607 is unreachable;4718 is dec1 with1=0 and4719/4720
are unreachable. Pruning these intervals and resolving every retained
successor gives exact quotient CFGs. The removed reachable blocks last one
step and preserve the complete vector, so they cannot introduce a hidden
halt or infinite removed-only run. Their DAG costs are208,207, and209 when
combined: fewer primitive leaves need not mean a smaller shared encoding.

At entry4598, register6 is zero. The interval4598..4609 increments6 then
runs equality followed by halt, so it halts exactly when register5 was1 and
otherwise returns with5=6=0. The inherited six-leaf direct test has precisely
that contract, by induction over its final clear loop. Replacing the interval
in current K219 preserves every outside effect and successor; its cost is
208 DAG nodes/4738 leaves. This is a new exact composition measurement of an
old Source137 idea, not a new specialization theorem or binary candidate.

Finally, scratch outputs cannot simply be ignored. A backward liveness
analysis, treating total clear loops as kills, still needs both5 and6 on
every nonhalting exit of the four equality contexts. Only the direct halt
exit has no live registers. This analysis is conservative; it rejects the
simple dead-output shortcut but is not a proof that richer relational
contracts cannot help.
