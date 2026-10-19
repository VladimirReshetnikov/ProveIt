# A weaker, proved-safe reassociation criterion for Wade's register programs

This is an ordinary mathematical proof directly matching `RM.v`. It has not
been compiled in Rocq or Lean in this session. It strengthens the sufficient
criterion used in the initial decoder search; it is not a claim of priority
over the programming-language literature.

## The theorem

Let `A ; B` denote one Wade cons cell whose car is A and whose cdr is B.
Regard a component as its finite big-step relation on register states and
the exits Normal, Halt, Break(k), Continue(k), where k is positive. Suppose:

1. A has no finite execution exiting with any Break(k).
2. C has no finite execution exiting with any Continue(k).

There is **no restriction on B**. A may emit Continue(k), C may emit
Break(k), and any component may halt or diverge. Then, for every initial
register vector R, final vector R', and exit x,

\[
  \operatorname{run}(A;(B;C),R,x,R')
  \quad\Longleftrightarrow\quad
  \operatorname{run}((A;B);C,R,x,R').
\]

This equivalence includes every finite exit with its exact level and final
register vector, not merely halting. It is valid for nondeterministic
component relations as well as the deterministic register language.

## A general finite-loop normal form

For a component F and exit x, write F_x for the binary relation on register
vectors associated with that exit. Write juxtaposition for relational
composition in execution order: XY first performs X, then Y. Let union be
set union and T* the reflexive transitive closure, using only finite paths.
Abbreviate Normal by N, Halt by H, Break(k) by B_k, Continue(k) by C_k.

For arbitrary components F and G, define

\[
 T_{F,G}=F_NG_{C_1}.
\]

This is exactly one restart of their cons cell: F completes normally and G
continues at level one. For k >= 1, define the non-restarting alternatives

\[
\begin{aligned}
 D_N^{F,G} &= F_{B_1}\cup F_NG_N,\\
 D_{B_k}^{F,G} &= F_{B_{k+1}}\cup F_NG_{B_k},\\
 D_{C_k}^{F,G} &= F_{C_k}\cup F_NG_{C_{k+1}},\\
 D_H^{F,G} &= F_H\cup F_NG_H.
\end{aligned}
\]

The exact finite big-step relation of the cons cell is

\[
 (F;G)_x=T_{F,G}^*D_x^{F,G}. \tag{1}
\]

**Proof of (1).** Inspect the final constructor of the finite `run`
derivation. Every constructor except `run_node_cdr_continue1` is exactly
one of the alternatives in D. The exceptional constructor prepends one
T transition and has a strictly smaller derivation for restarting this
same cons cell. Induction on this derivation gives a finite T path followed
by D. Conversely, a zero-length T path and a D alternative give the
corresponding non-restart constructor. Induction on the length of a finite
T path repeatedly applies `run_node_cdr_continue1`. This proves both
directions without any termination assumption on F or G.

## Computing both bracketings

Under the hypotheses, A_{B_k} and C_{C_k} are empty for every positive k.
Put T = A_N B_{C_1}. Formula (1) first yields

\[
\begin{aligned}
 (A;B)_N &= T^* A_NB_N,\\
 (A;B)_{B_k} &= T^* A_NB_{B_k},\\
 (A;B)_{C_k} &= T^*(A_{C_k}\cup A_NB_{C_{k+1}}),\\
 (A;B)_H &= T^*(A_H\cup A_NB_H).
\end{aligned}
\]

Since C has no Continue exit, the outer cons in `(A;B);C` never restarts.
Applying (1) again and distributing composition over union gives

\[
\begin{aligned}
 ((A;B);C)_N
   &=T^*(A_NB_{B_1}\cup A_NB_NC_N),\\
 ((A;B);C)_{B_k}
   &=T^*(A_NB_{B_{k+1}}\cup A_NB_NC_{B_k}),\\
 ((A;B);C)_{C_k}
   &=T^*(A_{C_k}\cup A_NB_{C_{k+1}}),\\
 ((A;B);C)_H
   &=T^*(A_H\cup A_NB_H\cup A_NB_NC_H).
\end{aligned} \tag{2}
\]

For the other bracketing, the inner cell `B;C` never restarts, so

\[
\begin{aligned}
 (B;C)_N &= B_{B_1}\cup B_NC_N,\\
 (B;C)_{B_k} &= B_{B_{k+1}}\cup B_NC_{B_k},\\
 (B;C)_{C_k} &= B_{C_k},\\
 (B;C)_H &= B_H\cup B_NC_H.
\end{aligned}
\]

The restart relation of `A;(B;C)` is therefore again precisely
`A_N B_{C_1} = T`. Substituting these four relations into (1), using
`A_{B_k} = empty`, gives exactly the four right sides of (2). Every finite
exit relation is equal, which proves the theorem.

The repeated event is B's Continue(1): it repeats the same A-then-B pair
in both bracketings. In the left bracketing the inner cell catches it; in
the right bracketing the outer cell catches it. Formula (2) accounts for
arbitrarily many finite repetitions. Infinite repetitions or divergence
inside a component create no additional finite derivation on either side.

## Exact exit mapping before any restart

The following cases give another way to review equation (2). Every row may
be preceded by any finite number of T repetitions.

| Event after entry | Result on both sides |
| --- | --- |
| A exits Continue(k) | Continue(k), same registers |
| A halts | Halt, same registers |
| A normal; B exits Break(1) | Normal; C is skipped |
| A normal; B exits Break(k+1), k >= 1 | Break(k); C is skipped |
| A normal; B exits Continue(1) | Restart A then B |
| A normal; B exits Continue(k+1), k >= 1 | Continue(k) |
| A normal; B halts | Halt |
| A normal; B normal; C normal | Normal |
| A normal; B normal; C exits Break(k) | Break(k) |
| A normal; B normal; C halts | Halt |

## Static criterion and implementation obligations

The static bounds already used in the search are sufficient. For a cons
cell `(X,Y)`, if its children's bounds are `(b_X,c_X)` and `(b_Y,c_Y)`, use

\[
 b_{(X,Y)}=\max((b_X-1)_+,b_Y),\qquad
 c_{(X,Y)}=\max(c_X,(c_Y-1)_+).
\]

Increment and Halt have bounds `(0,0)`, Decrement has `(1,0)`, Break(k)
has `(k,0)`, Continue(k) has `(0,k)`. Induction on finite `run` derivations
shows every emitted positive break or continue level is at most the
corresponding bound. The restarting constructor uses the induction
hypothesis for the smaller restarted derivation. Thus the new sufficient
test is just **break_bound(A) = 0 and continue_bound(C) = 0**; the other
four component bounds are unrestricted.

The hypotheses cannot simply be discarded: if A is Break(1), then
`A;(B;C)` skips both B and C, whereas `(A;B);C` executes C. If A and B are
increments and C is Continue(2), `A;(B;C)` repeatedly restarts the outer
cell, whereas `(A;B);C` has a finite Continue(1) exit.

This is a semantic source-program lemma. To apply it to a source DAG,
preserve the action relations of A, B, and C, or justify all nested changes
bottom-up. To apply it to a binary table, additionally verify every use of
every changed decoder row, including backward-peek and runtime microcode
contexts. A change in the source PC paths is expected and must be reflected
in the binary-to-source certificate. The lemma alone gives neither a
state-count saving nor a correct changed binary machine.

Primary semantics: `ZF/m254/coq/tm/RM.v` at upstream snapshot
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`.

https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/tm/RM.v
