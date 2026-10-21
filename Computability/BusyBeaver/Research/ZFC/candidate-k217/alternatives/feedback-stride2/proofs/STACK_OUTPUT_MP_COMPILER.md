# Stack-output MP with an unconditional result push

This is a command-level construction. Physical allocation and blank startup are separate obligations. It does not rely on the abandoned, erroneous stride-three sketch.

Let P be Cantor pairing; [x;w]=P(x,w), I(a,b)=4P(a,b), and Q_i a=4P(i,a)+2. Retain the exact AX command and composite transfer S=DROP;NIP;NIP. Thus S either halts if incoming top or cache is1, or sends (t,[x;v],d,h) to (h,v,d,x). AX(c;x,y), with U=d,A=d+x,B=h+y, pushes eight implication-valued heads a1,...,a8, followed by Q_d h and saved t; supplies its unchanged gated bundle on top; resets counter/cache to0.

## New MP interface

Set y=d+x. Define M(x) by

- if I(t,y)=h, return (0,[y;w],y,0);
- otherwise return (0,[0;w],y,0).

This is obtained semantically by omitting old MP's success-only zero push, retaining its successful copy of y to top, and then executing the inherited PUSH macro once on every returning branch. That low-level PUSH saves the current top in the stack and clears top. Its scratch-input preconditions must be checked in the source splice.

The stack grows by exactly one on every command, including failed MP. The result is carried by the new head, not by top. This is a real change in executable proof-command semantics, not a state renaming or a source re-association.

## Soundness

From a theorem-valued top/cache and an explicit safe stack wrapper, successful M pushes the MP consequence y; failed M pushes truth0. Both set top/cache to truth0. AX and S retain their old soundness arguments. Therefore every reached halt from a safe/protected seed witnesses native1. All natural codes, including I(0,0)=P(0,0)=0, are covered.

## Structural blocks

Write A0=AX(0;0,0). The following exact contracts use arbitrary numerical input top and stack; a permitted early halt is allowed where stated.

H=A0;S^11 retains its old contract: either halt or (t,[z;v],d,h) -> (t,v,0,z). The only possible halt is triggered by incoming t=1.

PUSH=A0;S^9;M(0);S maps every (t,w,d,h) to (0,[t;w],0,0), without halting. After nine shifts the tuple is (a8,[t;w],0,Q_d h). The MP condition fails by the tag mismatch, since I(a8,0) is0 mod4 and Q_d h is2 mod4. M pushes0, and the final S removes that0 while leaving top/cache0. No saved t is tested.

DISCARD=M(1);AX(1;0,0);S^10;M(0);S^2 maps (t,w,0,0) to (0,w,0,0), without halting. First M fails because I(t,1)>0, leaving (0,[0;w],1,0). AX's gate is disabled by U=A=C=1 and its saved top is0. Ten shifts leave (Q_1 0,[0;w],0,0). The next M again fails because I(Q_1 0,0)>0. It adds a second zero, and two shifts remove exactly those two zeros.

J(u)=M(u);S maps (0,w,0,0) to (0,w,u,0) for every u>=0. For u>0 M fails; for u=0 it succeeds by the zero alias. In either case it pushes0 and the following S removes exactly that0. There is no special empty-word requirement at u=0.

These assertions follow from identities on numerical pairing, not an assumption that a finite sequence of zero heads is encoded injectively with its length.

## Complete strong compiler

For every finite native derivation of X construct B_X satisfying

    (t,w,0,0) -> halt or (X,w,0,0)

for every natural t,w. Truth uses DISCARD. Every axiom, full bundle and GEN block from the transfer compiler is unchanged except that it invokes the repaired PUSH, DISCARD and J just defined:

- row j=1,...,7: DISCARD;AX(c;a,b);S^(j+1);H^(9-j);
- dominated row L(a,b,c,u), u<=a: DISCARD;J(u);AX(c;a-u,b);S^9;H;
- enabled bundle(a,b,c): DISCARD;AX(c;a,b);H^10;
- GEN_i(X): B_X;PUSH;J(i);S;AX(i;0,0);S^10.

For MP with major K=I(A,B), use

    DISCARD;PUSH;PUSH;
    B_K;PUSH;B_A;PUSH;S;S;
    M(B);S;S;
    AX(B;0,0);S^11.

The first three blocks reserve two safe zero heads: (0,[0,0;w],0,0). Building/pushing the major and minor followed by two shifts gives (A,[0,0;w],0,K), unless a sound early halt is allowed. Successful M(B) produces (0,[B,0,0;w],B,0). Two shifts give (B,[0;w],B,0), or halt if B=1 on the second shift. This is exactly the old compiler's successful-MP cleanup input. AX(B;0,0);S^11 returns (B,w,0,0), or halts when B=1. No head of the arbitrary suffix w is consumed.

For A=B=0, M succeeds intentionally, inserts0, and every stated zero is still removed by the exact pairing identities. There is no hidden nonzero assumption.

Induction on finite derivations proves the strong contract. As before, B_1;H halts from every (t,w,0,0). Thus completeness has not been weakened to a bounded proof search.

## Scheduler and protected startup

Keep the source field layout of whichever donor is used. With transfer-first layout S=[0], M(x)=[1,x], AX(c;x,y)=[c+2,y,x], the same cofinal padding AX(0;1,Y) works and preserves strict right-projection drainage. A permuted donor requires its already proved corresponding selector packing, not an unexamined reuse of these numbers.

The old conservative command weights S=-1, MP=0, AX=10 remain valid: new M has actual stack gain+1, which only improves the old lower bound. Therefore any already verified protected startup remains safe if the actual new table reaches the same appropriate source root/store and safe wrapper. This is conditional on the new literal startup; no new blank-start claim is made by the command proof.

## Drained-counter variant and measured prices

A second interface changes successful M to (0,[y;w],0,0), retaining failure (0,[0;w],y,0). All auxiliary blocks above are unchanged: their only successful use has y=0. The logical MP block needs only one reserved zero and no AX cleanup:

    DISCARD;PUSH;B_K;PUSH;B_A;PUSH;S;S;M(B);S;S.

Before M it has (A,[0;w],0,K); after M it has (0,[B,0;w],0,0), so two shifts return (B,w,0,0) or halt if B=1.

Owned exact pricing checked both selector orders and both associations of the common preparation/conditional-result/push factors. The non-draining stack-output interface costs202 distinct source nodes and allocates217 raw states in all four versions. The draining version costs203 nodes and allocates218 raw states in all four. These are provisional allocations, not calibrated physical machines. See STACK_ASSOCIATION_PRICES.json and the emitted inert source/table files. No claim of215 states is made.
