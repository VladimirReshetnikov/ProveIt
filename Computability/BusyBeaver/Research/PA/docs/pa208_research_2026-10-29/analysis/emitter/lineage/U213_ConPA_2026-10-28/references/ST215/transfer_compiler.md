# Complete proof compiler for the three-command NIP-transfer enumerator

Date: 2026-10-21. Ordinary all-natural command-level proof. This is not itself a binary runtime or blank-initializer certificate.

## 1. Exact commands and unchanged numerical calculus

Keep the calibrated dominated calculus, every logical row, the original full gated seed bundle, truth 0, native falsity 1, MP and theorem GEN. Write I(a,b)=4P(a,b), Q_i a=4P(i,a)+2, where P is Cantor pairing. In particular I(0,0)=0, while every Q-code is nonzero and has tag 2.

At command boundaries use (t,w,d,h) for top, encoded formula stack, additive counter, and cached formula. A stack [x;w] means P(x,w); zero unpairs as (0,0). Replace NIP by the transfer command S:

- If h=1, S halts.
- Otherwise, writing unpair(w)=(x,v), S(t,w,d,h)=(h,v,d,x).

Keep MP(x) exactly:

- Put y=d+x.
- If I(t,y)=h, return (y,[0;w],y,0).
- Otherwise return (0,w,y,0).

Keep AX(c;x,y) exactly. Put U=d, A=d+x, B=h+y, C=c. It returns

    (gate(A,B,c), [r1,...,r7,L(A,B,c,U),Q_U h,t;w], 0, 0).

Here gate is the full original bundle when c differs from A and B, and 0 otherwise. Each rj and L is an implication code, hence not 1; Q_U h has tag 2, hence is neither 0 nor 1. The saved t is the tenth stack entry. These ten-entry and nonfalsity facts are the only formula-output properties used in the compiler bookkeeping below.

Remove DROP. The new fields are

    fields(S)=[0],
    fields(MP(x))=[1,x],
    fields(AX(c;x,y))=[c+2,y,x].

The literal source and its selector CFG must establish these command equations and fields separately.

## 2. Two structural macros recovered without DROP

Let D=AX(0;0,0). Its gate is irrelevant in this section: the first S overwrites it.

### Top-preserving pop with a top-falsity guard

Define H=D;S^11. From any (t,[x;w],d,h), the ten AX heads are generated. After the first ten S commands the tuple is

    (Q_d h,[x;w],0,t).

All cache tests so far were on zero or the first nine new entries, so none halts. The eleventh S halts if t=1; otherwise it yields

    (t,w,0,x).

Thus H is a top-preserving pop with a top-falsity guard: it halts exactly when the incoming top t is 1; otherwise it preserves that top, removes exactly one preexisting stack head, loads that head into cache, and resets the counter to zero. It is not operationally equivalent to old NIP, which tests the incoming cache h instead. In particular H may erase an incoming h=1 without halting: AX resets h before any S test, and Q_d h still has tag 2. This distinction is intentional; the separate soundness invariant and the explicit completeness blocks below do not require old NIP equivalence.

### Save the top and reset

Define PUSH=D;S^9;MP(0). After nine S commands the tuple is

    (L(A,B,0,d),[t;w],0,Q_d h).

The cache has tag 2, whereas I(top,0) has tag 0, including the zero alias. Therefore MP(0) necessarily fails. The exact final tuple is

    (0,[t;w],0,0).

This holds for every natural t,w,d,h and never halts. It restores a useful push operation even though the primitive DROP command is absent.

## 3. Strong block invariant and truth/reset

For every theorem code X, construct a finite block B_X which, for all natural t,w, starting at (t,w,0,0), either halts or returns exactly

    (X,w,0,0).

No theoremhood of the arbitrary incoming t or stack w is required by this completeness contract. Early halts count as success; soundness is proved independently for safe actual runs.

Define DISCARD=MP(1);AX(1;0,0);S^10;MP(0).

- The first MP fails because I(t,1)>0 and h=0, giving (0,w,1,0).
- AX has A=c=1, so gate is zero. It resets d,h and pushes nine non-1 rows followed by saved 0.
- Ten S commands give (Q_1 0,w,0,0).
- Since Q_1 0>0, I(Q_1 0,0)>0, so final MP(0) fails and gives (0,w,0,0).

Thus DISCARD is B_0 and never halts. Define J(u), only when the current top, counter and cache are all zero, as the empty block when u=0, and MP(u) when u>0. The latter fails because I(0,u)>0, yielding (0,w,u,0). Omitting MP when u=0 is essential: I(0,0)=0 would otherwise succeed and push an unwanted zero.

## 4. Axiom blocks

### Retained row j, 1<=j<=7

For requested parameters (a,b,c), execute

    DISCARD; AX(c;a,b); S^(j+1); H^(9-j).

AX has U=0 and the requested A=a,B=b,C=c. After j+1 shifts, row j is top and row j+1 is cache. Exactly 9-j generated entries remain over w, the last being saved zero. Each H preserves the selected top and pops one of those entries, resetting d to zero. The final cache is therefore zero and the stack is exactly w. Selected logical rows are not 1, so their repeated H tests do not halt.

### Dominated row L(a,b,c,u), with u<=a

Execute

    DISCARD; J(u); AX(c;a-u,b); S^9; H.

After AX the desired L is entry 8. Nine shifts put it on top, with Q_u 0 cached and just saved zero above w. H removes that zero and restores cache zero. The u=0 case uses the empty J(0), not a successful zero-alias MP.

### Full original bundle

For an enabled triple c!=a,b, execute

    DISCARD; AX(c;a,b); H^10.

The desired full bundle is top after AX. The ten H macros remove exactly its ten generated entries, preserving that top and ending with saved zero in cache. No support-bearing subformula or vacuity conjunct is removed or replaced.

## 5. Generalization

Given B_X, construct

    B_(Q_i X) = B_X; PUSH; J(i); S; AX(i;0,0); S^10.

If B_X returns, PUSH gives (0,[X;w],0,0). J(i) sets d=i without changing the stack, with the necessary empty i=0 case. The single S then gives (0,w,i,X), with no test of X because its incoming cache was zero.

AX has U=A=c=i, so gate is zero, and its ninth entry is Q_i X, followed by saved zero. Ten shifts give exactly (Q_i X,w,0,0). The incoming X is not tested before AX resets the cache. This handles X=1 too, although an already available refutation needs no generalization.

## 6. Modus ponens: build the major first

Given B_A and B_(I(A,B)), construct

    B_B = B_(I(A,B)); PUSH; B_A; PUSH; S; S;
          MP(B); AX(B;0,0); S^11.

Ignoring earlier permitted halts:

1. B_(I(A,B));PUSH gives (0,[I(A,B);w],0,0).
2. B_A preserves that entire stack, and its following PUSH gives (0,[A,I(A,B);w],0,0).
3. Two shifts give (A,w,0,I(A,B)). The cache tested by the second shift is A; if A=1 the program has already halted successfully.
4. MP(B) succeeds by literal equality, giving (B,[0;w],B,0).
5. AX(B;0,0) has A=c=B and gate zero. It pushes its nine new non-1 entries and saved B above the successful-MP zero.
6. Ten shifts put B in cache and leave [0;w]. The eleventh shift either halts when B=1 or returns exactly (B,w,0,0).

This calculation remains valid when A=B=0 and the implication code is raw zero. The successful MP deliberately pushes its zero, and step 6 removes precisely that zero. No theorem substitution or code-decoding assumption is used.

Induction on any finite native proof now produces B_X. A proof DAG may be expanded to a finite proof tree; the fact that the major is compiled before the minor causes no dependency cycle.

## 7. Refutation suffix, wire encoding and cofinality

If B_1 halts, nothing more is needed. If it returns (1,w,0,0), H halts at its eleventh shift by Section 2. Thus the fixed word B_1;H is successful from every (t,w,0,0).

For a field list fs and residual r, let F(fs,r) be right-nested Cantor pairing of fs above r. Define

    tail([])=0,
    tail(k::L)=1+F(fields(k),tail(L)).

At a positive proof-list boundary the unchanged scheduler decrements first, then reads the command's one, two or three fields. Accordingly tail(k::L) executes k and leaves tail(L). At a new candidate boundary the initial command is decoded without an outer successor.

Let R=tail(B_1;H). For every Y choose first command AX(0;1,Y), with candidate number

    N_Y=P(2,P(Y,P(1,R))).

From any retained tuple, this initial AX resets d=h=0. Its top and resulting stack may be arbitrary; the universal strong block B_1;H still succeeds. Pairing domination gives N_Y>=Y, so successful candidates are cofinal above every fixed startup cutoff, including 4.

Every nonhalting positive proof list drains strictly: its next residual is a right projection after one, two or three unpairings of pred(p), hence is at most pred(p)<p. Thus the ordinary candidate scheduler reaches any chosen N_Y above its initial next-candidate value unless it halts earlier. No artificial finite cutoff or fairness assumption is inserted.

## 8. Soundness and conclusion

For a safe actual seed, top, cache and every decoded stack head are native theorems. AX and MP preserve this as before. S either moves the theorem-valued old cache to top and a theorem-valued stack head to cache, or halts when its cache is the theorem 1. Therefore every actual halt implies a native refutation.

Conversely, a native refutation yields B_1 and cofinally many successful candidates by Sections 3-7. Under the unchanged enumerator scheduling and a safe initialized frame, the new three-command source halts if and only if the dominated numerical calculus proves 1, hence if and only if ZFC has a finite refutation under the inherited calibration.

This is a new complete command-level compiler, not merely a theoremhood invariant or finite test. It relies on the exact ten-entry AX interface and new selector field encoding. Its source implementation, all-natural register/primitive contracts, physical allocation, complete-tape runtime and blank startup remain separate obligations. No claim is made that the earlier protected-arbitrary-tail theorem transfers automatically; ordinary safe zero/theorem-stack initialization and this universal command-block argument suffice.
