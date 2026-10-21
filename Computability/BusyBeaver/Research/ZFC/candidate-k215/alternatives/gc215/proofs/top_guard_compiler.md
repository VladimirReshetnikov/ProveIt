# A total proof compiler with the falsity guard on the outgoing top

Date: 2026-10-21. Independent all-natural command-level proof by the formalism research agent. This document does not certify a particular binary table, physical register implementation, or blank initializer.

## The new command and the exact claim

Let `P(a,b)=(a+b)(a+b+1)/2+b`, `I(a,b)=4P(a,b)`, and `Q_i(a)=4P(i,a)+2`. Let `head(w),tail(w)` be the two projections of Cantor pairing, so in particular `head(0)=tail(0)=0`. Write `[x;w]=P(x,w)` and extend the notation to a finite list of heads over an arbitrary numerical tail. These are identities on all natural numbers; no injective encoding of finite list length is asserted.

Keep exactly the accepted numerical calculus D: truth0, the seven retained logical rows, the dominated eighth row, the full original gated bundle, numerical modus ponens, and theorem-only generalization. The previously established comparison of D with ZFC refutability is an inherited premise.

Replace the transfer command by

```
S_top(t,w,d,h) = HALT                         if t=1;
S_top(t,w,d,h) = (h,tail(w),d,head(w))         if t!=1.
```

This tests precisely the incoming top which would otherwise be discarded. It differs from the accepted single-cache-guard transfer: `(1,w,d,0)` now halts, whereas `(0,w,d,1)` returns normally, with top1. These changes are covered explicitly below; no claim of operational equivalence to the cache-guard command is needed.

Keep MP and AX unchanged:

```
MP(x): y=d+x;
       if I(t,y)=h return (y,[0;w],y,0);
       otherwise return (0,w,y,0).

AX(c;x,y): U=d, A=d+x, B=h+y, C=c;
           return (G(A,B,C),
                   [R1,...,R7,L(A,B,C,U),Q_U(h),t;w],0,0).
```

Here `G` is the full permitted bundle if `C!=A,B`, and truth0 otherwise. Every gate and each of the first eight generated heads has tag0, hence differs from1. The ninth head has tag2, hence differs from0 and1. In particular the enabled bundle is `N(V0 -> J0)`, with literal `N(X)=I(X,1)`, so it too is implication-coded. AX resets counter/cache and saves the incoming top as its tenth head.

**Theorem.** For each finite D-derivation of a numerical code X, one can effectively construct a finite command word B_X which, for every natural t,w, terminates normally with exactly

```
B_X(t,w,0,0) = (X,w,0,0).
```

No command in that block halts. Thus this compiler has a stronger conclusion than the earlier cache-guard compiler's alternative of an early halt or the claimed return. The word `B_1;S_top` halts from every such input if D derives1. Together with theoremhood soundness and the unchanged scheduler, this proves source halting iff native refutability, hence iff ZFC inconsistency under the inherited calibration.

## 1. The exact AX shift lemma

Write the ten new AX heads as `a1,...,a8,q,t`, where `q=Q_d(h)`, and write its gate as g. Set `v0=0`, `vj=aj` for `1<=j<=8`, `v9=q`, `v10=t`. For `1<=k<=10`, after k applications of S_top the state is

```
(v_(k-1), [v_(k+1),...,v10;w], 0, vk).
```

For k=10 the displayed stack is simply w. Each of these steps terminates normally. The first guard sees g; the next nine see `v0,...,v8`. All are tag0 and hence are not1. The eleventh shift sees `v9=q`, also not1, and returns

```
(t,tail(w),0,head(w)).
```

No guard has tested t, any head of the original w, or the incoming h. In particular this calculation remains valid when any of these raw inputs is1. It uses only the exact inverse identity for pairing, so it also covers every zero alias.

## 2. Total structural macros

Put `D=AX(0;0,0)` and define

```
H    = D; S_top^11;
PUSH = D; S_top^9; MP(0).
```

For all natural inputs, these macros terminate normally and obey

```
H(t,w,d,h)    = (t,tail(w),0,head(w));
PUSH(t,w,d,h) = (0,[t;w],0,0).
```

The H equation is exactly the eleventh-shift calculation. Unlike the old macro with a cache guard, this H returns top1 without halting. For PUSH, after nine shifts the top is a8, the cache is `q=Q_d(h)`, the counter is0, and the stack is `[t;w]`. Then `I(a8,0)` has tag0 and q has tag2, so MP(0) fails and gives the stated result.

Starting with d=h=0 define

```
DISCARD = MP(1); AX(1;0,0); S_top^10; MP(0).
```

The first MP necessarily fails because `I(t,1)>0`, giving `(0,w,1,0)`. AX has A=C=1, so the gate is0 and the saved tenth head is0. Ten shifts give `(Q_1(0),w,0,0)`. Since `Q_1(0)>0`, final MP(0) fails. Thus DISCARD terminates normally at `(0,w,0,0)` for every natural t,w, including t=1.

On an input `(0,w,0,0)`, let J(0) be empty and let `J(u)=MP(u)` for u>0. Then J(u) returns `(0,w,u,0)`: for positive u, `I(0,u)>0` forces failure. Omitting MP when u=0 is necessary because the literal alias `I(0,0)=0` would otherwise push a zero.

## 3. Every axiom and truth

Truth uses `B_0=DISCARD`. Every retained row `Rj(a,b,c)`, for `1<=j<=7`, uses

```
DISCARD; AX(c;a,b); S_top^(j+1); H^(9-j).
```

After the direct shifts, row j is on top. There remain exactly `9-j` new stack heads above the old w, ending in the saved zero. Each H pops one of these heads while preserving the selected row; its last cache is therefore0. The final state is exactly `(Rj(a,b,c),w,0,0)`. Every component macro is total on these inputs.

For the dominated eighth row `L(a,b,c,u)`, with u<=a, use

```
DISCARD; J(u); AX(c;a-u,b); S_top^9; H.
```

The nine shifts select the eighth head, and H removes the saved zero while preserving that selected head. The input arithmetic supplies exactly U=u, A=a, B=b and C=c. The u=0 case uses the empty J(0).

For an enabled full bundle, use

```
DISCARD; AX(c;a,b); H^10.
```

The H macros preserve the exact gate, remove exactly the ten new heads, and finish with the saved zero in cache and the original stack w. No conjunct or supporting formula of the inherited bundle is altered.

## 4. Generalization

Given B_X, set

```
B_(Q_i X) = B_X; PUSH; J(i); S_top; AX(i;0,0); S_top^10.
```

After PUSH and J(i) the state is `(0,[X;w],i,0)`. The single S_top tests top0 and returns `(0,w,i,X)`, including when X=1. AX has U=A=C=i and therefore zero gate. Its ninth head is exactly `Q_i(X)` and its tenth is saved0. The final ten shifts return `(Q_i(X),w,0,0)` normally. This also covers i=0 without a spurious zero push.

## 5. Modus ponens, including every alias and falsity case

Suppose D proves A and `M=I(A,B)`, with their compiled blocks already constructed. Define

```
B_B = B_M; PUSH; B_A; PUSH; S_top; S_top;
      MP(B); AX(B;0,0); S_top^11.
```

The major-first order is legitimate structural recursion on the two finite premise proofs. It introduces no logical dependency cycle. The exact intermediate states are:

1. `B_M;PUSH` gives `(0,[M;w],0,0)`.
2. `B_A;PUSH` gives `(0,[A,M;w],0,0)`.
3. The first shift gives `(0,[M;w],0,A)` and the second gives `(A,w,0,M)`. Both guards test0. In particular the minor A=1 causes no halt.
4. MP(B) succeeds by exact equality `I(A,B)=M`, giving `(B,[0;w],B,0)`.
5. AX(B;0,0) has A=C=B, so its gate is0. It resets d,h and saves B as its tenth head above `[0;w]`.
6. Eleven shifts return `(B,w,0,0)`. Their last guard sees the tag2 code `Q_B(0)`, so this is a normal return even when B=1.

When A=B=0, the major M is the literal natural0. MP(0) intentionally succeeds and pushes exactly the zero removed in the final cleanup. If w=0, the encoding `[0;0]=0` does not invalidate the inverse-pairing identities or the displayed state equalities.

Induction on the finite derivation proves the total compiler theorem. A finite proof DAG may first be expanded to a finite proof tree. This is an effective transformation on finite data; its considerable runtime is immaterial to the existence theorem.

## 6. Soundness and safe arbitrary tails

For a safe run, top, cache and every head exposed from the stack are native theorems. AX preserves this because each logical row is an axiom, its ninth head is a theorem generalization of the incoming cache, and its tenth saves a theorem. MP either gives truth0 or applies native numerical MP and pushes truth0. S_top either halts because its theorem-valued incoming top is1, or transfers two theorem-valued values to top/cache. Thus every actual halt proves native1.

In particular, incoming top!=1 and cache1 is a normal transfer. Its output top1 remains theorem-valued and the next S_top would halt, although intervening commands may erase it. Completeness does not require that every possible appearance of a refutation be caught immediately; the explicit compiled suffix guarantees a later tested1.

The protected-tail theorem for the unchanged three-command scheduler also transfers. Its conservative balances are still `S_top=-1`, `MP=0`, `AX=+10`; successful MP may add an extra zero. The published all-natural credit proof depends only on these balances, exact wire fields, and the fact that every tested value is a theorem. At each returning S_top, the sufficient-credit invariant supplies an explicit theorem head above the arbitrary tail. If it halts instead, it tests a theorem top. Thus no tail head is exposed, and the same exact required initial credit d(N) applies; in particular d(1)=2. This invokes that separately proved combinatorial credit theorem, not finite credit tests.

## 7. Packing the refutation beyond every startup cutoff

The wire fields remain

```
fields(S_top)=[0];
fields(MP(x))=[1,x];
fields(AX(c;x,y))=[c+2,y,x].
```

Let F(fs,r) right-fold Cantor pairing of the field list fs over residual r, and define `tail([])=0`, `tail(k::L)=1+F(fields(k),tail(L))`. At positive proof-list boundaries the scheduler first decrements, then reads the fields, so these tail codes execute their finite command words exactly. A newly fetched candidate's first command is decoded without the leading decrement.

If D derives1, write `R=tail(B_1;S_top)`. For every Y the fresh candidate

```
N_Y = P(2,P(Y,P(1,R)))
```

executes `AX(0;1,Y)` followed by the same compiled refutation suffix. The first AX resets d=h=0 from any retained tuple. The total compiler then returns top1 with the old stack and zero counter/cache, and final S_top halts. Since `N_Y>=Y`, successful candidates lie above every fixed startup cutoff.

Every positive proof-list residual strictly decreases: after the initial decrement and one, two or three field unpairings, the new residual is at most its predecessor. Thus each candidate finishes unless it halts, and the unchanged increment-by-one scheduler reaches a successful candidate in finite time. This proves source halting iff native1 derivability for each safe seed covered by the ordinary or protected-tail invariant.

## Exact boundary of this result

The argument is a complete ordinary mathematical proof of the new all-natural command interface and its calibration inheritance. It does not assert that any proposed primitive source realizes S_top, that its scratch values are restored, that an allocator reaches a given state count, or that a binary table initializes the required safe source frame. Those concrete obligations need separate checks. The new guard placement may reduce source cost because the inspected register is also cleared; that opportunity is a source-engineering question, not a consequence of this proof alone.
