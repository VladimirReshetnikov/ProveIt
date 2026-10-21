# Moving the only falsity guard to AX entry

Date: 2026-10-21. Complete ordinary mathematical command-level proof. This is a separate candidate interface from both the old cache-guard transfer and the new top-guard transfer.

## Exact interface

Use the numerical calculus, Cantor pairing, formula operations, and full ten-head AX output specified in `top_guard_compiler.md`. Write `A0` for the old total AX command. Keep MP unchanged, replace transfer by the **total** command

```
S0(t,w,d,h) = (h,tail(w),d,head(w)),
```

and replace AX by

```
AX_guard(c;x,y)(t,w,d,h) = HALT                         if t=1;
AX_guard(c;x,y)(t,w,d,h) = A0(c;x,y)(t,w,d,h)           if t!=1.
```

The guard tests the incoming top. On normal return it must preserve every part of the old AX contract, including the incoming top saved as the tenth head. Neither the transfer nor MP can halt. All halts occur at AX entry.

**Theorem.** For every finite native proof of X, an effective finite block B_X has the following contract for all natural t,w:

```
B_X(t,w,0,0) either halts or returns exactly (X,w,0,0).
```

The word `B_1;AX_guard(0;0,0)` therefore halts from every such input. Under the unchanged scheduler, a safe initialized run halts exactly when the native numerical calculus proves1. The existing numerical-calculus-to-ZFC comparison then supplies the desired consistency calibration at command level.

## Structural macros and truth

Put `D=AX_guard(0;0,0)` and define

```
H = D;S0^11;
PUSH = D;S0^9;MP(0).
```

Each macro halts exactly when the incoming top t equals1. Otherwise their exact normal outputs are

```
H(t,w,d,h)    = (t,tail(w),0,head(w));
PUSH(t,w,d,h) = (0,[t;w],0,0).
```

These follow by counting the ten AX heads. No subsequent transfer has a guard. At the end of the first nine shifts for PUSH, cache `Q_d(h)` has tag2 while `I(top,0)` has tag0, so MP(0) necessarily fails.

For d=h=0 define

```
DISCARD=MP(1);AX_guard(1;0,0);S0^10;MP(0).
```

This block never halts. Its first MP fails because `I(t,1)>0`, even when incoming t=1. It therefore enters AX with top0. As A=C=1, the AX gate is0 and its saved top is0; the remaining calculation gives exactly `(0,w,0,0)`. Again J(0) is empty and J(u)=MP(u) for positive u, defined on a cleared input, giving `(0,w,u,0)`. This explicit zero exception prevents an unwanted successful MP(0).

## Axiom and inference blocks

Use exactly the same finite block formulas as for the top-guard compiler, with S0 and AX_guard substituted:

| Native proof step | Compiled block |
| --- | --- |
| Truth0 | `DISCARD` |
| Retained row Rj(a,b,c), 1<=j<=7 | `DISCARD;AX_guard(c;a,b);S0^(j+1);H^(9-j)` |
| Dominated L(a,b,c,u), u<=a | `DISCARD;J(u);AX_guard(c;a-u,b);S0^9;H` |
| Enabled full bundle | `DISCARD;AX_guard(c;a,b);H^10` |
| GEN from X to Q_i(X) | `B_X;PUSH;J(i);S0;AX_guard(i;0,0);S0^10` |
| MP from A and M=I(A,B) to B | `B_M;PUSH;B_A;PUSH;S0;S0;MP(B);AX_guard(B;0,0);S0^11` |

Every axiom block terminates normally with the exact requested theorem. All AX calls before selecting the theorem see top0; every subsequent H preserves a selected implication code or an enabled implication-coded bundle, never1. The counts remove exactly the generated heads through the saved zero and leave the original stack untouched.

For GEN, if B_X halts then the contract is satisfied. If it returns and X=1, the immediately following PUSH halts at its AX guard. If X!=1, PUSH returns `(0,[X;w],0,0)`, J(i) sets the counter, and S0 gives `(0,w,i,X)`. The subsequent AX therefore enters with top0, generates `Q_i(X)` as ninth head and saved0 as tenth, and ten shifts return exactly `(Q_i(X),w,0,0)`. No assumption about the decoded meaning of X is used.

For MP, compile the major M first. It is implication-coded and thus cannot be1. If its proof block returns, its PUSH therefore returns safely. Compile A over the preserved stack `[M;w]`. An early halt is allowed; if A=1 its following PUSH halts. Otherwise the two pushes and two shifts give `(A,w,0,M)` exactly. MP(B) succeeds by literal equality, returning `(B,[0;w],B,0)`. If B=1 the next AX guard halts. If B!=1, AX executes the old cleanup: A=C=B forces a zero gate, and eleven shifts return `(B,w,0,0)`. The successful-MP zero is removed exactly once.

This covers the raw alias A=B=M=0. In that case the successful MP(0) deliberately pushes zero; it is not replaced by a failed MP. Numerical zero-stack collapse does not invalidate the pairing inverse identities. This also covers both places where an old cache guard would have halted: a minor A=1 is caught at PUSH's AX entry, and a conclusion B=1 is caught at cleanup AX entry. Every other former cache guard may disappear without loss of the asserted return equation.

Induction on finite proofs gives the strong compiler. Earlier semantic halts do not need to preserve a final store. If B_1 were to return, it returns top1, so the appended AX_guard halts before modifying the store.

## Soundness, arbitrary tails and cofinal scheduling

The theoremhood invariant is unchanged on normal returns. S0 moves the theorem-valued old cache to top and the exposed theorem head to cache. MP either supplies truth or uses numerical MP. AX_guard either halts with theorem-valued top1 or has exactly the old AX theorem outputs. Thus every actual halt proves native1, including arbitrary raw command encodings.

For a protected arbitrary stack tail, the three-command credit recurrence remains identical: S0 costs one explicit head, MP costs zero conservatively, AX_guard adds ten on normal return. Any AX halt is already sound. Every nonhalting transfer therefore has the same guaranteed explicit theorem head available, and the previously proved all-natural credit theorem applies unchanged, including d(1)=2. No assumption is made that buried raw tail heads are theorems.

The wire fields remain `[0]`, `[1,x]`, `[c+2,y,x]` respectively. Let R encode the fixed finite suffix `B_1;AX_guard(0;0,0)` using the unchanged successor-and-pairing convention. For every Y the fresh candidate

```
N_Y=P(2,P(Y,P(1,R)))
```

first calls `AX_guard(0;1,Y)`. If its incoming top is1 it halts immediately. Otherwise it resets counter/cache and runs the universal strong suffix, which halts. Since N_Y>=Y, there are successful candidates beyond every fixed cutoff. Each nonhalting candidate's positive proof pointer strictly decreases after decrement and field decoding; the ordinary candidate increment then eventually reaches one of these successful candidates.

## Scope and physical obligation

This guard relocation is a genuinely different command semantics. It is calibrated at the level stated, with all natural inputs and all zero/falsity cases covered. A source implementation must independently prove the guard is exactly t=1, restores the original t on every other branch before old AX saves it, restores private scratch values, and leaves field decoding unchanged. Source size, allocated state count, whole-tape primitive simulation and blank initialization remain separate obligations.
