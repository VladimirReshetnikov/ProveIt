# Independent audit of the MP padding and direct-selection changes

## Revised successful MP

The proof in `analysis/reduction_search/no_mp_padding/proof.md` correctly
changes only successful MP from (z,[0;w],z,0) to (z,w,z,0). The deleted
source block is PUSH0 at [3847,3866). Its incoming top is zero because the
preceding transfer clears T and the following comparison never increments
T. The final PAR4 still installs z, preserves z in its counter, and leaves
scratch registers zero.

The new proof compiler's explicit initial `DISCARD;PUSH` reserves a zero.
For M=I(A,Y), no-early-halt execution gives:

| Step | Current | Stack | Counter | Cache |
| --- | --- | --- | --- | --- |
| DISCARD;PUSH |0|[0;w]|0|0|
| Build(M);PUSH |0|[M;0;w]|0|0|
| Build(A);PUSH |0|[A;M;0;w]|0|0|
| S;S |A|[0;w]|0|M|
| MP'(Y) |Y|[0;w]|Y|0|
| H |Y|w|0|0|

Here H=AX(0;0,0);S^11. Its first ten transfers encounter only the generated
nonfalsity rows and the zero initial cache; its final transfer tests the
incoming top. It consumes precisely the explicitly reserved zero after
successful MP'. If Y=1 it halts instead, as allowed by the strong Build
contract. Premise builders may also halt early. No old NIP cleanup is used:
this is the final three-command source language, not the earlier historical
four-command presentation.

The MP uses inside PUSH and DISCARD remain forced failures. For PUSH the
cache is a quantifier code of residue2 mod4, while the tested implication
has residue0. DISCARD compares positive implications against zero. J(u)
uses positive u and zero current/cache, hence fails and installs u only in
the additive counter. J(0) is correctly omitted because I(0,0)=0 could
succeed. The unchanged soundness and stack-credit invariants still apply:
MP' preserves the stack and therefore satisfies conservative weight0.

The abstract zero certificate is a genuine finite inductive invariant over
all execution lengths, rather than a bounded run. Its advertised initial
state is the canonical zero-register source entry, but it also contains
the actual protected bootstrap frame: at ordinal136 its domain masks are
(zero=128, positive=1), requiring only Y=0 and N>0. The actual register
vector (1,0,13,0,0,1,0,0,1) satisfies that domain. Thus the same invariant
covers that interior startup as well. This is in addition to the local
structural zero argument above.

## Direct-selection S25

The literal pre-pop macro in
`analysis/reduction_search/direct_selection/direct25_0.macro.json` has the
following exact structured shape. Register T is1 and cache H is5.

    clear(T);
    if dec(H) succeeds:
        increment(T);
        if dec(H) fails: halt;
        increment(T);
        while dec(H) succeeds: increment(T)

The branch `if dec(H) fails: halt` is the source tree
`((CD5,CB1),CH)`. Its zero branch reaches CH; its positive branch decrements
H and uses CB1 to bypass CH. The final loop is `(CD5,(CI1,CC2))`.

For arbitrary natural initial cache h:

- h=0: the outer decrement fails, the whole body is skipped, and T=H=0.
- h=1: the outer decrement succeeds, T becomes1, and the next decrement
  fails, reaching CH.
- h>=2: the two decrements consume2, the two increments contribute2 to T,
  and the transfer loop contributes the remaining h-2. Thus T=h, H=0.

The loop proof uses invariant T+H=h and decreases H on each iteration.
It terminates for every natural h. Every other register is preserved before
the unchanged stack pop. Since the arithmetic scratch registers remain
zero, the inherited fourteen-primitive pop contract applies. For
W=P(x,v), the final result is (h,v,d,x) when h!=1, and the command halts
exactly at h=1. This is precisely the old S contract. Total cost is
2 clearing primitives +9 body primitives +14 pop primitives =25.

## Copy-based S26

`copy26_0.macro.json` first clears T and copies H into T and X while clearing
H. It then tests X by two decrements. X=0 skips the body, X=1 reaches CH,
and X>=2 skips CH and clears the remaining X. The final pop sees X=Y=H=0
on every nonhalting path, and T is the original h. It has the same exact S
contract for all naturals. Its cost is2+4+6+14=26.

Both source constructions leave the earlier source and the protected
bootstrap address unchanged. The retained-CFG audit identifies the changed
old body interval [3876,3895); the clear-T and pop blocks are retained.
The finite256 pre-pop tests are useful implementation checks. The case
analysis and loop invariant above supply the unbounded mathematical
argument. Neither source simplification by itself proves a smaller
physical binary machine. The reported source DAG counts are201 for S25
and199 for S26, against the baseline197.

## Audit result

No gap was found in the revised reserved-zero MP3 proof or in the exact
S25/S26 command semantics. These are ordinary mathematical audits, not new
proof-assistant certificates. Literal table allocation, startup replay,
and complete arbitrary-value primitive simulation remain separate tasks.
