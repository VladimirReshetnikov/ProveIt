# Additional successful-MP interfaces

Source pin: `43026ff42f0939f09b9e95495248cfadcad38e38`.

These are source-level search directions accompanying `cache_mp_proof.md`.
They are not additional sub-252-state machines. The duplicated-result
continuation below has been measured at 253 states; the selector variant
does not yet have an established binary budget. The purpose
is to let the binary compilation search change register placement without
mistaking the old proof-compiler interface for a logical necessity.

## 1. A conclusion in both current formula and cache

Replace successful MP by the two existing loops 198 then 207:

```
198: D -> X,T
207: X -> H
```

Immediately after a successful comparison, `T=H=X=Y=0`. Hence the result is

\[
 (T,W,A,D,H,X,Y)=(b,S,0,0,b,0,0).
\]

The other two registers, nextproof and prooflist, are preserved. Both proof
registers contain the proved conclusion, and the stack is unchanged, so the
same Safe invariant holds. The source needs a new pair node `(198,207)`;
these are existing loops, but their composition is not an existing source
node. The construction lane measured a correct 253-working-state runtime:
add old-label state 255 with rows `(0,R,151)` and `(1,R,37)`, and change
old row `204/read1` to target 255. All 8,366 strict affine guards pass under
the map `[4,5,0,8,6,2,1,7,3]`. The artifacts are
`agents/machine_reduction/rotation-candidates/mp-double253.tm` and its JSON
decoder, with check record `agents/machine_reduction/mp-double253-check.json`.
No blank bootstrap is claimed for that measured 253-state variant.

The two-command normalization for cache-only MP **does not** work here.
`DROP0; NIP0` pushes and then reloads `b`, leaving the cache equal to `b`.
Instead, the following uniform five-command suffix returns the original
proof-block contract:

```
DROP0; MP0; NIP0; DROP0; NIP0.
```

Using the new duplicated-result MP semantics throughout, its exact trace is

\[
\begin{aligned}
 (b,S,0,b)&\longmapsto (b,P(b,S),0,b)\\
 &\longmapsto (0,P(b,S),0,0)\\
 &\longmapsto (0,S,0,b)\\
 &\longmapsto (b,P(0,S),0,b)\\
 &\longmapsto (b,S,0,0).
\end{aligned}
\]

The displayed four fields are `(T,W,D,H)`. The last step halts when `b=1`.
For the second step, the MP comparison is

\[
 I(b,0)=2b(b+1)=b,
\]

which holds exactly when `b=0`. If `b>0`, that MP fails and clears both proof
registers. If `b=0`, its successful output is the same needed zero state.
Thus there is no omitted zero-code exception.

Replace the cache-only `MP B; DROP0; NIP0` tail of the block in
`cache_mp_proof.md` by `MP B` followed by this five-command suffix. All other
parts of the Contract induction, Safe proof, cofinal padding, and decreasing
proof-pointer argument are unchanged. This establishes the same ordinary
finitary completeness theorem for this source variant. No negative additive
operand or branch-dependent command choice is required.

## 2. A conclusion in current formula and a temporary selector

Replace successful MP by loops 198 then 201:

```
198: D -> X,T
201: X -> A
```

The result is

\[
 (T,W,A,D,H,X,Y)=(b,S,b,0,0,0,0).
\]

This maintains the formula/stack Safe invariant and clears both scratch
registers. It changes the boundary convention for the selector `A`, which
must consequently be included in the abstract working state until repaired.
It does not change either scheduler register. This source also needs one
new pair node, `(198,201)`.

The next command's encoded selector is **added** to `A`. Execute the nominal
command `AX(c=0,x=b,y=0,u=0)`. Its encoded selector is 3, so the actual AX
dispatch uses `c=b`; its first numeric parameter is also `a=b`. Consequently
the unchanged first/second freshness gates set the current formula to zero,
and AX resets `A,D,H` to zero. Its stack consists of the original `S`, the
old current formula `b`, and the usual nine AX outputs. The nine outputs are
not code 1, by the same constructor lemmas used in `Enum254.axList_ne_one`.

The normalization is therefore

```
AX(c=0,x=b,y=0,u=0); NIP0^10; DROP0; NIP0.
```

The ten NIPs discard the nine AX outputs and load `b` into the cache. The
last two commands return `(T,W,A,D,H)=(b,S,0,0,0)`, unless the final NIP
halts because `b=1`. This is a fixed thirteen-command suffix once the
conclusion code `b` is fixed. It supplies the MP induction step with the
same arbitrary-input-top, arbitrary-stack Contract.

The enlarged boundary state causes no new enumeration obstruction. From
any nonnegative `A`, an encoded AX selector 3 dispatches to AX with actual
selector `A`, and the unchanged AX routine clears `A,D,H`. The resulting
current formula and stack may be arbitrary inputs to the following proof
block. An unused operand of this initial AX still supplies unbounded
padding. Every candidate pointer continues to decrease between fetches,
because a nonzero selector changes the branch taken but does not create a
new pointer or modify nextproof. Thus the same cofinal-enumeration argument
applies after extending the finite-step semantics to include `A`.

## 3. A proof-list transfer has a possible decreasing rank

This section is an observation for future construction, not an implemented
variant. A proposed continuation that leaves a proved conclusion in a
formula register while replacing `(D,L)` by `(0,L+D)` does **not** require
the pointer `L` alone to decrease. Instead, use

\[
 R=L+D.
\]

At a non-fetch root, the machine first decrements the nonzero encoded
pointer, then unpairs a selector and the additive operand `x`. For its
resulting tail `r`, the Cantor inequality `P(a,b)>=a+b` gives

\[
 r+x < L_{\rm old}.
\]

Before any success transfer, the new rank is at most
`r+(D_old+x) < L_old+D_old`. Moving all of `D` into `L` preserves this sum.
DROP and NIP obey the same bound; AX consumes more pointer fields and
clears `D`, so it also obeys it. Therefore every candidate still reaches
another fetch or halts. Nextproof must remain unchanged by the success
action for this argument to give ordinary sequential enumeration.

Completeness would need a numerical continuation compiler instead of the
unchanged list-of-commands encoder. For a known successful MP conclusion
`b`, a desired successor pointer `K>=b` can be obtained by packing that
command with residual pointer `K-b`; success restores `K`. The sentinel
convention must be respected: a nonzero `K` means the next root first
decrements it. One can put a harmless AX/repair block with an unused large
padding operand before a desired continuation to arrange `K>=b`.

The rank proof alone is not that compiler. In particular, it is not a
license to increment nextproof by `b`, which can skip candidates. No
concrete smaller machine, complete continuation compiler, or formal endpoint
for this proof-list idea is claimed here.

## 4. Shared freshness-gate constraints

For cache-only MP, `clear(T); transfer(D,H)` is a correct common success
action for the MP gate and both AX gates. At MP success `T=0`; at the first
AX gate, transferring `D` early is harmless because the existing later
transfer has the same total effect. At the second AX gate `D=0`.

The straightforward binary construction has a real context cost. The old
entry state 143 is a shared clear loop: predecessor `252/read1` supplies the
context selecting `T`, while predecessor `120/read0` supplies the context
selecting `H`. Placing that entry as the left child of a new common action
loses the former context and selects `H`. Its use by equality failure means
the entry is not exclusive to the AX success phase. Six failed affine
cases in the first direct construction are evidence of this exact problem.
A fresh generic selector repairs it at a cost of one additional state.

This distinguishes a correct common register action from a proved state
saving. A successful reduction must account for the context bit, find a
valid existing entry, or obtain a separate fold elsewhere.

## 5. Evidence

`mp_success_interfaces.py` checks the literal structured RM implementation
of the first two success variants and the duplicated-result normalization.
For the selector variant it checks the normalization algebra for arbitrary
nine non-falsity stack entries; the fact that the original AX outputs satisfy
that condition comes from the original constructor proof, not a sampled
axiom generator. All integers in these checks are exact. The saved result
records 141 literal full-MP cases for each source variant, 330 duplicated
normalizations, 1,200 full duplicated-MP contract tails, and 108 selector
normalizations. The largest tested conclusion has 4,097 bits.

This note supplies ordinary mathematical proofs and finite diagnostics.
It does not assert new kernel-checked Lean theorems. The original statements
used are `L2Lib254.loop198`, `loop207`, `loop201`, `Enum254.axList_ne_one`,
`Enum254.mp_contract`, and the cofinal completeness proof, at the pinned
commit above.

## 6. Hoisting the destructive result transfer into equality success

There is a different exact shared-gate transformation which keeps the
original left/right entry contexts of both clear loops. Starting from
cache-MP, make these edits in the 219-node DAG:

```
130 = (123,197)             # unchanged cache-MP pair, now comparison wrapper
129 = (199,Break2)          # previously Break1
131 = (130,214)             # both AX and MP use this gate
132 = (130,Halt)            # NIP's halt gate
151 = (216,131)             # previously (216,130)
```

All other nodes remain unchanged; no source node is added. Helper 123 now
returns normal on equality and break2 on inequality, clearing `X,H` in either
case. In node130's left context, break2 becomes break1, so its caller can
still use it as a condition. Equality proceeds to the existing transfer197.
Consequently node130 now means: compare `X,H`; on equality transfer `D` into
`H` and return normal; on inequality return break1 with `D` unchanged.

At MP success, `T=0`, so common gate131's extra clear is harmless and the
result is exactly cache-MP. At MP failure it skips the clear, and `T` was
already zero. For AX, write its tail input as
`(T,A,D,H,X,Y)=(G,c,a,b,0,0)`. After copy192, `A=0,X=Y=c`.

If the first gate succeeds (`c=b`), it sets `T=0,D=0,H=a`. If it fails,
it leaves `T=G,D=a,H=0`. Restore211 and the existing transfer197 therefore
produce `X=c,Y=0,D=0,H=a` in both cases, with `T` already correctly masked
by the first gate. The second gate compares `c` with `a`; its transfer sees
`D=0`, and it masks `T` exactly as before. Thus the entire AX output,
including all auxiliary registers, is identical to the original.

For NIP, failure still clears `X,H`, preserves `D`, and pops exactly as
before. Success may move `D` before the immediate halt, which does not
change the halting criterion or the preceding Safe invariant.

The potential advantage is concrete: clear214 remains a right child, the
old comparison123 remains a left child, and transfer197 remains a right
child. The earlier failed common-action construction changed clear214 to a
left context. A binary state reduction is not inferred merely from this
improved source arrangement; it still needs compilation and checking.

## 7. A specialized zero/one NIP test using existing helper128

This transformation is independent of section6: it keeps node129's original
break1 convention. Starting from cache-MP, set

```
152 = (153,170)
153 = (DecH,132)
132 = (128,Halt)
```

The unchanged helper128 is `(DecH,129)`, with
`129=(clearH,Break1)`. It returns normal exactly when its input `H` is zero;
otherwise it clears `H` and returns break1. The new outer test has three
cases. For original `H=0`, node153's first decrement fails, ending normally.
For `H=1`, that decrement reaches zero and helper128 returns normally, so
node132 halts. For `H>=2`, helper128 clears the residual positive cache and
returns break1; node132 captures this break and skips its halt. In each
nonhalting case, node152 then executes the unchanged pop170.

This gives exactly the old NIP semantics from every clean scratch state:
halt iff the incoming cache is1, otherwise pop the stack into the cache.
It neither initializes nor uses `X`. It reuses all three original NIP pair
nodes and the existing helper128; it adds no source node. Its proof is a
direct case split on the incoming natural cache value, without a generic
reassociation assumption.

`shared_gate_and_nip.py` checks sections6 and7 separately against the exact
literal structured program. For each variant it covers141 complete MP
cases,90 complete NIP cases, and256 whole AX-tail cases. The AX-tail tests
include arbitrary current values0,1,7,64, rather than presuming the bundle
is already a theorem when a freshness gate succeeds. These finite checks
support the ordinary proofs above; they do not establish a binary state
count or blank bootstrap for either refinement.

## 8. Why an unchanged MP/DROP macro cannot replace NIP

For fixed initial `T,D,H`, every fixed sequence of MP and DROP has the same
control and the same final `T,D,H`, independently of the initial stack.
Cache-MP preserves the stack; DROP only pushes its old top. The original MP
version also only pushes a zero on success. AX does not change this
independence: its formula outputs depend on its parameters and old cache,
and it only pushes the old top and generated formulas onto the old stack.

Take the two initial Safe working states `(T,W,D,H)=(0,0,0,0)` and
`(0,3,0,0)`. Here `3=P(2,0)`, and formula2 is `All(0,0)`, derivable by
generalization of the truth code0. One NIP returns cache0 from the first
state and cache2 from the second. Therefore no fixed sequence using only
the unchanged MP, DROP and AX boundary semantics can emulate NIP on all
Safe states. The temporary unpair operations inside MP do not contradict
this: their net boundary effect restores the old stack. Removing the NIP
opcode requires another operation to acquire a new stack-reading effect.
