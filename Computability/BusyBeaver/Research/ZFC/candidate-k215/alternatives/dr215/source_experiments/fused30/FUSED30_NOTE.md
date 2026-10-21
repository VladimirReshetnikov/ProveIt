# FUSED30: a source saving that increases the source DAG

This is a source-only experiment. It supplies no binary Turing-machine table,
no physical state count, and no 214-state candidate. The corrected source has
30 primitive occurrences in direct transfer, versus 35 in the parent, but
208 distinct subtrees in the full program, versus 201 in the parent. The loss
of sharing makes it an unsuccessful state-saving direction in its present form.

## Literal construction

The included `parent.sites.json` is the inherited simple direct-transfer source
from the pinned ST215 packet. Its subtree at path `111` is
`((clearT,copyHtoT),nip)`, with respective leaf counts 2,7,26. Keep `clearT`,
delete `copyHtoT`, and replace two subtrees inside `nip` as follows. Pairs are
binary source-tree nodes; `(opcode,operand)` denotes a primitive leaf.

At relative path `10000`, replace

```
(CD5, ((CD6, CC2), CB1))
```

by

```
(CD5, (CI1, ((CD6, CC3), CB1)))
```

At relative path `10010`, replace

```
(CD5, CC1)
```

by

```
(CD5, (CI1, CC2))
```

The complete replacement body is `(clearT,modifiedNip)`. Its exact tuple
construction is executable in `check_fused30.py`; the complete resulting source
is `fused30.sites.json`. The comparison continue must be **CC3**. Inserting CI1
adds an ancestor, so retaining CC2 incorrectly returns to CI1 and overcounts T.
The exploratory CC2 version was rejected during this audit and is not supplied
as the corrected source. In the corrected full CFG, ordinal 4703 returns to
ordinal 4700; the residual-clear continue at 4708 returns to 4706.

## All-natural source contract

At entry, let registers `(N,T,W,A,D,H,X,Y,L)` equal
`(n,t,w,a,d,h,0,0,l)`, for arbitrary natural n,t,w,a,d,h,l. The corrected body
halts exactly when h=1. Otherwise, if `unpair(w)=(x,v)`, it returns to source
root with

```
(n,h,v,a,d,x,0,0,l).
```

Thus the old top is discarded; the incoming cache becomes top, and the next
Cantor stack head becomes cache. N,A,D,L remain unchanged. The proof below is
for arbitrary natural values, not an inference from the finite corroboration.

First clear T by decrementing it to zero, then initialize X to 1. The modified
comparison couples each successful decrement of H with an increment of T.
At these completed pairs and at the H-loop heads, `T+H=h`. This equality is a
checkpoint invariant: the intervening single increment repairs the temporary
one-unit deficit immediately after a decrement.

- If h=0, the first H decrement takes its zero branch. The following X test
  consumes its single unit and skips the halt. T=H=X=0 on reaching the unpair
  suffix.
- If h=1, the first H decrement and T increment leave H=0,T=1. The X test
  consumes its single unit, and CC3 returns to the H decrement. Both H and X
  are now zero, so the source reaches its unique halt.
- If h>=2, the first comparison iteration consumes X. The second successful
  H decrement increments T again; X is now zero, so the comparison enters
  residual cleanup. Its H decrement/increment loop transfers each remaining
  H unit to T. At exit T=h,H=0,X=0. Y and W were not touched.

The comparison therefore reaches the unchanged unpair suffix exactly in the
nonhalting cases, with T=h,H=0,X=Y=0 and W=w. Its comparison has at most two
successful H tests before residual cleanup; cleanup terminates by decreasing H.

For completeness, the unchanged unpair suffix has a direct arithmetic proof.
It consumes one W unit on each outer iteration while evolving scratch `(X,Y)`
from `(0,0)` by

```
(X,Y) -> (X-1,Y+1)       when X>0,
(0,Y) -> (Y+1,0)         when X=0.
```

The second branch uses a finite Y-to-X transfer loop. With Cantor pairing
`P(X,Y)=(X+Y)(X+Y+1)/2+Y`, either branch increases P by exactly 1. Induction on
the consumed W units gives `P(X,Y)=w` at exit, hence `(X,Y)=unpair(w)`.
The suffix transfers Y into W and X into H, restoring both scratch registers
to zero and leaving T untouched. Each loop has an explicit decreasing natural
counter, so every nonhalting execution terminates. This proves the complete
source contract and scratch closure.

## Reproduction and scope

Run `python3 -B check_fused30.py`. It reconstructs the literal source from the
pinned parent, compares two independent control-flow resolvers, checks closure,
all unchanged earlier source effects, the corrected continue targets, and every
exit of the 30-primitive body. It also corroborates the contract on 14,400 input
tuples, preserving arbitrary sample values in the untouched registers.

The source-language utility and parent source are inherited from ProveIt
commit `b6fb232916d008383e7cf2990d68ddb30fded7db`, path
`Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/direct-transfer/inputs/simple.sites.json` for the parent and `checks/source_language.py` for the utility. This is the intermediate simple association, before the final contextual reassociation used by the physical ST215 table.
The encompassing DR215 packet retains the original notices and licenses.
No allocation search was run on this corrected source. The exact census and
hashes below, and the finite checker receipt, should not be presented as a
physical-runtime certificate.

## Exact data

- `parent.sites.json`: SHA-256 `5f9484c78a67a1ba58d33b632bbb43216b54d36c5ebf976546f9e6a1eaabd744`; metrics `{"dag_nodes": 201, "leaf_occurrences": 4732, "maximum_depth": 44, "maximum_zero_run": 6}`.
- `fused30.sites.json`: SHA-256 `0a1219db2f6986cbe2db8b477341a4e2bb1ceb6925f0256c42ea1af21566ac17`; metrics `{"dag_nodes": 208, "leaf_occurrences": 4727, "maximum_depth": 44, "maximum_zero_run": 6}`.
- Corrected source guarded primitive cases: 6,144.
