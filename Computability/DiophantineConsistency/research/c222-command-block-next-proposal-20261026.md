# Next actual C222 command-block checkpoint

26 October 2026. Read-only proposal; no new Lean implementation or compiler
invocation. The accepted append-composition leaf is enough to prove useful
actual blocks without importing any historical C254 execution semantics.

The smallest proposed pair is `ArithmeticCommandBlockPerm222` and Checks,
about 210–260 main lines and 50–65 focused checks. Import only
`DiophantineConsistency.ArithmeticCommandCompositionPerm222`. Work uniformly
in an arbitrary `ORingStructure V` satisfying IΣ1. This first checkpoint
proves literal command-cons execution, fixed finite stack popping, discard,
counter loading and exact dominated AX setup. It does not yet construct an
arbitrary proof compiler or claim a rule contract for every C222 row.

## Literal words and first endpoints

Use `P` below for the existing internal Cantor function. All `rest` operands
are already shifted command words, not raw candidates. Define:

```
nipWord rest      = P 0 rest + 1
dropWord rest     = P 1 rest + 1
mpWord x rest     = P 2 (P x rest) + 1
axWord c x y rest = P (c+3) (P y (P x rest)) + 1
```

The exposed AX argument order is `(c,x,y)`; its physical fields are **y then
x**. NIP and DROP have no argument field. Obtain four exact `eval_*` equations
from `eval_succ`, the existing `stepValue_*` equations and `tail_*` identities:
NIP halts exactly when the old cache is 1; DROP preserves d; MP adds x to d;
AX continues at
`stateValue (gateValue (d+x) (h+y) c)
 (axStackValue (d+x) h (h+y) c d t S) 0 0`.
The old d supplies the fourth axiom parameter **and** GEN label. No fresh
label, validity, nonzero-payload or semantic CProv premise is required.

For external fixed `Nat` counts, define `nipsWord 0=0` and
`nipsWord (k+1)=nipWord (nipsWord k)`. Define finite `pushL` using Cantor
cons, and prove the actual popping endpoint

```
evalValue (nipsWord (xs.length+1))
 (stateValue t (pushL (xs ++ [last]) S) d h)
 = someState t S d last
```

assuming only `h≠1` and every entry in xs differs from 1. The last entry is
allowed to equal 1: it is loaded after the final command, not subsequently
tested. External finite lists organize a fixed block, never reinterpret an
arbitrary internal-model stack as an externally finite list. A continuation
version follows from actual `eval_append_success`.

Define the exact nine-item list

```
axList a h b c u = [rho1 a b, rho2 a b c, rho3 a b c,
 rho4 a b c, rho5 a b c, rho6 a c, growG a b c,
 rho8 a b c u, wal u h]
```

and show `axStackValue ... = pushL (axList ... ++ [t]) S`. Each displayed
formula is implication- or universal-tagged and differs from false code1.
`gateValue` also differs from1: a collision produces truth0, while the
noncollision branch is the actual implication-headed helper-free bundle.
No bundle truth or C222 proof-calibration theorem is needed for popping.

## Discard and counter setup, including zero

Set `discardWord = mpWord 1 (axWord 1 0 0 (nipsWord 10))` and prove
`evalValue discardWord (stateValue t S 0 0) = someState 0 S 0 0`.
The first MP fails because `wim t 1` is nonzero, setting d=1. Therefore this
actual discard AX pushes `rho8 1 0 1 1` and `wal 1 0`, not the historical
C254 discard's fourth parameter 0. Ten NIPs restore the original saved
stack and the explicit zero last entry.

Define the actual counter loader
`Jword u = if u=0 then 0 else mpWord u 0`, with its finite fixed graph using
the existing arithmetic constructors. Prove, including u=0,

```
evalValue (appendValue (Jword u) rest) (stateValue 0 S 0 0)
 = evalValue rest (stateValue 0 S u 0).
```

At u≠0, `wim 0 u≠0` follows from the existing component lower bound, so MP
fails and sets exactly u without pushing a zero. At u=0, **do not execute
MP0**: `wim 0 0=0` would make MP succeed and change the stack. The empty
branch is essential.

The substantive first-leaf endpoint is, for arbitrary internal a,b,c,u,t,S
and arbitrary continuation rest, under the sole setup guard `u≤a`:

```
evalValue (appendValue discardWord
  (appendValue (Jword u) (axWord c (a-u) b rest)))
 (stateValue t S 0 0)
 = evalValue rest
    (stateValue (gateValue a b c) (axStackValue a 0 b c u 0 S) 0 0).
```

This derives the physical oldest-counter behavior, rather than supplying
the desired stack as a premise. Numeric collisions c=a or c=b remain legal
runtime cases and give truth0; a=b and c=0 are not separately prohibited.
Later extraction of the seed specifically requires only c≠a,b.

## Subsequent dependency order and remaining obstruction

After freezing that first pair, a separate selection/rule pair can define
`Contract word target := ∀t S, evalValue word (stateValue t S 0 0)=0 ∨
 evalValue word (stateValue t S 0 0)=someState target S 0 0` and prove fixed
entry extraction, leaves, GEN and MP. Preserve the actual GEN suffix
`DROP; J(i); NIP; AX(i,0,0); NIP^9; DROP; NIP; NIP`.
Omitting J and merely changing AX's x payload would generate `wal 0 H`,
not the required `wal i H`. The actual MP cleanup AX likewise uses old d=B.
GEN allows child conclusion1; MP's exact suffix halts when A=1 or B=1.
The major child contract must hold at top0 and saved stack `P A S`.

AX leaf6 supplies `rho6 a c`, so the source r6(a,b) leaf chooses AX parameters
`(a,0,b,0)`. Leaf7 is growG, never old rho7. Leaf8 directly supplies rho8 only
when `u≤a`. This is a genuine compiler obligation: the actual checker accepts
rho8 for arbitrary u. The Nat `EnumPerm.build_c222` resolves it with the
representation-independent finite `DominatedImplication.rho8_all` theorem.
That generic source is already in the cache and can later be interpreted
over internal implication/≤ and block contracts. However, an existential
word obtained by that theorem alone is **not yet a represented uniform word
function**. A later fixed circuit/witness extraction from its finite MP/
restricted-rho8 derivation must give the exact represented row10 output.
Do not transplant the old254 direct row10 leaf or silently assume u≤a.

Only after these finite blocks and uniform row10 are bound should a new
actual twelve-tag word row and history be built. Reuse `ArithmeticSequenceHistory`
for the new represented step, with its positive-index convention; do not
copy the old fixed-history algorithm. Actual `ArithmeticHistory222.value_succ`
and `ArithmeticProofConstructors222` already provide all child bounds and
checker equations. A later validity-conditional correctness proof can use
the Pi1 all-top/all-stack contract because eval and word are Delta1, with
bounded-prefix IΣ1 induction. No such proof, scheduler reach, machine
calibration or HA derivation is claimed here.

## Source/cache boundary

The accompanying cache plan pins the exact sources, objects, imports,
compiler, 38 external boundaries and read-only guides. The first leaf needs
122 cached custom modules, including95 Foundation modules, and407 artifacts:
the reviewed121/406 composition prerequisites plus the independently fresh,
author-byte-identical composition primary. No Foundation addition or
dependency refresh is needed. The current primary is
`/tmp/command-compositionperm222-controller-peer-d_j3izsj/lib/DiophantineConsistency/ArithmeticCommandCompositionPerm222.olean`,
SHA `6e629ca4e067de5179cdfaa201cdbbbda9fd1cb0e8b6e5efb60e39d6779dbfe2`.

A read-only future union with actual ProofConstructors222 adds eight custom
modules and no Foundation modules: History222, ProofConstructors222, Row222,
Row254, SequenceHistory, Code222Proof, Code254History and Code254Proof. Their
accepted source/object providers are pinned separately, not imported into
the proposed first leaf. Historical Block/Leaf/Rule/ProofWord254 sources
were read as guides only; their execution and validator semantics are not
proposed imports. Every first-leaf source/import/artifact/boundary pin was
reauthenticated while preparing the plan. Future execution, if authorized,
will use private outputs, Lean4.32 `-M6000 -j1 -DElab.async=false`, and the
512 MiB disk reserve before each invocation. No build was performed for
this proposal.
