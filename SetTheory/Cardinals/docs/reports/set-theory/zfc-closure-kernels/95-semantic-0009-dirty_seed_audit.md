# Independent dirty-root audit

## Finding and scope

The source-level safe-start theorem **does cover** the logical seed

`[N,T,W,A,D,H,X,Y,L] = [3,0,0,0,3,0,35,0,0]`.

It is the literal specialization
`DirtyProgram254.six_nonformula_path_iff 3 0 3 35 0 0`.
The scratch value `X = 35` introduces no additional proof obligation in
that theorem. The six numerical fields `N,A,D,X,Y,L` are universally
quantified. Only `T=W=H=0` is imposed for this simple safe-start family.

This finding does **not** establish the proposed 244-state machine. The
binary edit deleting shared grammar node `gm` affects four expanded source
occurrences; only one was initially known dead from the product invariant.
Source equivalence for all affected occurrences and binary simulation are
separate obligations. A valid initial source seed alone cannot repair an
incorrect subsequent program.

## Exact source theorem chain

Files were independently read using `git show` at the current supplied
ProveIt pin `6d69a46dce1de15397a9d2448dcc946d08c90327`. The following selected
copies are also packaged in the inherited route245 reference snapshot:

- `DirtyProgram254.lean`, SHA256
  `17ad4165bb08cd54e5824a8b59ab3564df43ff189ee9972a547a50edbc2719e4`.
- `DirtyRoot254.lean`, SHA256
  `d6d9a500a5428e375ba987116e8fd103e9a0f41e92dffb70d5377dc93e374b30`.
- `EnumSafeStart254.lean`, SHA256
  `22cab829c0f37919dd9bb7f28efdc658eeaeee687c84a817f0b082c9d5080dfe`.

For the original exact 219-node path program, compose:

1. `DirtyProgram254.six_nonformula_path_iff 3 0 3 35 0 0`:
   source halting from the displayed root seed iff a refutation of the
   sealed native CP/all-Form-GIC/IR theory exists.
2. `WFTheory.native_refutation_iff_zf`:
   native refutation iff a refutation of ordinary ZF, including Power and
   Foundation, exists.
3. `ChoiceCalibration254.zf_refutation_iff_zfc`:
   ZF refutation iff ZFC refutation.

Negating the composed equivalence gives source nonhalting iff Con(ZFC).
The two theory transfers use the quotient well-founded-part model and the
constructible inner model, together with first-order completeness. These
are ordinary metamathematical constructions formalizable in ZFC. The
inspected Lean declarations are external proof-system metatheorems; they
are not an already compiled internal-ZFC proof code for a new binary
table, and no such additional claim is made here.

`DirtySeed35.lean` displays the complete specialization in two small
declarations. It has not been compiled in this research checkout.

## Why the dirty scratch is harmless at the source root

The nine fields of `L2.AS` are declared in the order above. `L2.enc` maps
them to logical register indices 0 through 8, with all indices at least 9
equal to zero. Let `P(x,y)` be the source Cantor pairing, and `unP` its
inverse. For an arbitrary initial state, define:

- If `L=0`, set `N'=N+X+1`, `X'=0`, and `n=N`.
- If `L>0`, set `N'=N`, `X'=X`, and `n=L-1`.
- Let `(u,v)=unP(P(X',Y)+n)`.

The initial fetch routine and first selector read end at the common state

`[N',T,W,A+u,D,H,0,0,v]`.

The same two routines reach that state from the *clean virtual root*

`[N',T,W,0,D,H,0,0,P(A+u,v)+1]`.

Consequently `DirtyRoot254.root_equiv` preserves every structured root
outcome and its entire resulting register file for all nine initial
values. Its `iter_equiv` then preserves repeated-root halting. This is
stronger than a finite trace check and does not assume initial formula
safety.

For the displayed seed, `L=0` gives `N'=3+35+1=39`, `n=3`, and
`unP(3)=(2,0)`. The virtual root is therefore

`[39,0,0,0,3,0,0,0,4]`.

Both prefixes reach `[39,0,0,2,3,0,0,0,0]`. The values of top formula,
stack and retained formula are preserved by absorption. Their zero codes
satisfy the existing invariant by `C254.truth`, `C254.truth`, and
`Enum254.good_zero`.

The safe-start completeness argument tolerates the larger initial proof
cutoff 39. It drains any current candidate, then visits cofinally many
proof codes. The original AX instruction retains its fourth, semantically
irrelevant padding field, so any finite refutation can be padded beyond
the starting cutoff. `EnumSafeStart254.complete_from` needs no formula
invariant; the invariant is needed only for the soundness direction.

## Product-invariant compatibility

The route245 architecture checker initializes its abstract product masks
in register order `N,T,W,A,D,H,X,Y,L` to

`[7,1,1,7,7,1,7,7,7]`.

Mask bits correspond to 0, 1, and at least 2. Thus 7 allows every natural
number and 1 requires zero. This abstract entry condition agrees exactly
with the six-field dirty safe-start family and includes `X=35`. Its
independent edge checker states its scope as:

`Every N,A,D,X,Y,L; T=W=H=0 at root.`

An invariant fact at one expanded leaf cannot be transferred to a shared
grammar node without checking every expanded occurrence of that node.

## Primary source links

- https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyRoot254.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumSafeStart254.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean
- https://github.com/VladimirReshetnikov/ProveIt/blob/6d69a46dce1de15397a9d2448dcc946d08c90327/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean
- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/prog/Dag254.v

The dirty absorption theorem is prior art: intake 153/source 35, original
arrival `4e720ccbbfaa836b95be3b2f3f268a737b48c6d1`, preserved placement
`6135ffef4b`. This audit supplies an application and scope check, not a
novel dirty-start theorem.
