# Technical findings for the main report

## A finite-context simulation theorem

Write a machine configuration as `(q,h,tape)`. For a read bit `b`, derive facts of the form

`reachable from start on any initial tape and q=currentState and tape[h]=b => tape[h+j]=v`.

The backwards checker starts from the negation `tape[h]=b, tape[h+j]=1-v`. For each incoming transition `(p,a)->(w,d,q)`, the preceding head is at relative position`-d`. If the requested current value there is different from `w`, that predecessor is impossible. Otherwise shift the remaining constraints by`d` and set the old current cell to`a`. A proof succeeds only when every branch is contradicted before the depth bound; any branch reaching the initial control or the resource bound is unresolved. This is finite exact predecessor analysis, not a simulation of a long blank prefix.

For a pair `p,q` with an equal row on `1-b`, let `phi(q)=p` and let phi fix every other control. Remove q, redirect every target through phi, and replace row`p/b` with a trial row. The symbolic checker runs that trial table from the two original-origin contexts. A successful block must reach the exact phi-image of the original one-step successor, with the same complete tape and head. Unknown exterior bits are branched universally. Each block includes the trial first step, so its duration is positive. The equal row handles the other read symbol.

These local blocks give a positive-step simulation by induction on old runs. Since both machines are deterministic with total transitions at every working state, an infinite old run generates an infinite new run and a halting old run reaches the same halt. Hence the completed local certificate would prove halting equivalence, rather than merely preservation of one finite trace. **No one-state reduction passed this checker in the recorded experiments.** The known CM215 fold passes as a positive control, at unchanged state count.

This exact theorem also explains why a counter or tape invariant established only by a large finite blank prefix would not suffice: the context conditions must hold at every old occurrence of the folded controls.

## Three different ways of removing the saved top

The accepted source's primitive interval `[26,45)` is a19-leaf push of the incoming top. It is a closed source subtree at path`11010010010000`. Its successful mathematical interface is

`(T,W,X,Y)=(t,w,0,0) -> (0,P(t,w),0,0)`.

The next interval`[45,52)` copies D additively into T and restores D. The source edits are therefore exact and small:

1. AX9clear replaces`[26,45)` by the two-leaf clear loop`(CD1,CC1)`.
2. AX9additive deletes`[26,45)`. Its quantifier binder is `D+oldTop`.
3. AX9topbinder deletes`[26,52)`. Its quantifier binder is `oldTop`.

The source constructor verifies all6,150 retained guarded edges for the first two and6,141 for the third. Every outside edge keeps its opcode, operand, and mapped destination; no outside edge enters the interior of a removed block. Both independent complete CFG resolvers agree on each new source. This isolates the changed command semantics from accidental control-flow corruption.

The first two variants have a path to a full strong compiler described by the accompanying theoretical work. The third needs an additional typed variable-renaming calibration. One possible alphabet is the infinite family of theorem codes `f(0)=0`, `f(n+1)=Q_0(f(n))`, but using that alphabet requires checking all original axiom-gate and substitution side conditions under the injective renaming. This extra bridge is **open in this packet**. It would be incorrect to label the216-state allocated table a ZFC-consistency machine merely from the source/DAG counts.

## Measured encoding obstruction

Deleting code does not necessarily delete a shared subtree. The removed push and copy subtrees are used elsewhere, while the changed outer AX path creates new ancestor subtrees. Thus source lengths shrink while the DAG grows:

- AX9clear:4,734 leaves,205 DAG nodes,218-state protected allocation.
- AX9additive:4,732 leaves,204 DAG nodes,217-state protected allocation.
- AX9topbinder:4,725 leaves,203 DAG nodes,216-state protected allocation.

The primary K215 baseline has4,751 leaves,202 DAG nodes and215 physical states. The identity control reproduces its exact native table hash`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.

The unrotated source variants respectively need3,2,1 fresh states in the retained allocation model. Every lower tested fresh-state budget is infeasible in that model, but this is not a minimum-state theorem. The table checks quantify finite decoder paths only. Full symbolic primitive contracts, positive duration, complete blank initialization, and the source-calibration bridge are still required before accepting any new physical table.

Reassociation helps depth but not the source DAG in the completed bounded beams. A useful follow-up is therefore to search joint changes to the emitter and its binary allocation, or to change the shared source library. Repeating shorter-source searches while retaining every old decoder role is too restrictive to establish a physical breakthrough.

## Primary source paths

All paths below are pinned to commit`b07002a86bcc96e76a31b57dce23d3b8c2b76fa6`:

- [K215 README and status](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/README.md).
- [Exact accepted source](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json).
- [Original protected allocator](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/research/composition-allocation/allocate.py).
- [Independent local108 correction](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/research/composition-allocation/check_allocated.py).
- [Existing fixed52/176 helper-reuse search](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/conditional-marker/research/helper-reuse/final_helper_reuse_search.py). Our202-pair search broadens this fixed-pair question; it does not claim the helper-reuse idea itself is new.
- [Inherited source-rotation machinery](https://github.com/VladimirReshetnikov/ProveIt/blob/b07002a86bcc96e76a31b57dce23d3b8c2b76fa6/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/conditional-marker/research/source-packing/rotate_closed.py).
